package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/csv"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"math"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

const version = "1.0.0"

type Zone struct {
	Name     string `json:"name"`
	Size     uint64 `json:"size"`
	Limit    uint64 `json:"limit"`
	Used     uint64 `json:"used"`
	Free     uint64 `json:"free"`
	Requests uint64 `json:"requests"`
	Failures uint64 `json:"failures"`
	Sleeps   uint64 `json:"sleeps"`
	Raw      string `json:"raw,omitempty"`
}
type MallocType struct {
	Name     string `json:"name"`
	InUse    uint64 `json:"in_use"`
	Memory   uint64 `json:"memory"`
	HighUse  uint64 `json:"high_use"`
	Requests uint64 `json:"requests"`
	Size     string `json:"size,omitempty"`
	Raw      string `json:"raw,omitempty"`
}
type CommandRecord struct {
	Command    string   `json:"command"`
	Arguments  []string `json:"arguments"`
	Output     string   `json:"output,omitempty"`
	Error      string   `json:"error,omitempty"`
	DurationMS int64    `json:"duration_ms"`
}
type Snapshot struct {
	Schema      int               `json:"schema"`
	Timestamp   time.Time         `json:"timestamp"`
	Host        string            `json:"host"`
	Platform    string            `json:"platform"`
	Version     string            `json:"version"`
	Kernel      string            `json:"kernel"`
	Zones       []Zone            `json:"zones"`
	Malloc      []MallocType      `json:"malloc"`
	Sysctl      map[string]string `json:"sysctl"`
	Commands    []CommandRecord   `json:"commands,omitempty"`
	Notes       []string          `json:"notes,omitempty"`
	Fingerprint string            `json:"fingerprint"`
}
type ZoneDelta struct {
	Name         string `json:"name"`
	Before       *Zone  `json:"before,omitempty"`
	After        *Zone  `json:"after,omitempty"`
	UsedDelta    int64  `json:"used_delta"`
	FreeDelta    int64  `json:"free_delta"`
	RequestDelta int64  `json:"request_delta"`
	FailureDelta int64  `json:"failure_delta"`
	GrowthBytes  int64  `json:"growth_bytes"`
}
type Comparison struct {
	Start            time.Time   `json:"start"`
	End              time.Time   `json:"end"`
	DurationSeconds  float64     `json:"duration_seconds"`
	Zones            []ZoneDelta `json:"zones"`
	Added            []string    `json:"added"`
	Removed          []string    `json:"removed"`
	TotalGrowthBytes int64       `json:"total_growth_bytes"`
}
type Finding struct {
	Severity string  `json:"severity"`
	Category string  `json:"category"`
	Subject  string  `json:"subject"`
	Message  string  `json:"message"`
	Value    float64 `json:"value,omitempty"`
}
type Report struct {
	Timestamp          time.Time `json:"timestamp"`
	Host               string    `json:"host"`
	ZoneCount          int       `json:"zone_count"`
	MallocCount        int       `json:"malloc_count"`
	UsedObjects        uint64    `json:"used_objects"`
	FreeObjects        uint64    `json:"free_objects"`
	EstimatedUsedBytes uint64    `json:"estimated_used_bytes"`
	EstimatedFreeBytes uint64    `json:"estimated_free_bytes"`
	Requests           uint64    `json:"requests"`
	Failures           uint64    `json:"failures"`
	Findings           []Finding `json:"findings"`
	TopZones           []Zone    `json:"top_zones"`
}
type Config struct {
	Timeout    time.Duration
	SysctlKeys []string
	IncludeRaw bool
	Strict     bool
}
type Runner struct{ Timeout time.Duration }

func (r Runner) Run(name string, args ...string) CommandRecord {
	start := time.Now()
	ctx, cancel := context.WithTimeout(context.Background(), r.Timeout)
	defer cancel()
	cmd := exec.CommandContext(ctx, name, args...)
	data, err := cmd.CombinedOutput()
	rec := CommandRecord{Command: name, Arguments: args, Output: string(data), DurationMS: time.Since(start).Milliseconds()}
	if err != nil {
		rec.Error = err.Error()
	}
	if errors.Is(ctx.Err(), context.DeadlineExceeded) {
		rec.Error = "command timeout"
	}
	return rec
}
func defaults() Config {
	return Config{Timeout: 8 * time.Second, SysctlKeys: []string{
		"kern.osrelease", "kern.version", "kern.hostname", "vm.stats.vm.v_page_size", "vm.stats.vm.v_free_count", "vm.stats.vm.v_active_count", "vm.stats.vm.v_inactive_count", "vm.stats.vm.v_wire_count", "vm.stats.vm.v_cache_count", "vm.stats.vm.v_laundry_count", "vm.stats.vm.v_page_count", "vm.stats.vm.v_swappgsin", "vm.stats.vm.v_swappgsout", "vm.swap_total", "vm.swap_reserved", "vm.kmem_size", "vm.kmem_size_max", "vm.kmem_map_size", "vm.kmem_map_free", "vm.zone", "vm.uma", "hw.physmem", "hw.realmem", "hw.ncpu", "kern.smp.cpus"}}
}
func parseUnsigned(s string) uint64 {
	s = strings.TrimSpace(strings.ReplaceAll(s, ",", ""))
	s = strings.TrimSuffix(s, "K")
	if strings.HasSuffix(s, "k") {
		s = strings.TrimSuffix(s, "k")
	}
	if strings.HasPrefix(s, "0x") {
		n, _ := strconv.ParseUint(s[2:], 16, 64)
		return n
	}
	n, _ := strconv.ParseUint(s, 10, 64)
	return n
}
func parseSigned(s string) int64 { n, _ := strconv.ParseInt(strings.TrimSpace(s), 10, 64); return n }
func parseZoneLine(line string) (Zone, bool) {
	line = strings.TrimSpace(line)
	if line == "" || strings.HasPrefix(line, "ITEM") || strings.HasPrefix(line, "ZONE") || strings.HasPrefix(line, "--") {
		return Zone{}, false
	}
	idx := strings.Index(line, ":")
	if idx < 1 {
		return Zone{}, false
	}
	name := strings.TrimSpace(line[:idx])
	fields := strings.Fields(line[idx+1:])
	if len(fields) < 7 {
		return Zone{}, false
	}
	z := Zone{Name: name, Size: parseUnsigned(fields[0]), Limit: parseUnsigned(fields[1]), Used: parseUnsigned(fields[2]), Free: parseUnsigned(fields[3]), Requests: parseUnsigned(fields[4]), Failures: parseUnsigned(fields[5]), Sleeps: parseUnsigned(fields[6]), Raw: line}
	if z.Size == 0 && z.Used == 0 && z.Free == 0 && z.Requests == 0 {
		return Zone{}, false
	}
	return z, true
}
func ParseZones(data string) []Zone {
	zones := []Zone{}
	seen := map[string]bool{}
	for _, line := range strings.Split(data, "\n") {
		if z, ok := parseZoneLine(line); ok {
			if !seen[z.Name] {
				zones = append(zones, z)
				seen[z.Name] = true
			}
		}
	}
	sort.Slice(zones, func(i, j int) bool { return zones[i].Name < zones[j].Name })
	return zones
}
func parseMallocLine(line string) (MallocType, bool) {
	idx := strings.Index(line, ":")
	if idx < 1 {
		return MallocType{}, false
	}
	name := strings.TrimSpace(line[:idx])
	if name == "" || strings.HasPrefix(name, "Type") {
		return MallocType{}, false
	}
	fields := strings.Fields(line[idx+1:])
	if len(fields) < 4 {
		return MallocType{}, false
	}
	if _, err := strconv.ParseUint(fields[0], 10, 64); err != nil {
		return MallocType{}, false
	}
	m := MallocType{Name: name, InUse: parseUnsigned(fields[0]), Memory: parseUnsigned(fields[1]), HighUse: parseUnsigned(fields[2]), Requests: parseUnsigned(fields[3]), Raw: line}
	if len(fields) > 4 {
		m.Size = strings.Join(fields[4:], " ")
	}
	return m, true
}
func ParseMalloc(data string) []MallocType {
	result := []MallocType{}
	seen := map[string]bool{}
	for _, line := range strings.Split(data, "\n") {
		if m, ok := parseMallocLine(line); ok && !seen[m.Name] {
			result = append(result, m)
			seen[m.Name] = true
		}
	}
	sort.Slice(result, func(i, j int) bool { return result[i].Name < result[j].Name })
	return result
}
func ParseSysctl(data string) map[string]string {
	out := map[string]string{}
	for _, line := range strings.Split(data, "\n") {
		i := strings.Index(line, ":")
		if i < 1 {
			continue
		}
		key := strings.TrimSpace(line[:i])
		val := strings.TrimSpace(line[i+1:])
		if key != "" {
			out[key] = val
		}
	}
	return out
}
func fingerprint(s Snapshot) string {
	s.Fingerprint = ""
	s.Timestamp = time.Time{}
	s.Commands = nil
	s.Notes = nil
	data, _ := json.Marshal(s)
	sum := sha256.Sum256(data)
	return hex.EncodeToString(sum[:])
}
func Collect(cfg Config) (Snapshot, error) {
	host, _ := os.Hostname()
	s := Snapshot{Schema: 1, Timestamp: time.Now().UTC(), Host: host, Platform: runtime.GOOS + "/" + runtime.GOARCH, Version: version, Sysctl: map[string]string{}, Zones: []Zone{}, Malloc: []MallocType{}}
	r := Runner{Timeout: cfg.Timeout}
	if runtime.GOOS != "freebsd" {
		s.Notes = append(s.Notes, "collection targets FreeBSD; current platform is "+runtime.GOOS)
	}
	jobs := []struct {
		name string
		args []string
	}{{"vmstat", []string{"-z"}}, {"vmstat", []string{"-m"}}, {"uname", []string{"-r"}}}
	type result struct {
		index int
		rec   CommandRecord
	}
	ch := make(chan result, len(jobs))
	var wg sync.WaitGroup
	for i, j := range jobs {
		wg.Add(1)
		go func(i int, j struct {
			name string
			args []string
		}) { defer wg.Done(); ch <- result{i, r.Run(j.name, j.args...)} }(i, j)
	}
	wg.Wait()
	close(ch)
	records := make([]CommandRecord, len(jobs))
	for item := range ch {
		records[item.index] = item.rec
	}
	for i, rec := range records {
		s.Commands = append(s.Commands, rec)
		if rec.Error != "" {
			s.Notes = append(s.Notes, rec.Command+" failed: "+rec.Error)
			continue
		}
		switch i {
		case 0:
			s.Zones = ParseZones(rec.Output)
		case 1:
			s.Malloc = ParseMalloc(rec.Output)
		case 2:
			s.Kernel = strings.TrimSpace(rec.Output)
		}
	}
	for _, key := range cfg.SysctlKeys {
		rec := r.Run("sysctl", "-n", key)
		if rec.Error == "" {
			s.Sysctl[key] = strings.TrimSpace(rec.Output)
		} else if cfg.IncludeRaw {
			s.Notes = append(s.Notes, "sysctl "+key+": "+rec.Error)
		}
	}
	if !cfg.IncludeRaw {
		for i := range s.Zones {
			s.Zones[i].Raw = ""
		}
		for i := range s.Malloc {
			s.Malloc[i].Raw = ""
		}
		for i := range s.Commands {
			s.Commands[i].Output = ""
		}
	}
	s.Fingerprint = fingerprint(s)
	if cfg.Strict && len(s.Zones) == 0 {
		return s, errors.New("no UMA zones parsed from vmstat -z")
	}
	return s, nil
}
func WriteJSON(path string, v any) error {
	data, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return err
	}
	data = append(data, '\n')
	if path == "" || path == "-" {
		_, err = os.Stdout.Write(data)
		return err
	}
	return atomicWrite(path, data)
}
func atomicWrite(path string, data []byte) error {
	dir := filepath.Dir(path)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return err
	}
	f, err := os.CreateTemp(dir, ".uma-*")
	if err != nil {
		return err
	}
	tmp := f.Name()
	defer os.Remove(tmp)
	if _, err = f.Write(data); err != nil {
		f.Close()
		return err
	}
	if err = f.Sync(); err != nil {
		f.Close()
		return err
	}
	if err = f.Close(); err != nil {
		return err
	}
	return os.Rename(tmp, path)
}
func ReadSnapshot(path string) (Snapshot, error) {
	var s Snapshot
	f, err := os.Open(path)
	if err != nil {
		return s, err
	}
	defer f.Close()
	err = json.NewDecoder(io.LimitReader(f, 64<<20)).Decode(&s)
	if err != nil {
		return s, err
	}
	if s.Schema != 1 {
		return s, fmt.Errorf("unsupported schema %d", s.Schema)
	}
	return s, nil
}
func WriteJSONL(path string, v any) error {
	data, err := json.Marshal(v)
	if err != nil {
		return err
	}
	data = append(data, '\n')
	if path == "" || path == "-" {
		_, err = os.Stdout.Write(data)
		return err
	}
	f, err := os.OpenFile(path, os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0644)
	if err != nil {
		return err
	}
	defer f.Close()
	_, err = f.Write(data)
	return err
}
func ReadJSONL(path string) ([]Snapshot, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 65536), 32<<20)
	out := []Snapshot{}
	line := 0
	for sc.Scan() {
		line++
		b := bytes.TrimSpace(sc.Bytes())
		if len(b) == 0 {
			continue
		}
		var s Snapshot
		if err := json.Unmarshal(b, &s); err != nil {
			return nil, fmt.Errorf("line %d: %w", line, err)
		}
		out = append(out, s)
	}
	return out, sc.Err()
}
func intDelta(a, b uint64) int64 {
	if b >= a {
		d := b - a
		if d > math.MaxInt64 {
			return math.MaxInt64
		}
		return int64(d)
	}
	d := a - b
	if d > math.MaxInt64 {
		return math.MinInt64
	}
	return -int64(d)
}
func saturatingMultiply(a, b uint64) uint64 {
	if a != 0 && b > math.MaxUint64/a {
		return math.MaxUint64
	}
	return a * b
}
func Compare(a, b Snapshot) Comparison {
	c := Comparison{Start: a.Timestamp, End: b.Timestamp, DurationSeconds: b.Timestamp.Sub(a.Timestamp).Seconds(), Zones: []ZoneDelta{}, Added: []string{}, Removed: []string{}}
	old := map[string]Zone{}
	next := map[string]Zone{}
	for _, z := range a.Zones {
		old[z.Name] = z
	}
	for _, z := range b.Zones {
		next[z.Name] = z
	}
	names := map[string]bool{}
	for n := range old {
		names[n] = true
	}
	for n := range next {
		names[n] = true
	}
	keys := make([]string, 0, len(names))
	for n := range names {
		keys = append(keys, n)
	}
	sort.Strings(keys)
	for _, name := range keys {
		before, okA := old[name]
		after, okB := next[name]
		d := ZoneDelta{Name: name}
		if okA {
			copy := before
			d.Before = &copy
		}
		if okB {
			copy := after
			d.After = &copy
		}
		if !okA {
			c.Added = append(c.Added, name)
		}
		if !okB {
			c.Removed = append(c.Removed, name)
		}
		d.UsedDelta = intDelta(before.Used, after.Used)
		d.FreeDelta = intDelta(before.Free, after.Free)
		d.RequestDelta = intDelta(before.Requests, after.Requests)
		d.FailureDelta = intDelta(before.Failures, after.Failures)
		d.GrowthBytes = intDelta(saturatingMultiply(before.Used, before.Size), saturatingMultiply(after.Used, after.Size))
		c.TotalGrowthBytes += d.GrowthBytes
		c.Zones = append(c.Zones, d)
	}
	sort.Slice(c.Zones, func(i, j int) bool { return c.Zones[i].GrowthBytes > c.Zones[j].GrowthBytes })
	return c
}
func Analyze(s Snapshot, top int) Report {
	r := Report{Timestamp: s.Timestamp, Host: s.Host, ZoneCount: len(s.Zones), MallocCount: len(s.Malloc), Findings: []Finding{}, TopZones: append([]Zone{}, s.Zones...)}
	for _, z := range s.Zones {
		r.UsedObjects += z.Used
		r.FreeObjects += z.Free
		r.Requests += z.Requests
		r.Failures += z.Failures
		r.EstimatedUsedBytes += saturatingMultiply(z.Size, z.Used)
		r.EstimatedFreeBytes += saturatingMultiply(z.Size, z.Free)
		if z.Failures > 0 {
			r.Findings = append(r.Findings, Finding{"warning", "allocation_failures", z.Name, fmt.Sprintf("%d allocation failures", z.Failures), float64(z.Failures)})
		}
		if z.Limit > 0 && z.Used >= z.Limit {
			r.Findings = append(r.Findings, Finding{"critical", "zone_limit", z.Name, "zone at or above configured limit", float64(z.Used)})
		} else if z.Limit > 0 && float64(z.Used)/float64(z.Limit) > .9 {
			r.Findings = append(r.Findings, Finding{"warning", "zone_pressure", z.Name, "zone usage above 90 percent of limit", float64(z.Used) / float64(z.Limit)})
		}
		if z.Sleeps > 0 {
			r.Findings = append(r.Findings, Finding{"info", "allocation_sleeps", z.Name, fmt.Sprintf("%d allocation sleeps", z.Sleeps), float64(z.Sleeps)})
		}
	}
	sort.Slice(r.TopZones, func(i, j int) bool {
		return saturatingMultiply(r.TopZones[i].Size, r.TopZones[i].Used) > saturatingMultiply(r.TopZones[j].Size, r.TopZones[j].Used)
	})
	if top >= 0 && len(r.TopZones) > top {
		r.TopZones = r.TopZones[:top]
	}
	sort.Slice(r.Findings, func(i, j int) bool {
		if r.Findings[i].Severity != r.Findings[j].Severity {
			return severityRank(r.Findings[i].Severity) > severityRank(r.Findings[j].Severity)
		}
		return r.Findings[i].Subject < r.Findings[j].Subject
	})
	return r
}
func severityRank(s string) int {
	switch s {
	case "critical":
		return 3
	case "warning":
		return 2
	default:
		return 1
	}
}
func humanBytes(n uint64) string {
	v := float64(n)
	units := []string{"B", "KiB", "MiB", "GiB", "TiB", "PiB"}
	i := 0
	for v >= 1024 && i < len(units)-1 {
		v /= 1024
		i++
	}
	return fmt.Sprintf("%.2f %s", v, units[i])
}
func textReport(r Report) {
	fmt.Printf("UMA Forensics Go %s\nHost: %s\nTimestamp: %s\nZones: %d\nMalloc types: %d\nUsed objects: %d\nFree objects: %d\nEstimated used: %s\nEstimated free: %s\nRequests: %d\nFailures: %d\nFindings: %d\n", version, r.Host, r.Timestamp.Format(time.RFC3339), r.ZoneCount, r.MallocCount, r.UsedObjects, r.FreeObjects, humanBytes(r.EstimatedUsedBytes), humanBytes(r.EstimatedFreeBytes), r.Requests, r.Failures, len(r.Findings))
	fmt.Println("\nLargest zones by estimated active bytes:")
	for _, z := range r.TopZones {
		fmt.Printf("%-36s size=%-8d used=%-10d bytes=%s\n", z.Name, z.Size, z.Used, humanBytes(saturatingMultiply(z.Size, z.Used)))
	}
	for _, f := range r.Findings {
		fmt.Printf("[%s] %s: %s\n", strings.ToUpper(f.Severity), f.Subject, f.Message)
	}
}
func textComparison(c Comparison, top int) {
	fmt.Printf("Comparison: %s -> %s (%.1f seconds)\nTotal estimated growth: %d bytes\nAdded: %d Removed: %d\n", c.Start.Format(time.RFC3339), c.End.Format(time.RFC3339), c.DurationSeconds, c.TotalGrowthBytes, len(c.Added), len(c.Removed))
	for i, d := range c.Zones {
		if top >= 0 && i >= top {
			break
		}
		fmt.Printf("%-36s used=%+d free=%+d requests=%+d failures=%+d growth=%+d B\n", d.Name, d.UsedDelta, d.FreeDelta, d.RequestDelta, d.FailureDelta, d.GrowthBytes)
	}
}
func writeZonesCSV(path string, zones []Zone) error {
	var buf bytes.Buffer
	w := csv.NewWriter(&buf)
	w.Write([]string{"name", "size", "limit", "used", "free", "requests", "failures", "sleeps", "estimated_used_bytes"})
	for _, z := range zones {
		w.Write([]string{z.Name, strconv.FormatUint(z.Size, 10), strconv.FormatUint(z.Limit, 10), strconv.FormatUint(z.Used, 10), strconv.FormatUint(z.Free, 10), strconv.FormatUint(z.Requests, 10), strconv.FormatUint(z.Failures, 10), strconv.FormatUint(z.Sleeps, 10), strconv.FormatUint(saturatingMultiply(z.Size, z.Used), 10)})
	}
	w.Flush()
	if err := w.Error(); err != nil {
		return err
	}
	if path == "-" {
		_, err := os.Stdout.Write(buf.Bytes())
		return err
	}
	return atomicWrite(path, buf.Bytes())
}
func writeMallocCSV(path string, types []MallocType) error {
	var buf bytes.Buffer
	w := csv.NewWriter(&buf)
	w.Write([]string{"name", "in_use", "memory", "high_use", "requests", "size"})
	for _, m := range types {
		w.Write([]string{m.Name, strconv.FormatUint(m.InUse, 10), strconv.FormatUint(m.Memory, 10), strconv.FormatUint(m.HighUse, 10), strconv.FormatUint(m.Requests, 10), m.Size})
	}
	w.Flush()
	if err := w.Error(); err != nil {
		return err
	}
	if path == "-" {
		_, err := os.Stdout.Write(buf.Bytes())
		return err
	}
	return atomicWrite(path, buf.Bytes())
}
func stats(values []float64) map[string]float64 {
	out := map[string]float64{"count": float64(len(values))}
	if len(values) == 0 {
		return out
	}
	sorted := append([]float64{}, values...)
	sort.Float64s(sorted)
	sum := 0.0
	for _, v := range values {
		sum += v
	}
	mean := sum / float64(len(values))
	variance := 0.0
	for _, v := range values {
		variance += (v - mean) * (v - mean)
	}
	variance /= float64(len(values))
	out["min"] = sorted[0]
	out["max"] = sorted[len(sorted)-1]
	out["mean"] = mean
	out["stddev"] = math.Sqrt(variance)
	out["median"] = percentile(sorted, .5)
	out["p90"] = percentile(sorted, .9)
	out["p95"] = percentile(sorted, .95)
	out["p99"] = percentile(sorted, .99)
	return out
}
func percentile(sorted []float64, p float64) float64 {
	if len(sorted) == 0 {
		return 0
	}
	if p <= 0 {
		return sorted[0]
	}
	if p >= 1 {
		return sorted[len(sorted)-1]
	}
	x := p * float64(len(sorted)-1)
	i := int(x)
	f := x - float64(i)
	if i+1 >= len(sorted) {
		return sorted[i]
	}
	return sorted[i]*(1-f) + sorted[i+1]*f
}
func seriesReport(snaps []Snapshot) map[string]any {
	out := map[string]any{"samples": len(snaps)}
	if len(snaps) == 0 {
		return out
	}
	out["start"] = snaps[0].Timestamp
	out["end"] = snaps[len(snaps)-1].Timestamp
	values := []float64{}
	zones := map[string][]float64{}
	for _, s := range snaps {
		r := Analyze(s, 0)
		values = append(values, float64(r.EstimatedUsedBytes))
		for _, z := range s.Zones {
			zones[z.Name] = append(zones[z.Name], float64(saturatingMultiply(z.Used, z.Size)))
		}
	}
	out["estimated_used_bytes"] = stats(values)
	perZone := map[string]any{}
	for name, items := range zones {
		if len(items) >= 2 {
			perZone[name] = stats(items)
		}
	}
	out["zones"] = perZone
	if len(snaps) > 1 {
		out["first_last"] = Compare(snaps[0], snaps[len(snaps)-1])
	}
	return out
}
func validateSnapshot(s Snapshot) []string {
	problems := []string{}
	if s.Schema != 1 {
		problems = append(problems, "unexpected schema")
	}
	if s.Timestamp.IsZero() {
		problems = append(problems, "missing timestamp")
	}
	if s.Host == "" {
		problems = append(problems, "missing hostname")
	}
	if len(s.Zones) == 0 {
		problems = append(problems, "no UMA zones")
	}
	seen := map[string]bool{}
	for _, z := range s.Zones {
		if z.Name == "" {
			problems = append(problems, "unnamed zone")
		}
		if seen[z.Name] {
			problems = append(problems, "duplicate zone "+z.Name)
		}
		seen[z.Name] = true
	}
	if s.Fingerprint != "" && s.Fingerprint != fingerprint(s) {
		problems = append(problems, "fingerprint mismatch")
	}
	return problems
}
func parseDuration(s string) (time.Duration, error) {
	if n, err := strconv.ParseFloat(s, 64); err == nil {
		return time.Duration(n * float64(time.Second)), nil
	}
	return time.ParseDuration(s)
}
func usage() {
	fmt.Println("uma-forensics-go", version)
	fmt.Println("FreeBSD UMA allocation zone and kernel memory forensics")
	fmt.Println("Commands:")
	fmt.Println("  doctor              Inspect host support and command availability")
	fmt.Println("  snapshot            Capture vmstat -z, vmstat -m and selected sysctls")
	fmt.Println("  report              Analyze a saved snapshot or collect a fresh one")
	fmt.Println("  zones               List and filter UMA zones")
	fmt.Println("  malloc              List and filter kernel malloc types")
	fmt.Println("  sysctl              Display selected kernel memory tunables")
	fmt.Println("  compare             Compare two snapshots")
	fmt.Println("  watch               Periodically collect JSONL snapshots")
	fmt.Println("  series              Analyze a JSONL monitoring session")
	fmt.Println("  export              Export zones or malloc types as CSV")
	fmt.Println("  validate            Validate snapshot structure and fingerprint")
	fmt.Println("  selftest            Run offline parser and analytical checks")
	fmt.Println("  version             Print version")
	fmt.Println("Use 'uma-forensics-go <command> -h' for command-specific options")
}
func doctor() int {
	fmt.Printf("uma-forensics-go %s\nPlatform: %s/%s\nGo: %s\n", version, runtime.GOOS, runtime.GOARCH, runtime.Version())
	host, _ := os.Hostname()
	fmt.Println("Host:", host)
	required := []string{"vmstat", "sysctl", "uname"}
	optional := []string{"procstat", "top", "swapinfo", "netstat", "pkg", "freebsd-version"}
	failed := false
	for _, name := range required {
		p, err := exec.LookPath(name)
		if err != nil {
			fmt.Printf("REQUIRED %-18s unavailable\n", name)
			failed = true
		} else {
			fmt.Printf("REQUIRED %-18s %s\n", name, p)
		}
	}
	for _, name := range optional {
		p, err := exec.LookPath(name)
		if err != nil {
			fmt.Printf("OPTIONAL %-18s unavailable\n", name)
		} else {
			fmt.Printf("OPTIONAL %-18s %s\n", name, p)
		}
	}
	if runtime.GOOS != "freebsd" {
		fmt.Println("WARNING: this host is not FreeBSD")
		failed = true
	}
	if failed {
		return 1
	}
	return 0
}
func cmdSnapshot(args []string) error {
	fs := flag.NewFlagSet("snapshot", flag.ContinueOnError)
	out := fs.String("output", "-", "output JSON path or -")
	timeout := fs.Duration("timeout", 8*time.Second, "command timeout")
	raw := fs.Bool("raw", false, "include raw command output")
	strict := fs.Bool("strict", false, "require UMA zones")
	if err := fs.Parse(args); err != nil {
		return err
	}
	cfg := defaults()
	cfg.Timeout = *timeout
	cfg.IncludeRaw = *raw
	cfg.Strict = *strict
	s, err := Collect(cfg)
	if err != nil {
		return err
	}
	return WriteJSON(*out, s)
}
func cmdReport(args []string) error {
	fs := flag.NewFlagSet("report", flag.ContinueOnError)
	file := fs.String("input", "", "snapshot JSON path, empty collects live")
	top := fs.Int("top", 15, "largest zones to display")
	jsonOut := fs.Bool("json", false, "print JSON report")
	if err := fs.Parse(args); err != nil {
		return err
	}
	var s Snapshot
	var err error
	if *file != "" {
		s, err = ReadSnapshot(*file)
	} else {
		s, err = Collect(defaults())
	}
	if err != nil {
		return err
	}
	r := Analyze(s, *top)
	if *jsonOut {
		return WriteJSON("-", r)
	}
	textReport(r)
	return nil
}
func cmdZones(args []string) error {
	fs := flag.NewFlagSet("zones", flag.ContinueOnError)
	file := fs.String("input", "", "snapshot file")
	pattern := fs.String("match", "", "case-insensitive regex")
	sortBy := fs.String("sort", "bytes", "bytes, used, free, size, requests, failures, name")
	limit := fs.Int("limit", 40, "maximum rows, -1 unlimited")
	jsonOut := fs.Bool("json", false, "JSON output")
	if err := fs.Parse(args); err != nil {
		return err
	}
	var s Snapshot
	var err error
	if *file == "" {
		s, err = Collect(defaults())
	} else {
		s, err = ReadSnapshot(*file)
	}
	if err != nil {
		return err
	}
	var re *regexp.Regexp
	if *pattern != "" {
		re, err = regexp.Compile("(?i)" + *pattern)
		if err != nil {
			return err
		}
	}
	zones := []Zone{}
	for _, z := range s.Zones {
		if re == nil || re.MatchString(z.Name) {
			zones = append(zones, z)
		}
	}
	sort.Slice(zones, func(i, j int) bool {
		a, b := zones[i], zones[j]
		switch *sortBy {
		case "name":
			return a.Name < b.Name
		case "used":
			return a.Used > b.Used
		case "free":
			return a.Free > b.Free
		case "size":
			return a.Size > b.Size
		case "requests":
			return a.Requests > b.Requests
		case "failures":
			return a.Failures > b.Failures
		default:
			return saturatingMultiply(a.Size, a.Used) > saturatingMultiply(b.Size, b.Used)
		}
	})
	if *limit >= 0 && len(zones) > *limit {
		zones = zones[:*limit]
	}
	if *jsonOut {
		return WriteJSON("-", zones)
	}
	fmt.Printf("%-36s %8s %10s %10s %12s %12s\n", "ZONE", "SIZE", "USED", "FREE", "REQUESTS", "BYTES")
	for _, z := range zones {
		fmt.Printf("%-36.36s %8d %10d %10d %12d %12s\n", z.Name, z.Size, z.Used, z.Free, z.Requests, humanBytes(saturatingMultiply(z.Size, z.Used)))
	}
	return nil
}
func cmdMalloc(args []string) error {
	fs := flag.NewFlagSet("malloc", flag.ContinueOnError)
	file := fs.String("input", "", "snapshot path")
	pattern := fs.String("match", "", "name regex")
	limit := fs.Int("limit", 40, "maximum rows")
	jsonOut := fs.Bool("json", false, "JSON output")
	if err := fs.Parse(args); err != nil {
		return err
	}
	var s Snapshot
	var err error
	if *file == "" {
		s, err = Collect(defaults())
	} else {
		s, err = ReadSnapshot(*file)
	}
	if err != nil {
		return err
	}
	var re *regexp.Regexp
	if *pattern != "" {
		re, err = regexp.Compile("(?i)" + *pattern)
		if err != nil {
			return err
		}
	}
	types := []MallocType{}
	for _, m := range s.Malloc {
		if re == nil || re.MatchString(m.Name) {
			types = append(types, m)
		}
	}
	sort.Slice(types, func(i, j int) bool { return types[i].Memory > types[j].Memory })
	if *limit >= 0 && len(types) > *limit {
		types = types[:*limit]
	}
	if *jsonOut {
		return WriteJSON("-", types)
	}
	fmt.Printf("%-36s %12s %12s %12s %12s\n", "TYPE", "INUSE", "MEMORY", "HIGHUSE", "REQUESTS")
	for _, m := range types {
		fmt.Printf("%-36.36s %12d %12d %12d %12d\n", m.Name, m.InUse, m.Memory, m.HighUse, m.Requests)
	}
	return nil
}
func cmdSysctl(args []string) error {
	fs := flag.NewFlagSet("sysctl", flag.ContinueOnError)
	file := fs.String("input", "", "snapshot path")
	pattern := fs.String("match", "", "key regex")
	jsonOut := fs.Bool("json", false, "JSON output")
	if err := fs.Parse(args); err != nil {
		return err
	}
	var s Snapshot
	var err error
	if *file == "" {
		s, err = Collect(defaults())
	} else {
		s, err = ReadSnapshot(*file)
	}
	if err != nil {
		return err
	}
	var re *regexp.Regexp
	if *pattern != "" {
		re, err = regexp.Compile("(?i)" + *pattern)
		if err != nil {
			return err
		}
	}
	out := map[string]string{}
	keys := []string{}
	for k, v := range s.Sysctl {
		if re == nil || re.MatchString(k) {
			out[k] = v
			keys = append(keys, k)
		}
	}
	sort.Strings(keys)
	if *jsonOut {
		return WriteJSON("-", out)
	}
	for _, k := range keys {
		fmt.Printf("%-42s %s\n", k, out[k])
	}
	return nil
}
func cmdCompare(args []string) error {
	fs := flag.NewFlagSet("compare", flag.ContinueOnError)
	top := fs.Int("top", 40, "maximum displayed zones")
	jsonOut := fs.Bool("json", false, "JSON output")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if fs.NArg() != 2 {
		return errors.New("usage: compare [flags] before.json after.json")
	}
	a, err := ReadSnapshot(fs.Arg(0))
	if err != nil {
		return err
	}
	b, err := ReadSnapshot(fs.Arg(1))
	if err != nil {
		return err
	}
	c := Compare(a, b)
	if *jsonOut {
		return WriteJSON("-", c)
	}
	textComparison(c, *top)
	return nil
}
func cmdWatch(args []string) error {
	fs := flag.NewFlagSet("watch", flag.ContinueOnError)
	out := fs.String("jsonl", "uma-session.jsonl", "JSONL output path")
	interval := fs.String("interval", "5s", "sample interval")
	count := fs.Int("count", 12, "number of samples, 0 unlimited")
	timeout := fs.Duration("timeout", 8*time.Second, "per command timeout")
	quiet := fs.Bool("quiet", false, "suppress progress")
	if err := fs.Parse(args); err != nil {
		return err
	}
	d, err := parseDuration(*interval)
	if err != nil {
		return err
	}
	if d < time.Second {
		return errors.New("interval must be at least one second")
	}
	if *count < 0 {
		return errors.New("count must be nonnegative")
	}
	cfg := defaults()
	cfg.Timeout = *timeout
	var previous *Snapshot
	for i := 0; *count == 0 || i < *count; i++ {
		start := time.Now()
		s, err := Collect(cfg)
		if err != nil {
			return err
		}
		if err = WriteJSONL(*out, s); err != nil {
			return err
		}
		if !*quiet {
			r := Analyze(s, 0)
			fmt.Fprintf(os.Stderr, "sample=%d timestamp=%s zones=%d estimated_used=%s", i+1, s.Timestamp.Format(time.RFC3339), len(s.Zones), humanBytes(r.EstimatedUsedBytes))
			if previous != nil {
				c := Compare(*previous, s)
				fmt.Fprintf(os.Stderr, " growth=%+d", c.TotalGrowthBytes)
			}
			fmt.Fprintln(os.Stderr)
		}
		previous = &s
		if *count > 0 && i+1 >= *count {
			break
		}
		sleep := d - time.Since(start)
		if sleep > 0 {
			time.Sleep(sleep)
		}
	}
	return nil
}
func cmdSeries(args []string) error {
	fs := flag.NewFlagSet("series", flag.ContinueOnError)
	input := fs.String("input", "uma-session.jsonl", "JSONL input path")
	if err := fs.Parse(args); err != nil {
		return err
	}
	snaps, err := ReadJSONL(*input)
	if err != nil {
		return err
	}
	return WriteJSON("-", seriesReport(snaps))
}
func cmdExport(args []string) error {
	fs := flag.NewFlagSet("export", flag.ContinueOnError)
	input := fs.String("input", "", "snapshot JSON path")
	output := fs.String("output", "-", "CSV output path")
	kind := fs.String("kind", "zones", "zones or malloc")
	if err := fs.Parse(args); err != nil {
		return err
	}
	var s Snapshot
	var err error
	if *input == "" {
		s, err = Collect(defaults())
	} else {
		s, err = ReadSnapshot(*input)
	}
	if err != nil {
		return err
	}
	switch *kind {
	case "zones":
		return writeZonesCSV(*output, s.Zones)
	case "malloc":
		return writeMallocCSV(*output, s.Malloc)
	default:
		return errors.New("kind must be zones or malloc")
	}
}
func cmdValidate(args []string) error {
	fs := flag.NewFlagSet("validate", flag.ContinueOnError)
	if err := fs.Parse(args); err != nil {
		return err
	}
	if fs.NArg() != 1 {
		return errors.New("usage: validate snapshot.json")
	}
	s, err := ReadSnapshot(fs.Arg(0))
	if err != nil {
		return err
	}
	problems := validateSnapshot(s)
	if len(problems) > 0 {
		for _, p := range problems {
			fmt.Println("FAIL:", p)
		}
		return fmt.Errorf("%d validation problems", len(problems))
	}
	fmt.Println("PASS: snapshot structure and fingerprint")
	return nil
}
func selftest() error {
	fixture := "ITEM                   SIZE  LIMIT     USED     FREE      REQ FAIL SLEEP\nTCP:                    512, 0, 12, 5, 100, 0, 0\n"
	zones := ParseZones(fixture)
	if len(zones) != 1 {
		return fmt.Errorf("zone parser: got %d", len(zones))
	}
	z := zones[0]
	if z.Name != "TCP" || z.Size != 512 || z.Used != 12 || z.Requests != 100 {
		return errors.New("zone fields mismatch")
	}
	if len(ParseZones("nonsense\n")) != 0 {
		return errors.New("invalid zone accepted")
	}
	if parseUnsigned("1,024") != 1024 {
		return errors.New("numeric parser mismatch")
	}
	sys := ParseSysctl("vm.test: 100\nkern.foo: bar\n")
	if sys["vm.test"] != "100" {
		return errors.New("sysctl parser mismatch")
	}
	a := Snapshot{Schema: 1, Timestamp: time.Unix(100, 0), Host: "fixture", Zones: []Zone{{Name: "TCP", Size: 512, Used: 10, Requests: 20}}, Sysctl: map[string]string{}}
	b := Snapshot{Schema: 1, Timestamp: time.Unix(110, 0), Host: "fixture", Zones: []Zone{{Name: "TCP", Size: 512, Used: 12, Requests: 40}}, Sysctl: map[string]string{}}
	a.Fingerprint = fingerprint(a)
	b.Fingerprint = fingerprint(b)
	c := Compare(a, b)
	if c.TotalGrowthBytes != 1024 || c.Zones[0].RequestDelta != 20 {
		return errors.New("comparison mismatch")
	}
	r := Analyze(b, 10)
	if r.EstimatedUsedBytes != 6144 {
		return errors.New("analysis mismatch")
	}
	if len(validateSnapshot(a)) != 0 {
		return errors.New("snapshot validation mismatch")
	}
	if math.Abs(percentile([]float64{1, 2, 3, 4, 5}, .5)-3) > 1e-9 {
		return errors.New("percentile mismatch")
	}
	fmt.Println("PASS zone parsing")
	fmt.Println("PASS malformed input handling")
	fmt.Println("PASS numeric parsing")
	fmt.Println("PASS sysctl parsing")
	fmt.Println("PASS snapshot fingerprint")
	fmt.Println("PASS comparison")
	fmt.Println("PASS analysis")
	fmt.Println("PASS validation")
	fmt.Println("PASS statistical percentiles")
	return nil
}
func main() {
	if len(os.Args) < 2 {
		usage()
		return
	}
	cmd := os.Args[1]
	args := os.Args[2:]
	var err error
	switch cmd {
	case "help", "-h", "--help":
		usage()
	case "version", "--version":
		fmt.Println(version)
	case "doctor":
		os.Exit(doctor())
	case "snapshot":
		err = cmdSnapshot(args)
	case "report":
		err = cmdReport(args)
	case "zones":
		err = cmdZones(args)
	case "malloc":
		err = cmdMalloc(args)
	case "sysctl":
		err = cmdSysctl(args)
	case "compare":
		err = cmdCompare(args)
	case "watch":
		err = cmdWatch(args)
	case "series":
		err = cmdSeries(args)
	case "export":
		err = cmdExport(args)
	case "validate":
		err = cmdValidate(args)
	case "selftest":
		err = selftest()
	default:
		err = fmt.Errorf("unknown command %q", cmd)
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "error:", err)
		os.Exit(1)
	}
}
