package main

import (
	"flag"
	"fmt"
	"html"
	"log"
	"net/http"
	"os"
	"runtime"
	"runtime/debug"
	"sort"
	"strconv"
	"text/template"

	"github.com/temorfeouz/heapdump14/read"
)

const (
	defaultAddr = ":8080" // default webserver address
	maxFields   = 4096 + 1
)

var (
	httpAddr = flag.String("http", defaultAddr, "HTTP service address")
)

// d is the loaded heap dump.
var d *read.Dump

// link to type's page
func typeLink(ft *read.FullType) string {
	return fmt.Sprintf("<a href=\"type?id=%d\">%s</a>", ft.Id, ft.Name)
}

func objLink(x read.ObjId) string {
	return fmt.Sprintf("<a href=obj?id=%d>object %x</a>", x, d.Addr(x))
}

// returns an html string representing the target of an Edge
func edgeLink(e read.Edge) string {
	s := objLink(e.To)
	if e.ToOffset != 0 {
		s = fmt.Sprintf("%s+%d", s, e.ToOffset)
	}
	return s
}

// returns an html string representing the source of an Edge
func edgeSource(x read.ObjId, e read.Edge) string {
	s := objLink(x)
	if e.FieldName != "" {
		s = fmt.Sprintf("%s.%s: %s", s, e.FieldName, d.Ft(x).Name)
	} else if e.ToOffset != 0 {
		s = fmt.Sprintf("%s+%d: %s", s, e.ToOffset, d.Ft(x).Name)
	}
	return s
}

// the first d.PtrSize bytes of b contain a pointer.  Return html
// to represent that pointer.
func nonheapPtr(b []byte) string {
	p := readPtr(b)
	return nonheapAddr(p)
}

func nonheapAddr(p uint64) string {
	if p == 0 {
		return "nil"
	} else if p >= d.HeapStart && p < d.HeapEnd {
		return fmt.Sprintf("%x: unknown heap+%x", p, p-d.HeapStart)
	} else {
		for _, s := range d.SectionInfo {
			if p >= s.Start && p < s.End {
				return fmt.Sprintf("%x: %s+%x", p, s.Name, p-s.Start)
			}
		}
		//if uint64(len(d.Bss.Fields)) <= p {
		//	return fmt.Sprintf("%+v", d.Bss.Fields[p])
		//}
		//for k, v := range d.Bss.Fields {
		//
		//}
		// TODO: look up symbol in executable
		return fmt.Sprintf("%x: outsideheap", p)
	}
}

// display field
type Field struct {
	Addr  uint64
	Name  string
	Typ   string
	Value string
}

// rawBytes generates an html string representing the given raw bytes
func rawBytes(b []byte) string {
	v := ""
	s := ""
	for _, c := range b {
		v += fmt.Sprintf("%.2x ", c)
		if c <= 32 || c >= 127 {
			c = 46
		}
		s += fmt.Sprintf("%c", c)
	}
	return v + " | " + html.EscapeString(s)
}

func dump(bytes []byte) string {
	str := ""
	for i, b := range bytes {
		if i >= 16 {
			return str
		}
		return string(bytes)
		str = fmt.Sprintf("%s%02x&nbsp;", str, b)
	}
	return str
}

// getFields uses the data in b to fill in the values for the given field list.
// edges is a list of known connecting out edges.
func getFields(b []byte, fields []read.Field, edges []read.Edge) []Field {
	var r []Field
	off := uint64(0)
	for _, f := range fields {
		if f.Offset < off {
			log.Fatalf("out of order fields %x < %x", f.Offset, off)
		}
		if f.Offset > off {
			r = append(r, Field{off, fmt.Sprintf("<font color=LightGray>pad %d</font>", f.Offset-off),
				"", dump(b[off:f.Offset])})
			off = f.Offset
		}
		var value string
		var typ string
		switch f.Kind {
		case read.FieldKindBool:
			if b[off] == 0 {
				value = "false"
			} else {
				value = "true"
			}
			typ = "bool"
			off++
		case read.FieldKindUInt8:
			value = fmt.Sprintf("%d", b[off])
			typ = "uint8"
			off++
		case read.FieldKindSInt8:
			value = fmt.Sprintf("%d", int8(b[off]))
			typ = "int8"
			off++
		case read.FieldKindUInt16:
			value = fmt.Sprintf("%d", d.Order.Uint16(b[off:]))
			typ = "uint16"
			off += 2
		case read.FieldKindSInt16:
			value = fmt.Sprintf("%d", int16(d.Order.Uint16(b[off:])))
			typ = "int16"
			off += 2
		case read.FieldKindUInt32:
			value = fmt.Sprintf("%d", d.Order.Uint32(b[off:]))
			typ = "uint32"
			off += 4
		case read.FieldKindSInt32:
			value = fmt.Sprintf("%d", int32(d.Order.Uint32(b[off:])))
			typ = "int32"
			off += 4
		case read.FieldKindUInt64:
			value = fmt.Sprintf("%d", d.Order.Uint64(b[off:]))
			typ = "uint64"
			off += 8
		case read.FieldKindSInt64:
			value = fmt.Sprintf("%d", int64(d.Order.Uint64(b[off:])))
			typ = "int64"
			off += 8
		case read.FieldKindBytes4:
			value = rawBytes(b[off : off+4])
			typ = "raw bytes"
			off += 4
		case read.FieldKindBytes8:
			value = rawBytes(b[off : off+8])
			typ = "raw bytes"
			off += 8
		case read.FieldKindBytes16:
			value = rawBytes(b[off : off+16])
			typ = "raw bytes"
			off += 16
		case read.FieldKindPtr:
			typ = "*" + read.PtrName(d, f.Type)
			// TODO: get ptr base type somehow?  Also for slices,chans.
			if len(edges) > 0 && edges[0].FromOffset == off {
				value = edgeLink(edges[0])
				edges = edges[1:]
			} else {
				value = nonheapPtr(b[off:])
			}
			off += d.PtrSize
		case read.FieldKindIface:
			// TODO: the itab part?
			typ = "interface{...} " + read.IfaceName(d, readPtr(b[off:]))
			if len(edges) > 0 && edges[0].FromOffset == off+d.PtrSize {
				value = edgeLink(edges[0])
				edges = edges[1:]
			} else {
				// TODO: use itab to decide whether this is a
				// pointer or a scalar.
				value = nonheapPtr(b[off+d.PtrSize:])
			}
			off += 2 * d.PtrSize
		case read.FieldKindEface:
			// TODO: the type part
			typ = "interface{} " + read.EfaceName(d, readPtr(b[off:]))
			if len(edges) > 0 && edges[0].FromOffset == off+d.PtrSize {
				value = edgeLink(edges[0])
				edges = edges[1:]
			} else {
				// TODO: use type to decide whether this is a
				// pointer or a scalar.
				value = nonheapPtr(b[off+d.PtrSize:])
			}
			off += 2 * d.PtrSize
		case read.FieldKindString:
			typ = "string"
			if len(edges) > 0 && edges[0].FromOffset == off {
				value = edgeLink(edges[0])
				edges = edges[1:]
			} else {
				value = nonheapPtr(b[off:])
			}
			value = fmt.Sprintf("%s/%d", value, readPtr(b[off+d.PtrSize:]))
			off += 2 * d.PtrSize
		case read.FieldKindSlice:
			typ = "[]" + f.Type.Name()
			if len(edges) > 0 && edges[0].FromOffset == off {
				value = edgeLink(edges[0])
				edges = edges[1:]
			} else {
				value = nonheapPtr(b[off:])
			}
			value = fmt.Sprintf("%s/%d/%d", value, readPtr(b[off+d.PtrSize:]), readPtr(b[off+2*d.PtrSize:]))
			off += 3 * d.PtrSize
		case read.FieldKindBytesElided:
			typ = "raw bytes"
			value = fmt.Sprintf("... %d elided bytes ...", uint64(len(b))-off)
			off = uint64(len(b))
		default:
			typ = fmt.Sprintf("%d = %v", f.Kind, f.Kind)
		}
		r = append(r, Field{f.Offset, f.Name, typ, value})
	}
	if uint64(len(b)) > off {
		r = append(r, Field{off, fmt.Sprintf("<font color=LightGray>sizeclass pad %d</font>", uint64(len(b))-off), "", ""})
	}
	return r
}

type objInfo struct {
	Addr      uint64
	Typ       string
	DataSize  uint64
	TypeSize  uint64
	ExtraSize uint64
	Instances []instanceInfo
	Referrers []string
	IDom      string
	Dominates uint64
}

type instanceInfo struct {
	Fields []Field
}

var objTemplate = template.Must(template.New("obj").Parse(`
<html>
<head>
<style>
table
{
border-collapse:collapse;
}
table, td, th
{
border:1px solid grey;
}
</style>
<title>Object {{printf "%x" .Addr}}</title>
</head>
<body>
<tt>
<h2>Object {{printf "%x" .Addr}} : {{.Typ}}</h2>
<h3>Type {{.TypeSize}} bytes, data {{ .DataSize }} bytes, {{ .ExtraSize }} bytes of extra padding</h3>
{{ range .Instances }}
<table>
<tr>
<td>Address</td>
<td>Field</td>
<td>Type</td>
<td>Value</td>
</tr>
{{range .Fields}}
<tr>
<td>{{ printf "%x" .Addr}}</td>
<td>{{.Name}}</td>
<td>{{.Typ}}</td>
<td>{{.Value}}</td>
</tr>
{{end}}
</table>
<br>
{{end}}
<h3>Referrers</h3>
{{range .Referrers}}
{{.}}
<br>
{{end}}
<h3>Immediate dominator</h3>
{{ .IDom }}
<br>
<h3>Heap dominated by this object</h3>
{{.Dominates}} bytes
</tt>
</body>
</html>
`))

func objHandler(w http.ResponseWriter, r *http.Request) {
	q := r.URL.Query()
	v := q["id"]
	if len(v) != 1 {
		http.Error(w, "id parameter missing", 405)
		return
	}
	id, err := strconv.ParseUint(v[0], 10, 64)
	if err != nil {
		http.Error(w, err.Error(), 405)
		return
	}

	if int(id) >= d.NumObjects() {
		http.Error(w, "object not found", 405)
		return
	}
	x := read.ObjId(id)

	ft := d.Ft(x)
	data := d.Contents(x)
	instances := make([]instanceInfo, 0, uint64(len(data))/ft.Size)
	for uint64(len(data)) >= ft.Size {
		fld := getFields(data[:ft.Size], ft.Fields, d.Edges(x))
		if len(fld) > maxFields {
			msg := fmt.Sprintf("<font color=Red>elided for display: %d fields</font>", len(fld)-(maxFields-1))
			fld = fld[:maxFields-1]
			fld = append(fld, Field{0, msg, "", ""})
		}
		instances = append(instances, instanceInfo{fld})
		data = data[ft.Size:]
	}

	ref := getReferrers(x)
	if len(ref) > maxFields {
		msg := fmt.Sprintf("<font color=Red>elided for display: %d referrers</font>", len(ref)-(maxFields-1))
		ref = ref[:maxFields-1]
		ref = append(ref, msg)
	}

	var myIdom string
	if idom[x] == read.ObjNil {
		myIdom = "not reachable"
	} else if int(idom[x]) >= d.NumObjects() {
		myIdom = "none"
	} else {
		myIdom = objLink(idom[x])
	}
	info := objInfo{
		d.Addr(x),
		typeLink(ft),
		d.Size(x),
		ft.Size,
		uint64(len(data)),
		instances,
		ref,
		myIdom,
		domsize[x],
	}
	if err := objTemplate.Execute(w, info); err != nil {
		log.Print(err)
	}
}

type objEntry struct {
	Id   read.ObjId
	Addr uint64
}
type typeInfo struct {
	Name      string
	Size      uint64
	Instances []string
}

var typeTemplate = template.Must(template.New("type").Parse(`
<html>
<head>
<title>Type {{.Name}}</title>
</head>
<body>
<tt>
<h2>{{.Name}}</h2>
<h3>Size {{.Size}}</h3>
<h3>Instances</h3>
<table>
{{range .Instances}}
<tr><td>{{.}}</td></tr>
{{end}}
</table>
</tt>
</body>
</html>
`))

func typeHandler(w http.ResponseWriter, r *http.Request) {
	q := r.URL.Query()
	s := q["id"]
	if len(s) != 1 {
		http.Error(w, "type id missing", 405)
		return
	}
	id, err := strconv.ParseUint(s[0], 10, 64)
	if err != nil {
		http.Error(w, err.Error(), 405)
		return
	}

	if id >= uint64(len(d.FTList)) {
		http.Error(w, "can't find type", 405)
		return
	}

	ft := d.FTList[id]
	var info typeInfo
	info.Name = ft.Name
	info.Size = ft.Size
	for _, x := range byType[ft.Id].objects {
		info.Instances = append(info.Instances, fmt.Sprintf("%s: %d bytes", objLink(x), d.Size(x)))
	}
	if err := typeTemplate.Execute(w, info); err != nil {
		log.Print(err)
	}
}

type hentry struct {
	Name  string
	Count int
	Bytes string
	Dom   uint64
}

var histoTemplate = template.Must(template.New("histo").Parse(`
<html>
<head>
<style>
table
{
border-collapse:collapse;
}
table, td, th
{
border:1px solid grey;
}
</style>
<title>Type histogram</title>
</head>
<body>
<a href="/">&lt;&lt; Overview</a><br>
<tt>
<table>
<col align="left">
<col align="right">
<col align="right">
<tr>
<td align="right">Count</td>
<td align="right"><a href="histo?by=bytes">Bytes</a></td>
<td align="right"><a href="histo?by=dom">Domination</a></td>
<td>Type</td>
</tr>
{{range .}}
<tr>
<td align="right">{{.Count}}</td>
<td align="right">{{.Bytes}}</td>
<td align="right">{{.Dom}}</td>
<td>{{.Name}}</td>
</tr>
{{end}}
</table>
</tt>
</body>
</html>
`))

func histoHandler(w http.ResponseWriter, r *http.Request) {
	// build sorted list of types
	by := r.URL.Query()["by"]
	var s []hentry
	for id, b := range byType {
		if b.bytes == 0 {
			// This can happen for raw types that were superceded by dwarf types
			continue
		}
		ft := d.FTList[id]
		dom := uint64(0)
		for o, _ := range b.objects {
			dom += domsize[o]
		}
		s = append(s, hentry{typeLink(ft), len(b.objects), read.BtsToHuman(b.bytes), dom})
	}
	if by == nil || len(by) == 0 || by[0] == "bytes" {
		sort.Sort(ByBytes(s))
	} else if by[0] == "dom" {
		sort.Sort(ByDom(s))
	}

	if err := histoTemplate.Execute(w, s); err != nil {
		log.Print(err)
	}
}

type ByBytes []hentry

func (a ByBytes) Len() int           { return len(a) }
func (a ByBytes) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a ByBytes) Less(i, j int) bool { return a[i].Bytes > a[j].Bytes }

type ByDom []hentry

func (a ByDom) Len() int           { return len(a) }
func (a ByDom) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a ByDom) Less(i, j int) bool { return a[i].Dom > a[j].Dom }

type mainInfo struct {
	HeapSize         string
	HeapUsed         string
	NumObjects       int
	ReachableObjects int
	ReachableBytes   string
}

var mainTemplate = template.Must(template.New("histo").Parse(`
<html>
<head>
<title>Heap dump viewer</title>
</head>
<body>
<tt>

<h2>Heap dump viewer</h2>
<br>
Heap size: {{.HeapSize}} bytes
<br>
Heap live: {{.HeapUsed}} bytes
<br>
Heap objects: {{.NumObjects}}
<br>
Reachable objects: {{.ReachableObjects}}
<br>
Reachable size: {{.ReachableBytes}} bytes
<br>
<a href="histo">Type Histogram</a><br>
<a href="globals">Globals</a><br>
<a href="goroutines">Goroutines</a><br>
<a href="others">Miscellaneous Roots</a><br>
<a href="memory">Memory by address</a><br>
</tt>
</body>
</html>
`))

func mainHandler(w http.ResponseWriter, r *http.Request) {
	reachableObjects := 0
	reachableBytes := uint64(0)
	n := d.NumObjects()
	for i, dom := range domsize {
		if dom != 0 && i != n {
			reachableObjects++
			reachableBytes += d.Size(read.ObjId(i))
		}
	}
	i := mainInfo{read.BtsToHuman(d.HeapEnd - d.HeapStart), read.BtsToHuman(d.Memstats.Alloc), n, reachableObjects, read.BtsToHuman(reachableBytes)}
	if err := mainTemplate.Execute(w, i); err != nil {
		log.Print(err)
	}
}

type globalsinfo struct {
	Data []Field
	Bss  []Field
}

var globalsTemplate = template.Must(template.New("globals").Parse(`
<html>
<head>
<style>
table
{
border-collapse:collapse;
}
table, td, th
{
border:1px solid grey;
}
</style>
<title>Global roots</title>
</head>
<body>
<tt>
<h2>Global roots</h2>
<table>
<tr>
<td colspan=4>.data section</td>
</tr>
<tr>
<td>Address</td>
<td>Name</td>
<td>Type</td>
<td>Value</td>
</tr>
{{range .Data}}
<tr>
<td>{{printf "%08x" .Addr}}</td>
<td>{{.Name}}</td>
<td>{{.Typ}}</td>
<td>{{.Value}}</td>
</tr>
{{end}}
<tr>
<td colspan=4>.bss section</td>
</tr>
<tr>
<td>Address</td>
<td>Name</td>
<td>Type</td>
<td>Value</td>
</tr>
{{range .Bss}}
<tr>
<td>{{printf "%08x" .Addr}}</td>
<td>{{.Name}}</td>
<td>{{.Typ}}</td>
<td>{{.Value}}</td>
</tr>
{{end}}
</table>
</tt>
</body>
</html>
`))

func globalsHandler(w http.ResponseWriter, r *http.Request) {
	gi := globalsinfo{
		getFields(d.Data.Data, d.Data.Fields, d.Data.Edges),
		getFields(d.Bss.Data, d.Bss.Fields, d.Bss.Edges),
	}
	if err := globalsTemplate.Execute(w, gi); err != nil {
		log.Print(err)
	}
}

var othersTemplate = template.Must(template.New("others").Parse(`
<html>
<head>
<style>
table
{
border-collapse:collapse;
}
table, td, th
{
border:1px solid grey;
}
</style>
<title>Other roots</title>
</head>
<body>
<tt>
<h2>Other roots</h2>
<table>
<tr>
<td>Name</td>
<td>Type</td>
<td>Value</td>
</tr>
{{range .}}
<tr>
<td>{{.Name}}</td>
<td>{{.Typ}}</td>
<td>{{.Value}}</td>
</tr>
{{end}}
</table>
</tt>
</body>
</html>
`))

func othersHandler(w http.ResponseWriter, r *http.Request) {
	var f []Field
	for _, x := range d.Otherroots {
		for _, e := range x.Edges {
			f = append(f, Field{0, x.Description, "unknown", edgeLink(e)})
		}
	}
	if err := othersTemplate.Execute(w, f); err != nil {
		log.Print(err)
	}
}

type meminfo struct {
	Link string
	Typ  string
}

var memoryTemplate = template.Must(template.New("memory").Parse(`
<html>
<head>
<style>
table
{
border-collapse:collapse;
}
table, td, th
{
border:1px solid grey;
}
</style>
<title>Memory</title>
</head>
<body>
<tt>
<h2>Memory</h2>
{{range .}}
{{.Link}} {{.Typ}}<br>
{{end}}
</tt>
</body>
</html>
`))

func memoryHandler(w http.ResponseWriter, r *http.Request) {
	var m []meminfo
	start := d.HeapStart
	startStr, hasStart := r.URL.Query()["start"]
	if hasStart {
		tmp, err := strconv.ParseUint(startStr[0], 16, 64)
		if err == nil {
			start = tmp
		}
	}
	count := 0
	prev := read.ObjNil
	for a := start; a < d.HeapEnd; a += d.PtrSize {
		x := d.FindObj(a)
		if x != read.ObjNil && x != prev {
			m = append(m, meminfo{objLink(x), d.Ft(x).Name})
			prev = x
			count++
			if count >= 10000 {
				break
			}
		}
	}
	if err := memoryTemplate.Execute(w, m); err != nil {
		log.Print(err)
	}
}

type goListInfo struct {
	Name  string
	State string
}

var goListTemplate = template.Must(template.New("golist").Parse(`
<html>
<head>
<style>
table
{
border-collapse:collapse;
}
table, td, th
{
border:1px solid grey;
}
</style>
<title>Goroutines</title>
</head>
<body>
<tt>
<h2>Goroutines</h2>
<table>
<tr>
<td>Name</td>
<td>State</td>
</tr>
{{range .}}
<tr>
<td>{{.Name}}</td>
<td>{{.State}}</td>
</tr>
{{end}}
</table>
</tt>
</body>
</html>
`))

func goListHandler(w http.ResponseWriter, r *http.Request) {
	var i []goListInfo
	for _, g := range d.Goroutines {
		name := fmt.Sprintf("<a href=go?id=%x>goroutine %x</a>", g.Addr, g.Addr)
		var state string
		switch g.Status {
		case 0:
			state = "idle"
		case 1:
			state = "runnable"
		case 2:
			// running - shouldn't happen
			log.Fatal("found running goroutine in heap dump")
		case 3:
			state = "syscall"
		case 4:
			state = g.WaitReason
		case 5:
			state = "dead"
		default:
			log.Fatal("unknown goroutine status")
		}
		i = append(i, goListInfo{name, state})
	}
	// sort by state
	sort.Sort(ByState(i))
	if err := goListTemplate.Execute(w, i); err != nil {
		log.Print(err)
	}
}

type ByState []goListInfo

func (a ByState) Len() int           { return len(a) }
func (a ByState) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a ByState) Less(i, j int) bool { return a[i].State < a[j].State }

type goInfo struct {
	Addr   uint64
	Obj    read.ObjId
	State  string
	Frames []string
}

var goTemplate = template.Must(template.New("go").Parse(`
<html>
<head>
<style>
table
{
border-collapse:collapse;
}
table, td, th
{
border:1px solid grey;
}
</style>
<title>Goroutine {{printf "%x" .Addr}}</title>
</head>
<body>
<tt>
<h2>Goroutine <a href=obj?id={{.Obj}}>{{printf "%x" .Addr}}</a></h2>
<h3>{{.State}}</h3>
<h3>Stack</h3>
{{range .Frames}}
{{.}}
<br>
{{end}}
</tt>
</body>
</html>
`))

func goHandler(w http.ResponseWriter, r *http.Request) {
	q := r.URL.Query()
	v := q["id"]
	if len(v) != 1 {
		http.Error(w, "id parameter missing", 405)
		return
	}
	addr, err := strconv.ParseUint(v[0], 16, 64)
	if err != nil {
		http.Error(w, err.Error(), 405)
		return
	}
	var g *read.GoRoutine
	for _, x := range d.Goroutines {
		if x.Addr == addr {
			g = x
			break
		}
	}
	if g == nil {
		http.Error(w, "goroutine not found", 405)
		return
	}

	var i goInfo
	i.Addr = g.Addr
	i.Obj = d.FindObj(g.Addr)
	switch g.Status {
	case 0:
		i.State = "idle"
	case 1:
		i.State = "runnable"
	case 2:
		// running - shouldn't happen
		log.Fatal("found running goroutine in heap dump")
	case 3:
		i.State = "syscall"
	case 4:
		i.State = g.WaitReason
	case 5:
		i.State = "dead"
	default:
		log.Fatal("unknown goroutine status")
	}

	for f := g.Bos; f != nil; f = f.Parent {
		i.Frames = append(i.Frames, fmt.Sprintf("<a href=frame?id=%x&depth=%d>%s</a>", f.Addr, f.Depth, f.Name))
	}

	if err := goTemplate.Execute(w, i); err != nil {
		log.Print(err)
	}
}

type frameInfo struct {
	Addr      uint64
	Name      string
	Depth     uint64
	Goroutine string
	Vars      []Field
}

var frameTemplate = template.Must(template.New("frame").Parse(`
<html>
<head>
<style>
table
{
border-collapse:collapse;
}
table, td, th
{
border:1px solid grey;
}
</style>
<title>Frame {{.Name}}</title>
</head>
<body>
<tt>
<h2>Frame {{.Name}} {{ printf "%x" .Addr }}</h2>
<h3>In {{.Goroutine}}</h3>
<h3>Variables</h3>
<table>
<tr>
<td>Offset</td>
<td>Name</td>
<td>Type</td>
<td>Value</td>
</tr>
{{range .Vars}}
<tr>
<td>{{ printf "%x" .Addr }}
<td>{{.Name}}</td>
<td>{{.Typ}}</td>
<td>{{.Value}}</td>
</tr>
{{end}}
</table>
</tt>
</body>
</html>
`))

func frameHandler(w http.ResponseWriter, r *http.Request) {
	q := r.URL.Query()
	v := q["id"]
	if len(v) != 1 {
		http.Error(w, "id parameter missing", 405)
		return
	}
	addr, err := strconv.ParseUint(v[0], 16, 64)
	if err != nil {
		http.Error(w, err.Error(), 405)
		return
	}
	z := q["depth"]
	if len(z) != 1 {
		http.Error(w, "depth parameter missing", 405)
		return
	}
	depth, err := strconv.ParseUint(z[0], 10, 64)
	if err != nil {
		http.Error(w, err.Error(), 405)
		return
	}

	var f *read.StackFrame
	for _, g := range d.Frames {
		if g.Addr == addr && g.Depth == depth {
			f = g
			break
		}
	}
	if f == nil {
		http.Error(w, "stack frame not found", 405)
		return
	}

	var i frameInfo
	i.Addr = f.Addr
	i.Name = f.Name
	i.Depth = f.Depth
	i.Goroutine = fmt.Sprintf("<a href=go?id=%x>goroutine %x</a>", f.Goroutine.Addr, f.Goroutine.Addr)

	// variables
	i.Vars = getFields(f.Data, f.Fields, f.Edges)

	if err := frameTemplate.Execute(w, i); err != nil {
		log.Print(err)
	}
}

// So meta.
func heapdumpHandler(w http.ResponseWriter, r *http.Request) {
	f, err := os.Create("metadump")
	if err != nil {
		panic(err)
	}
	runtime.GC()
	debug.WriteHeapDump(f.Fd())
	f.Close()
	w.Write([]byte("done"))
}

func usage() {
	fmt.Fprintf(os.Stderr,
		"usage: hview heapdump [executable]\n")
	flag.PrintDefaults()
	os.Exit(2)
}

func main() {
	flag.Usage = usage
	flag.Parse()

	var dump, exec string
	args := flag.Args()
	switch len(args) {
	case 1:
		dump = args[0]
		exec = ""
	case 2:
		dump = args[0]
		exec = args[1]
	default:
		usage()
		return
	}

	fmt.Println("Loading...")
	d = read.Read(dump, exec)

	fmt.Println("Analyzing...")
	prepare()

	fmt.Println("Ready.  Point your browser to localhost" + *httpAddr)
	http.HandleFunc("/", mainHandler)
	http.HandleFunc("/obj", objHandler)
	http.HandleFunc("/type", typeHandler)
	http.HandleFunc("/histo", histoHandler)
	http.HandleFunc("/globals", globalsHandler)
	http.HandleFunc("/goroutines", goListHandler)
	http.HandleFunc("/go", goHandler)
	http.HandleFunc("/frame", frameHandler)
	http.HandleFunc("/others", othersHandler)
	http.HandleFunc("/memory", memoryHandler)
	http.HandleFunc("/heapdump", heapdumpHandler)
	if err := http.ListenAndServe(*httpAddr, nil); err != nil {
		log.Fatal(err)
	}
}

// Map from object ID to list of objects that refer to that object.
// It is split in two parts for efficiency.  If an object x has <= 1
// inbound edge, we store it in ref1[x].  Otherwise, it is stored in ref2[x].
// Since most objects have only one incoming reference,
// ref2 ends up small.
var ref1 []read.ObjId
var ref2 map[read.ObjId][]read.ObjId

func getReferrers(x read.ObjId) []string {
	return getNReferrers(x, 0, true)
}

const maxDepth = 0 // disabled

func getNReferrers(x read.ObjId, depth int, fulltext bool) []string {
	var r []string
	addr := d.Addr(x)
	end := addr + d.Size(x)
	refAddr := make([]uint64, 0, 16)
	if y := ref1[x]; y != read.ObjNil {
		for _, e := range d.Edges(y) {
			if e.To == x {
				refAddr = append(refAddr, d.Addr(y)+e.FromOffset)
				r = append(r, edgeSource(y, e))
				if depth < maxDepth {
					for _, ref := range getNReferrers(y, depth+1, false) {
						r = append(r, "-------&nbsp;"+ref)
					}
				}
			}
		}
		for _, y := range ref2[x] {
			for _, e := range d.Edges(y) {
				if e.To == x {
					refAddr = append(refAddr, d.Addr(y)+e.FromOffset)
					r = append(r, edgeSource(y, e))
					if depth < maxDepth {
						for _, ref := range getNReferrers(y, depth+1, false) {
							r = append(r, "-------&nbsp;"+ref)
						}
					}
				}
			}
		}
	}
	if fulltext {
		numObjects := d.NumObjects()
		for i := 0; i < numObjects; i++ {
			objId := read.ObjId(i)
			contents := d.Contents(objId)
		scanObjs:
			for a := uint64(0); a+d.PtrSize <= uint64(len(contents)); a += d.PtrSize {
				p := readPtr(contents[a:])
				if p >= addr && p < end {
					for _, ref := range refAddr {
						if ref == d.Addr(objId)+a {
							// Ignore objects in edges
							continue scanObjs
						}
					}
					r = append(r, objLink(objId)+
						fmt.Sprintf("+%x/%x -> %x+%x (fulltext objects)", a, d.Ft(objId).Size, addr, p-addr))
				}
			}
		}
	}
	for _, s := range []*read.Data{d.Data, d.Bss} {
		for _, e := range s.Edges {
			if e.To != x {
				continue
			}
			refAddr = append(refAddr, s.Addr+e.FromOffset)
			if e.FieldName != "" {
				r = append(r, "global "+e.FieldName)
			} else {
				r = append(r, nonheapAddr(s.Addr+e.FromOffset))
			}
		}
		if fulltext {
		scanSections:
			for a := uint64(0); a+d.PtrSize <= uint64(len(s.Data)); a += d.PtrSize {
				p := readPtr(s.Data[a:])
				if p >= addr && p < end {
					for _, ref := range refAddr {
						if ref == s.Addr+a {
							// Ignore objects in edges
							continue scanSections
						}
					}
					r = append(r, nonheapAddr(s.Addr+a)+fmt.Sprintf(" -> %x+%x (fulltext globals)", addr, p-addr))
				}
			}
		}
	}
	for _, f := range d.Frames {
		for _, e := range f.Edges {
			if e.To == x {
				refAddr = append(refAddr, f.Addr+e.FromOffset)
				r = append(r, fmt.Sprintf("<a href=frame?id=%x&depth=%d>%s</a>.%s", f.Addr, f.Depth, f.Name, e.FieldName))
			}
		}
		if fulltext {
		scanFrames:
			for a := uint64(0); a+d.PtrSize <= uint64(len(f.Data)); a += d.PtrSize {
				p := readPtr(f.Data[a:])
				if p >= addr && p < end {
					for _, ref := range refAddr {
						if ref == f.Addr+a {
							// Ignore objects in edges
							continue scanFrames
						}
					}
					r = append(r, fmt.Sprintf("<a href=frame?id=%x&depth=%d>%s+%x</a> -> %x+%x (fulltext frames)",
						f.Addr, f.Depth, f.Name, a, addr, p-addr))
				}
			}
		}
	}
	for _, s := range d.Otherroots {
		for _, e := range s.Edges {
			if e.To == x {
				r = append(r, s.Description)
			}
		}
	}
	for _, f := range d.Finalizers {
		if f.Obj >= addr && f.Obj < end {
			r = append(r, "Some finalizer")
		}
	}
	for _, f := range d.QFinal {
		if f.Obj >= addr && f.Obj < end {
			r = append(r, "Queued finalizer")
		}
	}
	for _, d := range d.Defers {
		if d.Argp >= addr && d.Argp < end {
			r = append(r, "Defer")
		}
	}
	return r
}

type bucket struct {
	bytes   uint64
	objects []read.ObjId
}

// histogram by full type id
var byType []bucket

func prepare() {
	// group objects by type
	fmt.Println("Grouping by type...")
	byType = make([]bucket, len(d.FTList))
	for i := 0; i < d.NumObjects(); i++ {
		x := read.ObjId(i)
		tid := d.Ft(x).Id
		b := byType[tid]
		b.bytes += d.Size(x)
		b.objects = append(b.objects, x)
		byType[tid] = b
	}

	// compute referrers
	fmt.Println("Computing referrers...")
	ref1 = make([]read.ObjId, d.NumObjects())
	for i := 0; i < d.NumObjects(); i++ {
		ref1[i] = read.ObjNil
	}
	ref2 = map[read.ObjId][]read.ObjId{}
	for i := 0; i < d.NumObjects(); i++ {
		x := read.ObjId(i)
		//fmt.Printf("object %d %x %d %s %s\n", i, d.Addr(x), d.Size(x), d.Ft(x).GCSig, d.Ft(x).Name)
		//printbytes(d.Contents(x))
		for _, e := range d.Edges(x) {
			r := ref1[e.To]
			if r == read.ObjNil {
				ref1[e.To] = x
			} else if x != r {
				s := ref2[e.To]
				if len(s) == 0 || x != s[len(s)-1] {
					ref2[e.To] = append(s, x)
				}
			}
		}
	}

	dom()
}

// map from object ID to the size of the heap that is dominated by that object.
var domsize []uint64

// immediate dominator, indexed by ObjId
var idom []read.ObjId

func dom() {
	fmt.Println("Computing dominators...")
	n := d.NumObjects()

	// make list of roots
	// TODO: have loader compute this?
	roots := map[read.ObjId]struct{}{}
	for _, s := range []*read.Data{d.Data, d.Bss} {
		for _, e := range s.Edges {
			roots[e.To] = struct{}{}
		}
	}
	for _, f := range d.Frames {
		for _, e := range f.Edges {
			roots[e.To] = struct{}{}
		}
	}
	for _, x := range d.Otherroots {
		for _, e := range x.Edges {
			roots[e.To] = struct{}{}
		}
	}

	// compute postorder traversal
	// object states:
	// 0 - not seen yet
	// 1 - seen, added to queue, not yet expanded children
	// 2 - seen, already expanded children
	// 3 - added to postorder
	postorder := make([]read.ObjId, 0, n)
	postnum := make([]int, n+1)
	state := make([]byte, n)
	var q []read.ObjId // stack of work to do, holds state 1 and 2 objects
	for x := range roots {
		if state[x] != 0 {
			if state[x] != 3 {
				log.Fatal("bad state found")
			}
			continue
		}
		state[x] = 1
		q = q[:0]
		q = append(q, x)
		for len(q) > 0 {
			y := q[len(q)-1]
			if state[y] == 2 {
				state[y] = 3
				q = q[:len(q)-1]
				postnum[y] = len(postorder)
				postorder = append(postorder, y)
			} else {
				if state[y] != 1 {
					log.Fatal("bad state")
				}
				state[y] = 2
				for _, e := range d.Edges(y) {
					z := e.To
					if state[z] == 0 {
						state[z] = 1
						q = append(q, z)
					}
				}
			}
		}
	}
	postnum[n] = n // virtual start node

	// compute immediate dominators
	// http://www.hipersoft.rice.edu/grads/publications/dom14.pdf
	idom = make([]read.ObjId, n+1)
	for i := 0; i < n; i++ {
		idom[i] = read.ObjNil
	}
	idom[n] = read.ObjId(n)
	for r := range roots {
		idom[r] = read.ObjId(n)
	}
	var redges []read.ObjId
	change := true
	for change {
		change = false
		for i := len(postorder) - 1; i >= 0; i-- {
			x := postorder[i]
			// get list of incoming edges
			redges = redges[:0]
			if ref1[x] != read.ObjNil {
				redges = append(redges, ref1[x])
				redges = append(redges, ref2[x]...)
			}
			a := read.ObjNil
			for _, b := range redges {
				if idom[b] == read.ObjNil {
					continue
				}
				if a == read.ObjNil {
					a = b
					continue
				}
				for a != b {
					if postnum[a] < postnum[b] {
						a = idom[a]
					} else {
						b = idom[b]
					}
				}
			}
			if _, ok := roots[x]; ok {
				a = read.ObjId(n)
			}
			if a != idom[x] {
				idom[x] = a
				change = true
			}
		}
	}

	domsize = make([]uint64, n+1)
	for _, x := range postorder {
		domsize[x] += d.Size(x)
		domsize[idom[x]] += domsize[x]
	}
	// Note: unreachable objects will have domsize of 0.
}

func readPtr(b []byte) uint64 {
	switch d.PtrSize {
	case 4:
		return uint64(d.Order.Uint32(b))
	case 8:
		return d.Order.Uint64(b)
	default:
		log.Fatal("unsupported PtrSize=%d", d.PtrSize)
		return 0
	}
}

func printbytes(b []byte) {
	for i := 0; i < len(b); i++ {
		fmt.Printf("%02x ", b[i])
		if i%16 == 15 {
			fmt.Println()
		}
	}
	if len(b)%16 != 0 {
		fmt.Println()
	}
}
