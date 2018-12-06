package icetTerm

import (
	"commentmap"
	"fmt"
	"strings"
)

const PROC_SIZE = 5
const STMT_SIZE = 0
const SKIP = "skip"
const ANNOT_SIZE = 5

type IDType int

type AnnotatationType int

const ( // annotation types
	Inv    AnnotatationType = iota
	Prop                    // property
	Pre                     // precondition
	Assume                  // assumtpion
	Declare
	Grouping
	None
)

const (
	Pid IDType = iota
	Variable
)

type IcetTerm interface {
	PrintIceT(int) string
	Remainder() IcetTerm
	Minimize() IcetTerm
}

// Programs
type Program struct {
	procs []IcetTerm
}

type Process struct {
	stmts []IcetTerm
}

type Declarations struct {
	Decls []string
}

type Assign struct {
	ProcID string
	Var    string
	Key    string
	Value  string
	IsMap  bool
}

type Send struct {
	ProcID        string
	RecipientID   string
	Value         string
	RecipientType IDType
}

type Recv struct {
	ProcID     string
	Variable   string
	FromId     string
	Decls      Declarations
	IsRecvFrom bool
}

type ForLoop struct {
	ProcID    string
	LoopVar   string
	Set       string
	Invariant string
	Stmts     Process
}

type RepeatLoop struct {
	ProcID string
	Stmts  Process
}

type SymSet struct {
	ProcVar string
	Name    string
	Stmts   Process
}

type Conditional struct {
	ProcID string
	Cond   string
	Left   Process
	Right  Process
}

type Group struct {
	Proc Process
}

type Annotation struct {
	Annot  string
	Type   AnnotatationType
	ProcID string
	Pos    commentmap.RelPos
}

type AnnotationSet struct {
	Annots []Annotation
}

func indentationAtLv(lv int) string {
	ident := ""
	for i := 0; i < lv; i++ {
		ident = fmt.Sprintf("\t%v", ident)
	}
	return ident
}

func IsSkip(t IcetTerm) bool {
	proc, ok := t.(*Process)
	if ok && len(proc.stmts) == 0 {
		return true
	}
	return false
}

// Declarations

func (c *Conditional) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	return fmt.Sprintf("%vite(%v,%v,\n%v,\n%v)", ident, c.ProcID, c.Cond, c.Left.PrintIceT(lv+1), c.Right.PrintIceT(lv+1))
}

func (c *Conditional) Remainder() IcetTerm {
	lr := c.Left.Remainder().(*Process)
	rr := c.Right.Remainder().(*Process)
	return &Conditional{ProcID: c.ProcID, Cond: c.Cond, Left: *lr, Right: *rr}
}

func (c *Conditional) Minimize() IcetTerm {
	lm := c.Left.Minimize().(*Process)
	rm := c.Right.Minimize().(*Process)
	if IsSkip(lm) && IsSkip(rm) {
		return NewProcess()
	}
	return &Conditional{ProcID: c.ProcID, Cond: c.Cond, Left: *lm, Right: *rm}
}

func MapToIcetTerm(vs []IcetTerm, lv int) []string {
	vsm := make([]string, len(vs))
	for i, v := range vs {
		vsm[i] = v.PrintIceT(lv)
	}
	return vsm
}

func joinWithIndent(strings []string, sep string, lv int) string {
	var ret string
	ident := indentationAtLv(lv)
	switch len(strings) {
	case 0:
		return ""
	case 1:
		return fmt.Sprintf("%v%v", ident, strings[0])
	}
	ret = ""
	for _, s := range strings[0 : len(strings)-1] {
		ret = fmt.Sprintf("%v%v%v%v", ret, ident, s, sep)
	}
	return fmt.Sprintf("%v%v%v", ret, ident, strings[len(strings)-1])
}

func (d *Declarations) PrintIceT(lv int) string {
	return fmt.Sprintf("[%v]", joinWithIndent(d.Decls, ",\n", lv))
}

func (d *Declarations) Remainder() IcetTerm {
	return NewProcess()
}

func (d *Declarations) Minimize() IcetTerm {
	return d
}

func NewDeclarations() Declarations {
	return Declarations{make([]string, 0)}
}

func (d *Declarations) AppendDecl(decl string) {
	d.Decls = append(d.Decls, decl)
}

func (d *Declarations) Append(d1 *Declarations) {
	d.Decls = append(d.Decls, d1.Decls...)
}

// Assign statements

func (a *Assign) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	if a.IsMap {
		return fmt.Sprintf("%vassign(%v,%v,upd(ref(%v,%v),ref(%v,%v),%v))", ident, a.ProcID, a.Var, a.Var, a.ProcID, a.Key, a.ProcID, a.Value)
	}
	return fmt.Sprintf("%vassign(%v,%v,%v)", ident, a.ProcID, a.Var, a.Value)
}

func (a *Assign) Remainder() IcetTerm {
	return NewProcess()
}

func (a *Assign) Minimize() IcetTerm {
	return a
}

// Send statements

func (s *Send) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	if s.RecipientType == Pid {
		return fmt.Sprintf("%vsend(%v, e_pid(%v), %v)", ident, s.ProcID, s.RecipientID, s.Value)
	}
	return fmt.Sprintf("%vsend(%v, e_var(%v), %v)", ident, s.ProcID, s.RecipientID, s.Value)
}

func (s *Send) Remainder() IcetTerm {
	return NewProcess()
}

func (s *Send) Minimize() IcetTerm {
	return s
}

// Receive statements

func (r *Recv) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	if r.IsRecvFrom {
		return fmt.Sprintf("%vrecv(%v, e_pid(%v), %v)", ident, r.ProcID, r.FromId, r.Variable)
	}
	return fmt.Sprintf("%vrecv(%v, %v)", ident, r.ProcID, r.Variable)
}

func (r *Recv) Remainder() IcetTerm {
	return NewProcess()
}

func (r *Recv) Minimize() IcetTerm {
	return r
}

// For Loops

func (l *ForLoop) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	if l.Invariant == "" {
		return fmt.Sprintf("%vfor(%v, %v, %v,\n %v)", ident, l.ProcID, l.LoopVar, l.Set, l.Stmts.PrintIceT(lv+1))
	}
	return fmt.Sprintf("%vfor(%v, %v, %v, rr, %v,\n %v)", ident, l.ProcID, l.LoopVar, l.Set, l.Invariant, l.Stmts.PrintIceT(lv+1))
}

func (l *ForLoop) Remainder() IcetTerm {
	return NewProcess()
}

func (l *ForLoop) Minimize() IcetTerm {
	minStmts := l.Stmts.Minimize().(*Process)
	if IsSkip(minStmts) {
		return NewProcess()
	}
	return &ForLoop{ProcID: l.ProcID, LoopVar: l.LoopVar, Set: l.Set, Invariant: l.Invariant, Stmts: *minStmts}
}

// Repeat Loops

func (l *RepeatLoop) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	return fmt.Sprintf("%vwhile(%v, true,\n %v)\n", ident, l.ProcID, l.Stmts.PrintIceT(lv+1))
}

func (l *RepeatLoop) Remainder() IcetTerm {
	return l
}

func (l *RepeatLoop) Minimize() IcetTerm {
	minStms := l.Stmts.Minimize().(*Process)
	if IsSkip(minStms) {
		return NewProcess()
	}
	return &RepeatLoop{ProcID: l.ProcID, Stmts: *minStms}
}

// Sets
func (s *SymSet) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	return fmt.Sprintf("%vsym(%v, %v,\n%v)", ident, s.ProcVar, s.Name, s.Stmts.PrintIceT(lv+1))
}

func (s *SymSet) Remainder() IcetTerm {
	sr := s.Stmts.Remainder().(*Process)
	return &SymSet{ProcVar: s.ProcVar, Name: s.Name, Stmts: *sr}
}
func (s *SymSet) Minimize() IcetTerm {
	sm := s.Stmts.Minimize().(*Process)
	if IsSkip(sm) {
		return NewProcess()
	}
	return &SymSet{ProcVar: s.ProcVar, Name: s.Name, Stmts: *sm}
}

// Programs
func NewProgram() *Program {
	return &Program{make([]IcetTerm, 0, PROC_SIZE)}
}

func (p *Program) AddProc(proc IcetTerm) {
	p.procs = append(p.procs, proc)
}

func (p *Program) RemoveLastProc() (IcetTerm, bool) {
	if len(p.procs) > 0 {
		proc := p.procs[len(p.procs)-1]
		p.procs = p.procs[:len(p.procs)-1]
		return proc, true
	}
	return NewProcess(), false
}

func (p *Program) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	switch len(p.procs) {
	case 0:
		return fmt.Sprintf("%v%v", ident, SKIP)
	case 1:
		return fmt.Sprintf("%v%v", ident, p.procs[0].PrintIceT(0))
	}
	strs := MapToIcetTerm(p.procs, lv+1)
	procs := joinWithIndent(strs, ",\n", 0)
	return fmt.Sprintf("%vpar([\n%v])", ident, procs)
}

func (p *Program) Remainder() IcetTerm {
	remProcs := make([]IcetTerm, len(p.procs))
	for i, proc := range p.procs {
		remProcs[i] = proc.Remainder()
	}
	return &Program{remProcs}
}

func (p *Program) Minimize() IcetTerm {
	minProcs := make([]IcetTerm, 0)
	for _, proc := range p.procs {
		min := proc.Minimize()
		if !IsSkip(min) {
			minProcs = append(minProcs, min)
		}
	}
	return &Program{minProcs}
}

// Processes
func NewProcess() *Process {
	return &Process{make([]IcetTerm, 0, STMT_SIZE)}
}

func (proc *Process) Len() int {
	return len(proc.stmts)
}

func (proc *Process) IsEmpty() bool {
	return len(proc.stmts) == 0
}

func (proc *Process) AddStmt(stmt IcetTerm) {
	if !IsSkip(stmt.Minimize()) {
		proc.stmts = append(proc.stmts, stmt)
	}

}

func (proc *Process) AddStmts(stmts []IcetTerm) {
	for _, stmt := range stmts {
		proc.AddStmt(stmt)
	}
}

func (proc *Process) AddProc(proc1 *Process) {
	proc.stmts = append(proc.stmts, proc1.stmts...)
}

func (proc *Process) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	switch len(proc.stmts) {
	case 0:
		return fmt.Sprintf("%v%v", ident, SKIP)
	case 1:
		return fmt.Sprintf("%v%v", ident, proc.stmts[0].PrintIceT(0))
	}
	strs := MapToIcetTerm(proc.stmts, lv+1)
	procs := joinWithIndent(strs, ",\n", 0)
	return fmt.Sprintf("%vseq([\n%v\n%v])", ident, procs, ident)
}

func (proc *Process) Remainder() IcetTerm {
	remStmts := make([]IcetTerm, len(proc.stmts))
	for i, stmt := range proc.stmts {
		remStmts[i] = stmt.Remainder()
	}
	return &Process{remStmts}
}

func (proc *Process) Minimize() IcetTerm {
	minStmts := make([]IcetTerm, 0)
	for _, stmt := range proc.stmts {
		min := stmt.Minimize()
		if !IsSkip(min) {
			minStmts = append(minStmts, min)
		}
	}
	return &Process{minStmts}
}

// Annotations

func (a *Annotation) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	switch a.Type {
	case Pre:
		return fmt.Sprintf("%vpre(%v, %v)", ident, a.ProcID, a.Annot)
	case Assume:
		return fmt.Sprintf("%vassume(%v, %v)", ident, a.ProcID, a.Annot)
	case Prop:
		return fmt.Sprintf("%v%v", ident, a.Annot)
	case Inv:
		return fmt.Sprintf("%v%v", ident, a.Annot)
	}
	return ""
}

func (g *Group) PrintIceT(lv int) string {
	if g.Proc.Len() > 0 {
		ident := indentationAtLv(lv)
		return fmt.Sprintf("%vgroup(skip, \n%v)", ident, g.Proc.PrintIceT(lv+1))
	}
	return ""
}

func (g *Group) Remainder() IcetTerm {
	rem := g.Proc.Remainder().(*Process)
	return &Group{*rem}
}

func (g *Group) Minimize() IcetTerm {
	if IsSkip(&g.Proc) {
		return NewProcess()
	}
	min := g.Proc.Minimize().(*Process)
	return &Group{*min}
}

func (a *Annotation) Remainder() IcetTerm {
	return NewProcess()
}

func (a *Annotation) Minimize() IcetTerm {
	if a.Annot == "" {
		return NewProcess()
	}
	return a
}

func (a *Annotation) IsGroupStart() bool {
	return (strings.TrimSpace(a.Annot) == "start")
}

func (a *Annotation) IsGroupEnd() bool {
	return (strings.TrimSpace(a.Annot) == "end")
}

func (a *AnnotationSet) Split() (*AnnotationSet, *AnnotationSet) {
	pre := NewAnnotationSet()
	post := NewAnnotationSet()
	for _, annot := range a.Annots {
		switch annot.Pos {
		case commentmap.Before:
			pre.Add(annot)
		case commentmap.After:
			post.Add(annot)
		}
	}
	return pre, post
}

func (as *AnnotationSet) PrintIceT(lv int) string {
	if len(as.Annots) > 0 {
		ident := indentationAtLv(lv)
		var s []string
		for _, a := range as.Annots {
			s = append(s, a.PrintIceT(lv))
		}
		return fmt.Sprintf("%v%v", ident, strings.Join(s, ","))
	}
	return ""
}

func (a *AnnotationSet) Remainder() IcetTerm {
	return NewProcess()
}

func (a *AnnotationSet) Minimize() IcetTerm {
	if len(a.Annots) == 0 {
		return NewProcess()
	}
	return a
}

func NewAnnotationSet() *AnnotationSet {
	return &AnnotationSet{Annots: make([]Annotation, 0)}
}

func (as *AnnotationSet) Add(a ...Annotation) {
	as.Annots = append(as.Annots, a...)
}
