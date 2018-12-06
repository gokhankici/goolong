package gochai

import (
	"encoding/binary"
	"fastrpc"
	"fmt"
	"io"
	"node"
	"reflect"
)

type ChaiNode struct {
	*node.Node        // extends node
	Set        SymSet //node belongs to set Set
	intType    uint8
	intChans   []chan fastrpc.Serializable
	pairType   uint8
	pairChans  []chan fastrpc.Serializable
}

type SymSet struct {
	InSet bool
	Name  string
	Param string
}

// -- protocol state
type IntVar struct {
	thisVar int32
}

type UInt8 struct {
	thisVar uint8
}

type GhostVar struct {
}

type NoOpVar struct {
}

type IntPair struct {
	L *IntVar
	R *IntVar
}

func (v *IntVar) Assign(val int32) {
	v.thisVar = val
}

func (v *IntVar) Get() int32 {
	return v.thisVar
}

func NewUInt8() *UInt8 {
	return &UInt8{thisVar: 0}
}

func (v *UInt8) Assign(val uint8) {
	v.thisVar = val
}

func (v *UInt8) Get() uint8 {
	return v.thisVar
}

func NewUInt8_(v uint8) *UInt8 {
	return &UInt8{thisVar: v}
}

// -- get user input from stdin
func (v *IntVar) ReadIO() {
	fmt.Scanf("%v", &v.thisVar)
}

func (v *IntVar) Marshal(wire io.Writer) {
	var b [4]byte
	bs := b[:4]
	binary.LittleEndian.PutUint32(bs, uint32(v.Get()))
	wire.Write(bs)
}

func (v *IntVar) Unmarshal(wire io.Reader) error {
	var b [4]byte
	bs := b[:4]
	_, err := io.ReadAtLeast(wire, bs, 4)
	v.Assign(int32(binary.LittleEndian.Uint32(bs)))
	return err
}

func (v *IntVar) New() fastrpc.Serializable {
	return new(IntVar)
}

func NewVar() *IntVar {
	return &IntVar{thisVar: -1}
}

func NewIntVar_(v int32) *IntVar {
	return &IntVar{thisVar: v}
}

// ghost variables: refer to another processes state; not executed

func NewGhostVar() *GhostVar {
	return &GhostVar{}
}

func (v *GhostVar) Assign(val int32) { //have no runtime effect
}

func (v *GhostVar) Get() int32 {
	return 0
}

// no-op var: refer to own state; not exectuted

func NewNoOpVar() *NoOpVar {
	return &NoOpVar{}
}

func (v *NoOpVar) Assign(val int32) { //have no runtime effect
}

func (v *NoOpVar) Get() int32 {
	return 0
}

//-- Pairs
func makePair(l *IntVar, r *IntVar) *IntPair {
	return &IntPair{L: l, R: r}
}

func (p *IntPair) Unpack() (*IntVar, *IntVar) {
	return p.L, p.R
}

func (p *IntPair) Marshal(wire io.Writer) {
	var b [8]byte
	bs := b[:8]
	tmp32 := p.L.Get()
	bs[0] = byte(tmp32)
	bs[1] = byte(tmp32 >> 8)
	bs[2] = byte(tmp32 >> 16)
	bs[3] = byte(tmp32 >> 24)
	tmp32 = p.R.Get()
	bs[4] = byte(tmp32)
	bs[5] = byte(tmp32 >> 8)
	bs[6] = byte(tmp32 >> 16)
	bs[7] = byte(tmp32 >> 24)
	wire.Write(bs)
}

func (p *IntPair) Unmarshal(wire io.Reader) error {
	var tmp int32
	var b [8]byte
	bs := b[:8]
	_, err := io.ReadAtLeast(wire, bs, 8)
	tmp = int32((uint32(bs[0]) | (uint32(bs[1]) << 8) | (uint32(bs[2]) << 16) | (uint32(bs[3]) << 24)))
	p.L.Assign(tmp)
	tmp = int32((uint32(bs[4]) | (uint32(bs[5]) << 8) | (uint32(bs[6]) << 16) | (uint32(bs[7]) << 24)))
	p.R.Assign(tmp)
	return err
}

func (p *IntPair) New() fastrpc.Serializable {
	return &IntPair{NewVar(), NewVar()}
}

//---- Maps
type Map struct {
	thisMap map[int32]int32
}

func NewMap() Map {
	thisMap := make(map[int32]int32)
	return Map{thisMap: thisMap}
}

func (m *Map) Put(key int32, val int32) {
	m.thisMap[key] = val
}

func (m *Map) GetKey(key *IntVar) int32 {
	return m.thisMap[key.Get()]
}

func (m *Map) getType() string {
	return "map(int, int)"
}

// -- protocol communication

func CreateNewNode(name string, id int, myaddr string, peerAddrList []string, isServer bool) *ChaiNode {
	n := &ChaiNode{
		node.MakeNode(id, myaddr, peerAddrList, isServer),
		EmptySet(),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList))}

	n.intType = n.RegisterRPC(new(IntVar), n.intChans)
	n.pairType = n.RegisterRPC(new(IntPair), n.pairChans)
	for i := range n.intChans {
		n.intChans[i] = make(chan fastrpc.Serializable)
		n.pairChans[i] = make(chan fastrpc.Serializable)
	}

	return n
}

func (n *ChaiNode) Start() {
	n.Run()
	<-n.Connected
}

func (n *ChaiNode) Shutdown() {
	n.Done <- true
	n.Stop = true
}

func (n *ChaiNode) AssignSymSet(name string, param string) {
	n.Set = SymSet{InSet: false, Name: name, Param: param}
}

func (n *ChaiNode) StartSymSet(name string, param string) {
	n.Set = SymSet{InSet: true, Name: name, Param: param}
}

func EmptySet() SymSet {
	return SymSet{InSet: false, Name: "", Param: ""}
}

// Send sends msg to id
func (n *ChaiNode) Send(id int, msg fastrpc.Serializable) {
	var code uint8
	switch msg.(type) {
	case *IntVar:
		code = n.intType
	case *IntPair:
		code = n.pairType
	}
	n.NSend(id, code, msg)
}

// receive from any peer
func (n *ChaiNode) RecvAll(chans []chan fastrpc.Serializable) fastrpc.Serializable {
	cases := make([]reflect.SelectCase, len(chans))
	for i, ch := range chans {
		cases[i] = reflect.SelectCase{Dir: reflect.SelectRecv, Chan: reflect.ValueOf(ch)}
	}
	_, msg, _ := reflect.Select(cases)
	return msg.Interface().(fastrpc.Serializable)
}

func (n *ChaiNode) Recv() *IntVar {
	msg := n.RecvAll(n.intChans)
	return msg.(*IntVar)
}

func (n *ChaiNode) SendPair(id int, l *IntVar, r *IntVar) {
	pair := makePair(l, r)
	n.Send(id, pair)
}

func (n *ChaiNode) RecvPair() (*IntVar, *IntVar) {
	msg := n.RecvAll(n.pairChans)
	return msg.(*IntPair).Unpack()
}

// Receive from a given id
func (n *ChaiNode) RecvFromGen(id int, chans []chan fastrpc.Serializable) fastrpc.Serializable {
	msg := <-chans[id]
	return msg
}

func (n *ChaiNode) RecvFrom(id int) *IntVar {
	msg := n.RecvFromGen(id, n.intChans)
	return msg.(*IntVar)
}

func (n *ChaiNode) RecvPairFrom(id int) (*IntVar, *IntVar) {
	msg := n.RecvFromGen(id, n.pairChans)
	return msg.(*IntPair).Unpack()
}
