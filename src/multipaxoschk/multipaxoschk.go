package main

import (
	"flag"
	"fmt"
	"go/ast"
	"icet"
	"icetTerm"
	"log"
	"paxosproto"
)

// Parses paxos specific sends and receive methods
type PaxosParser struct{}

func (p *PaxosParser) ParseSend(name string, args []ast.Expr, procID string, idType icetTerm.IDType, getValue func(ast.Node) string) (bool, *icetTerm.Send) {
	//n.SendAcceptorReply(int(resID.Get()), wT, w, success)
	if name == "SendAcceptorReply" {
		id := getValue(args[0])
		wt := getValue(args[1])
		w := getValue(args[2])
		success := getValue(args[3])
		val := fmt.Sprintf("pair(%v,pair(%v,%v))", wt, w, success)
		return true, &icetTerm.Send{ProcID: procID, RecipientID: id, RecipientType: idType, Value: val}
	}
	//n.SendPrepare(Peer, id, myTerm)
	if name == "SendPrepare" {
		peerID := getValue(args[0])
		myID := getValue(args[1])
		myTerm := getValue(args[2])
		myInst := getValue(args[3])
		val := fmt.Sprintf("pair(%v,pair(%v,pair(%v,pair(%v, 0))))", paxosproto.PrepareType, myID, myInst, myTerm)
		return true, &icetTerm.Send{ProcID: procID, RecipientID: peerID, RecipientType: idType, Value: val}
	}
	//n.SendAccept(Peer, id, myTerm, x)
	if name == "SendAccept" {
		peerID := getValue(args[0])
		myID := getValue(args[1])
		myTerm := getValue(args[2])
		x := getValue(args[3])
		myInst := getValue(args[4])
		val := fmt.Sprintf("pair(%v,pair(%v,pair(%v,pair(%v,%v))))", paxosproto.AcceptType, myID, myInst, myTerm, x)
		return true, &icetTerm.Send{ProcID: procID, RecipientID: peerID, RecipientType: idType, Value: val}
	}
	return false, nil
}

//string, []ast.Expr, string, string, bool, func(ast.Node) string
func (p *PaxosParser) ParseReceive(name string, args []ast.Expr, fromID string, procID string, IntType string, getValue func(ast.Node) string) (bool, *icetTerm.Recv) {
	//rwT, rw, rsuccess := n.RecvAcceptorReplyFrom(Peer)
	if name == "RecvAcceptorReplyFrom" {
		rwT := getValue(args[0])
		rw := getValue(args[1])
		rsuccess := getValue(args[2])
		val := fmt.Sprintf("pair(%v,pair(%v,%v))", rwT, rw, rsuccess)
		decls := icetTerm.NewDeclarations()
		decls.AppendDecl(fmt.Sprintf("decl(%v,%v)", rwT, IntType))
		decls.AppendDecl(fmt.Sprintf("decl(%v,%v)", rw, IntType))
		decls.AppendDecl(fmt.Sprintf("decl(%v,%v)", rsuccess, IntType))
		return true, &icetTerm.Recv{ProcID: procID, Variable: val, FromId: fromID, IsRecvFrom: true, Decls: decls}
	}
	// msgType, resID, t, x := n.AcceptorReceive()
	if name == "AcceptorReceive" {
		msgType := getValue(args[0])
		resID := getValue(args[1])
		pInst := getValue(args[2])
		t := getValue(args[3])
		x := getValue(args[4])
		val := fmt.Sprintf("pair(%v,pair(%v,pair(%v,pair(%v,%v))))", msgType, resID, pInst, t, x)
		decls := icetTerm.NewDeclarations()
		decls.AppendDecl(fmt.Sprintf("decl(%v,%v)", msgType, IntType))
		decls.AppendDecl(fmt.Sprintf("decl(%v,%v)", resID, IntType))
		decls.AppendDecl(fmt.Sprintf("decl(%v,%v)", pInst, IntType))
		decls.AppendDecl(fmt.Sprintf("decl(%v,%v)", t, IntType))
		decls.AppendDecl(fmt.Sprintf("decl(%v,%v)", x, IntType))
		return true, &icetTerm.Recv{ProcID: procID, Variable: val, FromId: fromID, IsRecvFrom: false, Decls: decls}
	}
	return false, nil
}

func main() {
	// parsing file
	flag.Parse()
	if flag.NArg() != 1 {
		log.Fatal("usage: icet <go file>")
	}
	file := flag.Args()[0]
	v := icet.MakeNewIceTVisitor()
	v.Parser = &PaxosParser{}
	term := v.ExtractIcetTerm(file)
	fmt.Printf("%v.", term)
}
