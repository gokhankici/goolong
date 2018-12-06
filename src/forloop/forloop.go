package main

import (
	"flag"
	"fmt"
	"gochai"
)

var isServer = flag.Bool("server", true, "Act as server (true) or client (false). ")
var myID = flag.Int("id", 0, "Replica id")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	if *isServer {
		runServerProtocol(peerAddresses)
	} else {
		runClientProtocol(peerAddresses)
	}
}

func runServerProtocol(peerAddresses []string) {
	n := gochai.CreateNewNode("m", 0, *myAddr, peerAddresses, false)
	n.AssignSymSet("clients", "")
	fmt.Println("Acting as server.")
	//Protocol--
	for ID := range n.PeerIds {
		// {-@ invariant: forall([decl(id,int)], implies(elem(id,rr), ref(msg, id)=42)) -@}
		val := gochai.NewVar()
		fmt.Printf("sending 42 to %v\n", ID)
		val.Assign(42)
		n.Send(ID, val)
	}
	n.Shutdown()
	//--end
}

func runClientProtocol(peerAddresses []string) {
	n := gochai.CreateNewNode("c", *myID, *myAddr, peerAddresses, true)
	fmt.Println("Acting as client.")
	msg := gochai.NewVar()
	// Protocol --
	n.StartSymSet("clients", "p")
	msg = n.Recv()
	fmt.Printf("Received Message: %v", msg.Get())
	// -- end
	n.Shutdown()
}

// {-@ ensures: forall([decl(p,int)], implies(elem(p, clients), ref(msg, p)=42)) -@}
