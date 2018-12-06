package main

import (
	"flag"
	"fmt"
	"gochai"
)

const coordID = 0 // coordinator ID

var isServer = flag.Bool("coord", true, "Act as coordinator (true) or db-node (false). ")
var myID = flag.Int("id", coordID, "Replica id")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	if *isServer {
		runCoordinatorProtocol(peerAddresses)
	} else {
		runServerProtocol(peerAddresses)
	}
}

func runCoordinatorProtocol(peerAddresses []string) {
	c := coordID
	n := gochai.CreateNewNode("c", c, *myAddr, peerAddresses, false)
	fmt.Println("Acting as coordinator.")
	n.AssignSymSet("dbs", "")
	n.Start()
	// Declaring protocol state
	proposal := gochai.NewVar()
	vote := gochai.NewVar()
	reply := gochai.NewVar()
	abort := gochai.NewVar()
	committed := gochai.NewVar()
	ack := gochai.NewVar()
	// Initializations
	committed.Assign(0)
	abort.Assign(0)
	fmt.Println("Please enter your proposal number")
	proposal.ReadIO()

	/*{-@ invariant:
			forall([decl(i,int)],
							implies(
									and([elem(i,rr)]),
									and([
										ref(value,i)=0,
										ref(val,i)=proposal
										])
							)
					)
	-@}*/
	for ID := range n.PeerIds {
		fmt.Printf("Sending proposal to %v\n", ID)
		n.Send(ID, proposal)
		vote = n.RecvFrom(ID)
		fmt.Printf("Received %v\n", vote.Get())
		if vote.Get() == 0 {
			abort.Assign(1)
			fmt.Printf("abording proposal %v\n", proposal.Get())
		}
	}
	// -- Second phase --
	if abort.Get() == 0 {
		reply.Assign(1)
		committed.Assign(1)
	} else {
		reply.Assign(0)
	}

	/*{-@ invariant: forall([decl(i,int)],
						and([
								implies(
									and([elem(i,rr), committed=1]),
									ref(value,i)=ref(val,i)
								),
								implies(
									and([elem(i,dbs), committed=0]),
									ref(value,i)=0)
					 			])
		 				)
	-@}*/
	for ID := range n.PeerIds {
		n.Send(ID, reply)
		ack = n.RecvFrom(ID)
	}
	fmt.Printf("Decision for proposal %v is %v and ack %v\n", proposal.Get(), committed.Get(), ack)
	n.Shutdown()
	//--end
}

func runServerProtocol(peerAddresses []string) {
	n := gochai.CreateNewNode("db", *myID, *myAddr, peerAddresses, true)
	c := coordID
	n.Start()
	n.StartSymSet("dbs", "dbs")
	fmt.Println("Acting as db server.")
	val := gochai.NewVar()
	value := gochai.NewVar()
	decision := gochai.NewVar()
	ackMsg := gochai.NewVar()
	myVote := gochai.NewVar()
	value.Assign(0)
	n.StartSymSet("dbs", "p")
	// First phase --
	val = n.RecvFrom(c)
	fmt.Printf("Received proposal value %v.\n Enter 1 to accept and 0 to refuse.\n", val.Get())
	myVote.ReadIO()
	fmt.Printf("decision is: %v\n", myVote.Get())
	n.Send(c, myVote)
	// -- Sendond phase --
	decision = n.RecvFrom(c)
	if decision.Get() == 1 {
		value.Assign(val.Get())
	}
	ackMsg.Assign(1)
	n.Send(c, ackMsg)
	fmt.Printf("Decision for proposal %v is %v; permanent value is %v", val.Get(), decision.Get(), value.Get())
	n.Shutdown()
	// --end
}

// {-@ ensures: and([forall([decl(i,int)], implies(and([elem(i,dbs), committed=1]), ref(value,i)=proposal)), forall([decl(i,int)], implies(and([elem(i,dbs), committed=0]), ref(value,i)=0))]) -@}
