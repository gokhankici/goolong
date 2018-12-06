package main

import (
	"flag"
	"fmt"
	"gochai"
)

var term = flag.Int("term", 0, "Current term")
var myID = flag.Int("id", 0, "Replica id")
var myAddr = flag.String("addr", ":7070", "Server address (this machine). Defaults to localhost.")

func main() {
	flag.Parse()
	peerAddresses := flag.Args()
	doneFollower := make(chan bool, 1)
	doneCandidate := make(chan bool, 1)
	go runFollower(peerAddresses, doneFollower)
	go runCandidate(peerAddresses, term, doneCandidate)
	// wait for follower and candidate to finish
	<-doneFollower
	<-doneCandidate
}

func runFollower(peerAddresses []string, done chan bool) {
	n := gochai.CreateNewNode("f", *myID, *myAddr, peerAddresses, false)
	n.Start()
	n.StartSymSet("fs", "f")
	n.AssignSymSet("cs", "")
	// Initializations
	myTerm := gochai.NewVar()
	voted := gochai.NewVar()
	votedFor := gochai.NewVar()
	myVote := gochai.NewVar()
	votes := gochai.NewMap()
	myTerm.Assign(-1)
	voted.Assign(0)
	// -- begin protocol
	for _ = range n.PeerIds {
		myVote.Assign(0)
		resID, t := n.RecvPair()
		// proceed if the request is not outdated
		if t.Get() > myTerm.Get() {
			myTerm.Assign(t.Get())
			voted.Assign(0)
			votedFor.Assign(0)
		}
		if t.Get() >= myTerm.Get() && (voted.Get() == 0 || votedFor.Get() == resID.Get()) {
			voted.Assign(1)
			votedFor.Assign(resID.Get())
			votes.Put(myTerm.Get(), resID.Get())
			myVote.Assign(1)
		}

		n.Send(int(resID.Get()), myVote)
	}
	n.Shutdown()
	done <- true
	//--end
}

func runCandidate(peerAddresses []string, termArg *int, done chan bool) {
	n := gochai.CreateNewNode("c", *myID, *myAddr, peerAddresses, true)
	n.Start()

	// -- Assigning sets --
	// part of symmetric set "cs"
	n.StartSymSet("cs", "c")
	// communicates with set "fs"
	n.AssignSymSet("fs", "")

	// Declaring protocol state
	term := gochai.NewVar()
	id := gochai.NewVar()
	vote := gochai.NewVar()
	count := gochai.NewVar()
	isLeader := gochai.NewVar()

	// -- ghost variables used to access follower statements
	votedFor := gochai.NewGhostVar()
	myTerm := gochai.NewGhostVar()

	// cardinalities
	k := gochai.NewVar() // k=#{f | f.term < c.term}
	l := gochai.NewVar() // l=#{f | f.term ≥ c.term ∧ f.votes [c.term] = c}
	// =====================
	//    Initialization
	// =====================

	/*{-@ pre: and([
				ref(k,C) = card(fs),
				ref(l,C) = 0,
				ref(count,C) = 0,
				ref(isLeader, C) = 0])
	-@}*/

	/*{-@ assume:
		forall([decl(i,int)],
				and([
					ref(k,i) = card(fs),
					ref(l,i) = 0
					])
					)
	-@}*/
	isLeader.Assign(0)
	count.Assign(0)
	term.Assign(int32(*termArg))

	// =====================
	//    Sending Proposals
	// =====================
	for Peer := range n.PeerIds {
		// send proposal to follower

		/*{-@ pre:
				forall([decl(i,int)],
					implies(
						elem(i,cs),
						and([
							ref(k,i)+ref(l,i) =< card(fs),
							ref(count,i)=ref(l,i)
							])
					 )
			  )
		-@}*/
		id.Assign(n.MyId())
		n.SendPair(Peer, id, term)
		vote = n.RecvFrom(Peer)
		if vote.Get() == 1 {
			count.Assign(count.Get() + 1)
		}
		// Updating ghost variables; these have no runtime behavior
		if vote.Get() == 1 && votedFor.Get() == n.MyId() && term.Get() == myTerm.Get() {
			l.Assign(l.Get() + 1)
			k.Assign(k.Get() - 1)
		}
	}

	// =====================
	//    Counting replies
	// =====================

	/*{-@ pre:
			forall([decl(i,int)],
				implies(
					and([
						elem(i,cs),
						ref(isLeader,i)=1
						]),
						card(fs)<ref(count,i)*2)
				)
	-@}*/

	// {-@ declare: decl(f0, int) -@}

	// {-@ assume: elem(f0,fs) -@}

	/*{-@ assume:
			forall([decl(i,int), decl(j,int)],
		 		implies(
					and([
						elem(i,cs),
						elem(j,cs),
						ref(l,i) > card(fs)/2,
						ref(l,j) > card(fs)/2
						]),
				and([
					ref(ref(votes,f0),
					ref(term,i))=i,
					ref(ref(votes,f0),
					ref(term,j))=j
		 			])
		 	 )
	 )
	-@}*/

	/*{-@ pre: forall([decl(i,int), decl(j,int)],
								implies(
										and([
											elem(i,cs),
											elem(j,cs),
											ref(count,i) > card(fs)/2,
											ref(count,j) > card(fs)/2,
											ref(term,i)=ref(term,j),
											ref(isLeader,j)=1,
											ref(isLeader,i)=1
											]),
										i=j
									)
					 )
	-@}*/
	if 2*int(count.Get()) > n.NumPeers() {
		isLeader.Assign(1)
	}

	if isLeader.Get() == 1 {
		fmt.Printf("I'm the leader for term %v!!", term.Get())
	} else {
		fmt.Printf("Not the leader in term %v.", term.Get())
	}
	// --end
	n.Shutdown()
	done <- true
}

/*{-@ ensures: forall([decl(i,int), decl(j,int)],
			implies(
					and([
						elem(i,cs),
						elem(j,cs),
						ref(term,i)=ref(term,j),
						ref(isLeader,j)=1,
						ref(isLeader,i)=1
						]),
					i=j
				)
		)
-@}*/
