module PaxosSingle {

  function domain<U,V>(m: map<U,V>) : set<U>
	  ensures domain(m) == set u : U | u in m :: u;
	  ensures forall u :: u in domain(m) ==> u in m;
  {
		  set u : U | u in m :: u
  }

  function method len(s: set<nat>) : (l: nat)
    ensures l == |s|
  {
    |s|
  }

  datatype Loc = P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8

  datatype Msg_Acc =                                                                                                     // code
      Prepare(no: int)                                                                                                   // code
    | Accept(no: int, val: int)                                                                                          // code

  datatype Msg_Phase =                                                                                                   // code
      OneB                                                                                                               // code
    | TwoB                                                                                                               // code

  datatype Msg_Prop = Value(max_seen_n: int, max_accepted_n: int, max_val: int, phase: Msg_Phase)                        // code

  method {:timeLimit 0} PaxosSingle                                                                                      // code
    ( Ps : set<nat>                                                                                                      // code
    , As : set<nat>                                                                                                      // code
    )
    requires |Ps| > 0                                                                                                    // inv
    requires |As| >= 2                                                                                                   // inv
    requires Ps !! As                                                                                                    // inv
    decreases *
  {
    // #########################################################################
    // Proposer local state
    // #########################################################################

    // proposed value of the proposer
    var Prop_V : map<nat, int> := *;                                                                                     // code
    assume domain(Prop_V) == Ps;                                                                                         // inv

    // proposal number of the proposal
    var Prop_N : map<nat, nat> := *;                                                                                     // code
    assume domain(Prop_N) == Ps;                                                                                         // inv
    assume forall p :: p in Ps ==> Prop_N[p] > 0;                                                                        // inv
    assume forall p1,p2 :: p1 in Ps && p2 in Ps ==> (p1 == p2 <==> Prop_N[p1] == Prop_N[p2]);                            // inv

    // max seen proposal number
    var Prop_Max : map<nat, int> := map p | p in Ps :: (-1);                                                             // code

    // proposer's program counter
    var Prop_PC  : map<nat, Loc>  := map p | p in Ps :: P0;                                                              // harness

    // heard of count
    var Prop_HO       : map<nat, nat>  := map p | p in Ps :: 0;                                                          // code
    var Prop_HO2      : map<nat, nat>  := map p | p in Ps :: 0;                                                          // code

    // is proposer in the second phase ?
    var Prop_Ready    : map<nat, bool> := map p | p in Ps :: false;                                                      // code

    var Prop_Decided  : map<nat, bool> := map p | p in Ps :: false;                                                      // code

    var Prop_Exec_P5 : map<nat, bool> := map p | p in Ps :: false;                                                       // annot
    var Prop_Exec_P6 : map<nat, bool> := map p | p in Ps :: false;                                                       // annot

    var Prop_a   : map<nat, nat> := *;                                                                                   // harness
    assume domain(Prop_a) == Ps;                                                                                         // inv
    assume forall p,a :: p in Ps && a == Prop_a[p] ==> a in As;                                                          // inv

    var Prop_WL  : map<nat, set<nat>> := map p | p in Ps :: As;                                                          // harness
    var Prop_WL2 : map<nat, set<nat>> := map p | p in Ps :: As;                                                          // harness

    // #########################################################################
    // Acceptor State
    // #########################################################################

    // value of the highest numbered proposal accepted by the acceptor
    var Acc_MaxV : map<nat, int> := *;                                                                                   // code
    assume domain(Acc_MaxV) == As;                                                                                       // inv

    // highest accepted proposal's number
    var Acc_Max_Accepted_N : map<nat, int> := map a | a in As :: (-1);                                                   // code

    // max proposal number seen
    var Acc_Max_Seen_N : map<nat, int> := map a | a in As :: (-1);                                                       // code

    // all accepted proposal numbers
    var Acc_Ns  : map<nat, set<int>> := map a | a in As :: {};                                                           // annot

    // acceptor's program counter
    var Acc_PC  : map<nat, Loc> := map a | a in As :: P0;                                                                // harness

    // #########################################################################
    // Message soups
    // #########################################################################

    var Acc_Soup  : map<nat, multiset<(nat,Msg_Acc)>>  := map a | a in As :: multiset{};                                 // harness
    var Prop_Soup : map<nat, multiset<(nat,Msg_Prop)>> := map p | p in Ps :: multiset{};                                 // harness

    var Acc_Soup_Hist  : map<nat, set<(nat,Msg_Acc)>>  := map a | a in As :: {};                                         // annot
    var Prop_Soup_Hist : map<nat, set<(nat,Msg_Prop)>> := map p | p in Ps :: {};                                         // annot

    // #########################################################################
    // Message histories
    // #########################################################################

    var OneA_Hist : set<nat>                     := {};                                                                  // annot
    var OneB_Hist : map<nat, set<(int,int,int)>> := map a | a in As :: {};                                               // annot
    var TwoA_Hist : set<(int,int)>               := {};                                                                  // annot
    var TwoB_Hist : map<nat, set<(int,int)>>     := map a | a in As :: {};                                               // annot

    // #########################################################################
    // Other history variables
    // #########################################################################

    // (a,n) in Joined_Rnd ==> a has seen a proposal msg numbered n
    var Joined_Rnd : map<nat, set<int>> := map a | a in As :: {};                                                        // annot

    // #########################################################################
    // Set cardinalities
    // #########################################################################

    // k[p] := #{a in A | p.n in a.ns}
    // i.e. number of acceptors have accepted p's proposal
    var k : map<nat, nat> := map p | p in Ps :: 0;                                                                       // annot

    // k_pending[p] := #{(a,Value(no,val,TwoB)) in Prop_Soup[p] | no == p.n}
    // i.e. number of messages in flight that will increment the `p.ho2`
    // variable upon receive
    var k_pending : map<nat, nat> := map p | p in Ps :: 0;                                                               // annot

    // l[p] := #{a in A | p.n !in a.ns && a.max <= p.n}
    // i.e. number of acceptors may accept p's proposal
    var l : map<nat, nat> := map p | p in Ps :: len(As);                                                                 // annot

    // m[p] := #{a in A | p.n !in a.ns && a.max > p.n}
    // i.e. number of acceptors will never accept p's proposal
    var m : map<nat, nat> := map p | p in Ps :: 0;                                                                       // annot

    // #########################################################################

    var WL_main := Ps + As;                                                                                              // harness

    while WL_main != {}                                                                                                  // harness
    invariant WL_main <= Ps + As;                                                                                   // inv
    invariant
        ( domain(Acc_Ns)             == As                                                                               // inv
        && domain(Acc_Max_Seen_N)     == As                                                                              // inv
        && domain(Acc_Max_Accepted_N) == As                                                                              // inv
        && domain(Acc_Soup)           == As                                                                              // inv
        && domain(Acc_MaxV)           == As                                                                              // inv

        && domain(Prop_Decided) == Ps                                                                                    // inv
        && domain(Prop_HO)      == Ps                                                                                    // inv
        && domain(Prop_HO2)     == Ps                                                                                    // inv
        && domain(Prop_Max)     == Ps                                                                                    // inv
        && domain(Prop_N)       == Ps                                                                                    // inv
        && domain(Prop_PC)      == Ps                                                                                    // inv
        && domain(Prop_Ready)   == Ps                                                                                    // inv
        && domain(Prop_Exec_P5) == Ps                                                                                    // inv
        && domain(Prop_Exec_P6) == Ps                                                                                    // inv
        && domain(Prop_Soup)    == Ps                                                                                    // inv
        && domain(Prop_V)       == Ps                                                                                    // inv
        && domain(Prop_WL)      == Ps                                                                                    // inv
        && domain(Prop_WL2)     == Ps                                                                                    // inv
        && domain(Prop_a)       == Ps                                                                                    // inv

        && domain(k)         == Ps                                                                                       // inv
        && domain(k_pending) == Ps                                                                                       // inv
        && domain(l)         == Ps                                                                                       // inv
        && domain(m)         == Ps                                                                                       // inv

        && domain(OneB_Hist)  == As                                                                                      // inv
        && domain(TwoB_Hist)  == As                                                                                      // inv
        && domain(Joined_Rnd) == As                                                                                      // inv

        && domain(Prop_Soup_Hist) == Ps                                                                                  // inv
        && domain(Acc_Soup_Hist)  == As                                                                                  // inv
        );
    invariant forall a:nat,pid:nat,msg:Msg_Acc :: a in As && (pid,msg) in Acc_Soup[a] ==> pid in Ps;                // inv
    invariant forall p:nat,pid:nat,msg:Msg_Prop :: p in Ps && (pid,msg) in Prop_Soup[p] ==> pid in As;              // inv
    invariant forall p:nat,pid:nat,msg:Msg_Prop :: p in Ps && (pid,msg) in Prop_Soup_Hist[p] ==> pid in As;         // inv
    invariant forall p,a :: p in Ps && a == Prop_a[p] ==> a in As;                                                  // harness
    invariant forall p :: p in Ps ==> Prop_WL[p] <= As && Prop_WL2[p] <= As;                                        // inv
    invariant forall p :: p in Ps && Prop_Ready[p] ==> Prop_HO[p] > |As|/2;                                         // inv

    // ----------------------------------------------------------------------

    invariant forall n,v1,v2 :: (n,v1) in TwoA_Hist && (n,v2) in TwoA_Hist ==> v1 == v2; // (5)                     // inv
    invariant forall a,p,n,v :: a in As && (p,Accept(n,v)) in Acc_Soup[a] ==> Prop_PC[p] !in {P0, P1, P2} && n == Prop_N[p] && v == Prop_V[p]; // inv
    invariant forall n,v :: (n,v) in TwoA_Hist ==> exists p :: p in Ps && n == Prop_N[p] && v == Prop_V[p] && Prop_PC[p] !in {P0, P1, P2}; // inv
    invariant forall p :: p in Ps ==> (Prop_Ready[p] ==> Prop_PC[p] !in {P0, P1, P2});                              // inv
    invariant forall p :: p in Ps && Prop_PC[p] in {P4, P5, P6, P7} ==> Prop_Ready[p];                              // inv
    invariant forall p :: p in Ps && Prop_Decided[p] ==> Prop_Ready[p];                                             // inv

    // ----------------------------------------------------------------------

    invariant forall a,n,v :: a in As && (n,v) in TwoB_Hist[a] ==> (n,v) in TwoA_Hist; // (6)                       // inv
    invariant forall a,msg :: a in As && msg in Acc_Soup[a] ==> msg in Acc_Soup_Hist[a];                            // inv
    invariant forall a,n,v :: a in As && (n,v) in TwoB_Hist[a] ==> (exists p :: p in Ps && (p, Accept(n,v)) in Acc_Soup_Hist[a]); // inv
    invariant forall a,n,v,p :: a in As && (p, Accept(n,v)) in Acc_Soup_Hist[a] ==> (n,v) in TwoA_Hist;             // inv

    // ----------------------------------------------------------------------

    invariant forall p :: p in Ps ==> k[p] >= 0 && l[p] >= 0 && m[p] >= 0;                                          // inv
    invariant forall p :: p in Ps ==> |As| == k[p] + l[p] + m[p];                                                   // inv
    invariant forall p :: p in Ps && k[p] > |As|/2 ==> m[p] <= |As|/2;                                              // inv

    invariant forall p :: p in Ps && Prop_Decided[p] ==> k[p] > |As|/2; // (7)                                      // inv
    invariant forall p :: p in Ps ==> Prop_HO2[p] + k_pending[p] <= k[p];                                           // inv
    invariant forall p :: p in Ps ==> k_pending[p] >= 0;                                                            // inv

    // ----------------------------------------------------------------------

    invariant forall a,vote :: a in As && vote in TwoB_Hist[a]==> vote.0 >= 0; // (11)                              // inv

    // ----------------------------------------------------------------------

    invariant forall a,no,maxn,maxv :: a in As && (no, maxn, maxv) in OneB_Hist[a] ==> no in Joined_Rnd[a]; // (15) // inv

    // ----------------------------------------------------------------------

    invariant forall a,n :: a in As && n in Joined_Rnd[a] ==> n <= Acc_Max_Seen_N[a]; // (14)                       // inv

    // ----------------------------------------------------------------------

    invariant forall a,msg,n :: a in As && msg in Acc_Soup[a] && msg.1 == Prepare(n) ==> n >= 0;                    // inv
    invariant forall n :: n in OneA_Hist ==> n >= 0;                                                                // inv

    // ----------------------------------------------------------------------

	invariant forall p,n,v :: (n,v) in TwoA_Hist && p in Ps && Prop_N[p] == n ==> Prop_Ready[p];                     // inv

    // ----------------------------------------------------------------------

    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // !!! Required to prove the safety property !!!
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	// free invariant forall p,p' :: p in Ps && p' in Ps && Prop_Ready[p'] && Prop_N[p] < Prop_N[p'] && Prop_V[p] != Prop_V[p'] ==> m[p] > |As|/2;    // inv
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

    // ----------------------------------------------------------------------

    // invariant forall p1,p2 :: p1 in Ps && p2 in Ps && Prop_Decided[p1] && Prop_Decided[p2] ==> Prop_V[p1] == Prop_V[p2]; // (4) (safety property) // inv

    // ----------------------------------------------------------------------

    decreases *
    {
      var processToRun := *; assume processToRun in WL_main;                                                             // harness

      if processToRun in As {                                                                                            // code
        var a := processToRun;                                                                                           // harness

        /* while true
             (pid, msg) <- recv
             match msg {
               Prepare(no) =>
                 if max1 < no {
                   max1 <- no
                 }
               Accept(no,val) =>
                 if max1 <= no {
                   ns <- ns U {no}
                   if max2 < no {
                     max2 <- no
                     v    <- val
                   }
                 }
             }
             send pid (max1, max2, v)
           done
         */
        if Acc_Soup[a] != multiset{} {                                                                                   // harness
          var pid := *; var msg := *; assume (pid,msg) in Acc_Soup[a];                                                     // code
          Acc_Soup := Acc_Soup[a := Acc_Soup[a] - multiset{(pid,msg)}];                                                  // harness

          var phase;                                                                                                     // code
          var old_max_seen_n := Acc_Max_Seen_N[a];                                                                       // code

          match msg {                                                                                                    // code
            case Prepare(no) =>                                                                                          // code
              if old_max_seen_n < no {                                                                                   // code
                // update counters m & l
                var onea_wl := Ps;                                                                                       // annot
                while onea_wl != {}                                                                                      // annot
                invariant onea_wl <= Ps;                                                                                 // inv
                invariant domain(l) == Ps && domain(m) == Ps;                                                            // inv
                invariant forall p :: p in Ps ==> k[p] >= 0 && l[p] >= 0 && m[p] >= 0;                                   // inv
                invariant forall p :: p in Ps ==> |As| == k[p] + l[p] + m[p];                                            // inv
                decreases |onea_wl|
                {
                  var p' := *; assume p' in onea_wl;                                                                     // annot

                  if Prop_N[p'] !in Acc_Ns[a] &&                                                                         // annot
                    Prop_N[p'] >= Acc_Max_Seen_N[a] &&                                                                   // annot
                    Prop_N[p'] < no &&                                                                                   // annot
                    l[p'] > 0 {                                                                                          // annot
                      m := m[p' := m[p'] + 1];                                                                           // annot
                      l := l[p' := l[p'] - 1];                                                                           // annot
                  }                                                                                                      // annot
                  onea_wl := onea_wl - {p'};                                                                             // annot
                }

                Acc_Max_Seen_N := Acc_Max_Seen_N[a := no];                                                               // code
                Joined_Rnd := Joined_Rnd[a := Joined_Rnd[a] + {no}];                                                     // annot
              }                                                                                                          // code

              phase := OneB;                                                                                             // code
            case Accept(no,val) =>                                                                                       // code
              if old_max_seen_n <= no  {                                                                                 // code
                Acc_Ns := Acc_Ns[a := Acc_Ns[a] + {no}];                                                                 // annot

                if Acc_Max_Accepted_N[a] <= no {                                                                         // code
                  Acc_MaxV := Acc_MaxV[a := val];                                                                        // code
                  Acc_Max_Accepted_N := Acc_Max_Accepted_N [a := no];                                                    // code
                }                                                                                                       // code

                assume l[pid] > 0;                                                                                       // annot
                k := k[pid := k[pid] + 1];                                                                               // annot
                l := l[pid := l[pid] - 1];                                                                               // annot
              }                                                                                                          // code

              phase := TwoB;                                                                                             // code
          }                                                                                                              // code

          if * {                                                                                                         // harness
            var max_seen_n     := Acc_Max_Seen_N[a];
            var max_accepted_n := Acc_Max_Accepted_N[a];
            var maxv           := Acc_MaxV[a];

            var resp := (a, Value(max_seen_n, max_accepted_n, maxv, phase));                                             // code

            Prop_Soup := Prop_Soup[pid := Prop_Soup[pid] + multiset{resp}];                                              // code
            Prop_Soup_Hist := Prop_Soup_Hist[pid := Prop_Soup_Hist[pid] + {resp}];                                       // annot

            // history variable update
            match msg {                                                                                                  // annot
              case Prepare(no) =>                                                                                        // annot
                if old_max_seen_n < no {                                                                                 // annot
                  OneB_Hist := OneB_Hist[a := OneB_Hist[a] + {(no, max_accepted_n, maxv)}];                              // annot
                }                                                                                                        // annot
              case Accept(no,val) =>                                                                                     // annot
                if old_max_seen_n <= no {                                                                                // annot
                  TwoB_Hist := TwoB_Hist[a := TwoB_Hist[a] + {(no,val)}];                                                // annot
                  k_pending := k_pending[pid := k_pending[pid] + 1];                                                     // annot
                }                                                                                                        // annot
            }                                                                                                            // annot
          }                                                                                                              // harness
        }                                                                                                                // harness
      } else if processToRun in Ps {                                                                                     // code
        var p := processToRun;                                                                                           // harness

        if Prop_PC[p] == P0 {                                                                                            // harness
          /* for a in A:
               <P1>
               <P2>
             done
           */
          if Prop_WL[p] != {} { // a in Prop_WL[p]                                                                       // code
            var a := *; assume a in Prop_WL[p];                                                                          // harness

            Prop_a := Prop_a[p := a];                                                                                    // harness
            Prop_WL := Prop_WL[p := Prop_WL[p] - {a}];                                                                   // harness
            Prop_PC := Prop_PC[p := P1];                                                                                 // harness
          } else {                                                                                                       // harness
            Prop_PC := Prop_PC[p := P3];                                                                                 // harness
          }

        } else if Prop_PC[p] == P1 {                                                                                     // harness
          /* send a (p, Prepare(n))
           */
          var a := Prop_a[p];
          var n := Prop_N[p];

          Acc_Soup := Acc_Soup[a := Acc_Soup[a] + multiset{(p, Prepare(n))}];                                            // code
          Acc_Soup_Hist := Acc_Soup_Hist[a := Acc_Soup_Hist[a] + {(p, Prepare(n))}];                                     // annot

          // history update
          OneA_Hist := OneA_Hist + {n};                                                                                  // annot

          Prop_PC := Prop_PC[p := P2];                                                                                   // harness

        } else if Prop_PC[p] == P2 {                                                                                     // harness
          /* reply <- recvTO(a);
             match reply {
               None =>
                 return ()
               Some Value(no, val, OneB) =>
                 if no > max {
                   max <- no
                   v   <- val
                 }
                 ho <- ho + 1
             }
           */
          var a := Prop_a[p];
          var n := Prop_N[p];

          if * {                                                                                                         // harness
            if Prop_Soup[p] != multiset{} {                                                                              // harness
              var pid := *; var msg := *; assume (pid,msg) in Prop_Soup[p];                                              // code
              Prop_Soup := Prop_Soup[p := Prop_Soup[p] - multiset{(pid,msg)}];                                           // harness

              if msg.max_seen_n < n {                                                                                    // code
                if msg.max_accepted_n > Prop_Max[p] {                                                                    // code
                  Prop_Max := Prop_Max[p := msg.max_accepted_n];                                                         // code
                  Prop_V   := Prop_V  [p := msg.max_val];                                                                // code
                }                                                                                                        // code
                Prop_HO := Prop_HO[p := Prop_HO[p] + 1];                                                                 // code
              }                                                                                                          // code

              Prop_PC := Prop_PC[p := P0];                                                                               // harness
            }                                                                                                            // harness
          } else {                                                                                                       // harness
            Prop_PC := Prop_PC[p := P0];                                                                                 // harness
          }                                                                                                              // harness

        } else if Prop_PC[p] == P3 {                                                                                     // harness
          /* if 2 x ho > |A| {
               ready <- true
               <P4>
             }
             <P8>
           */
       // } // code
          var ho := Prop_HO[p];                                                                                          // code
          if ho * 2 > |As| {                                                                                             // code
            Prop_Ready := Prop_Ready[p := true];                                                                         // code
            Prop_PC    := Prop_PC   [p := P4];                                                                           // harness
          } else {                                                                                                       // harness
            Prop_PC := Prop_PC[p := P8];                                                                                 // harness
          }                                                                                                              // code

        } else if Prop_PC[p] == P4 {                                                                                     // harness
          /* for a in A:
               <P5>
               <P6>
             done
             <P7>
           */
          if Prop_WL2[p] != {} { // a in Prop_WL2[p]                                                                     // code
            var a := *; assume a in Prop_WL2[p];                                                                         // harness

            Prop_a := Prop_a[p := a];
            Prop_WL2 := Prop_WL2[p := Prop_WL2[p] - {a}];                                                                // harness
            Prop_PC := Prop_PC[p := P5];                                                                                 // harness
          } else {                                                                                                       // harness
            Prop_PC := Prop_PC[p := P7];                                                                                 // harness
          }

        } else if Prop_PC[p] == P5 {                                                                                     // harness
          /* send a (p, Accept(n))
           */
          var a := Prop_a[p];
          var n := Prop_N[p];
          var v := Prop_V[p];

          Acc_Soup := Acc_Soup[a := Acc_Soup[a] + multiset{(p, Accept(n,v))}];                                           // code
          Acc_Soup_Hist := Acc_Soup_Hist[a := Acc_Soup_Hist[a] + {(p, Accept(n,v))}];                                    // annot

          // history update
          TwoA_Hist := TwoA_Hist + {(n,v)};                                                                              // annot
          Prop_Exec_P5 := Prop_Exec_P5[p := true];                                                                       // annot

          Prop_PC := Prop_PC[p := P6];                                                                                   // harness

        } else if Prop_PC[p] == P6 {                                                                                     // harness
          /* reply <- recvTO(a);
             match reply {
               None =>
                 return ()
               Some Value(no, val, TwoB) =>
                 if no = n {
                   ho2 <- ho2 + 1
                 }
             }
           */
          var a := Prop_a[p];

          if * {                                                                                                         // harness
            if Prop_Soup[p] != multiset{} {                                                                              // harness
              var pid := *; var msg := *; assume (pid,msg) in Prop_Soup[p];                                              // code
              Prop_Soup := Prop_Soup[p := Prop_Soup[p] - multiset{(pid,msg)}];                                           // harness

              if Prop_N[p] >= msg.max_seen_n {                                                                           // code
                Prop_HO2 := Prop_HO2[p := Prop_HO2[p] + 1];                                                              // code
                assume k_pending[p] > 0;                                                                                 // annot
                k_pending := k_pending[p := k_pending[p] - 1];                                                           // annot
              }                                                                                                          // code

              Prop_Exec_P6 := Prop_Exec_P6[p := true];                                                                   // annot
              Prop_PC := Prop_PC[p := P4];                                                                               // harness
            }                                                                                                            // harness
          } else {                                                                                                       // harness
            Prop_Exec_P6 := Prop_Exec_P6[p := true];                                                                     // harness
            Prop_PC := Prop_PC[p := P4];                                                                                 // harness
          }

        } else if Prop_PC[p] == P7 {                                                                                     // harness
          /* if ho2 * 2 > |A| {
               decided <- true
             }
           */
       // } // code
          var ho2 := Prop_HO2[p];                                                                                        // code
          if ho2 * 2 > |As| {                                                                                            // code
            Prop_Decided := Prop_Decided[p := true];                                                                     // code
          }                                                                                                              // code
          Prop_PC := Prop_PC[p := P8];                                                                                   // harness
        } else if Prop_PC[p] == P8 {                                                                                     // harness
          WL_main := WL_main - {p};                                                                                      // harness
        }                                                                                                                // harness
      }                                                                                                                  // code
    }                                                                                                                    // harness
  }
}
