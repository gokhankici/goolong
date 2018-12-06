module TwoPhaseCommit
{
  datatype VoteType     = Yes | No                                                                                       // code
  datatype DecisionType = Commit | Abort                                                                                 // code
  datatype AckType      = Ack                                                                                            // code
  datatype PC           = P0 | P1 | P2 | P3 | P4 | P5 | P6                                                               // harness

  function domain<U,V>(m: map<U,V>) : set<U>
    ensures domain(m) == set u : U | u in m :: u;
    ensures forall u :: u in domain(m) ==> u in m;
  {
    set u : U | u in m :: u
  }

  method {:timeLimit 0} TwoPhase( Ps : set<nat> // workers                                                               // code
                 , c  : nat      // coordinator                                                                          // code
                 )
    requires forall p :: p in Ps ==> p != c
    decreases *
  {
    // ################################################################
    // Initialize C
    // ################################################################
    var proposal : int := *;                                                                                             // code
    var committed      := false;                                                                                         // code
    var abort          := false;                                                                                         // code
    var reply          := Abort;                                                                                         // code
    var c_pc           := P0;                                                                                            // harness

    var vote_buf : seq<VoteType> := [];                                                                                  // harness
    var ack_buf : seq<AckType>   := [];                                                                                  // harness
    // ################################################################

    // ################################################################
    // Initialize Ps
    // ################################################################
    var Id       := map i | i in Ps :: 0;                                                                                // code
    var Val      := map i | i in Ps :: 0;                                                                                // code
    var Value    := map i | i in Ps :: 0;                                                                                // code
    var Msg      : map<nat,VoteType> := *;     assume domain(Msg) == Ps;                                                 // code
    var Decision : map<nat,DecisionType> := *; assume domain(Decision) == Ps;                                            // code
    var Ps_pc    := map i | i in Ps :: P0;                                                                               // harness

    var prep_buf : map<nat, seq<(nat,nat)>>   := map i | i in Ps :: [];                                                  // harness
    var dec_buf : map<nat, seq<DecisionType>> := map i | i in Ps :: [];                                                  // harness
    // ################################################################

    var main_WL := Ps + {c};                                                                                             // harness
    var WL  := Ps;                                                                                                       // harness
    var WL2 := Ps;                                                                                                       // harness
    var WL3 := Ps;                                                                                                       // harness
    var WL4 := Ps;                                                                                                       // harness
    var vote := *;                                                                                                       // code

    var c_p2_is_run := false;                                                                                            // annot

    var Ps_p0_is_run := map p | p in Ps :: false;                                                                        // annot
                        assume domain(Ps_p0_is_run) == Ps;                                                               // inv
    var Ps_p2_is_run := map p | p in Ps :: false;                                                                        // annot
                        assume domain(Ps_p2_is_run) == Ps;                                                               // inv
    var Ps_p3_is_run := map p | p in Ps :: false;                                                                        // annot
                        assume domain(Ps_p3_is_run) == Ps;                                                               // inv

    while main_WL != {}                                                                                                  // harness
    invariant domain(prep_buf) == Ps;                                                                                    // inv
    invariant domain(dec_buf) == Ps;                                                                                     // inv
    invariant domain(Ps_pc) == Ps;                                                                                       // inv
    invariant domain(Decision) == Ps;                                                                                    // inv
    invariant domain(Val) == Ps;                                                                                         // inv
    invariant domain(Value) == Ps;                                                                                       // inv
    invariant domain(Id) == Ps;                                                                                          // inv
    invariant domain(Msg) == Ps;                                                                                         // inv
    invariant domain(Ps_p0_is_run) == Ps;                                                                                // inv
    invariant domain(Ps_p2_is_run) == Ps;                                                                                // inv
    invariant domain(Ps_p3_is_run) == Ps;                                                                                // inv

    invariant main_WL <= Ps + {c};                                                                                       // inv
    invariant WL <= Ps;                                                                                                  // inv
    invariant WL2 <= Ps;                                                                                                 // inv

    invariant forall p :: p in Ps && p !in main_WL ==> Ps_pc[p] == P5;                                                   // inv

    // ##########################################################################
    // Sequencing
    // ##########################################################################
    invariant c_p2_is_run <==> c_pc in {P3, P4, P5, P6};                                                                 // inv

    invariant forall p :: p in Ps ==> ( Ps_p0_is_run[p] <==> Ps_pc[p] in {P1, P2, P3, P4, P5} );                         // inv
    invariant forall p :: p in Ps ==> ( Ps_p2_is_run[p] <==> Ps_pc[p] in {P3, P4, P5} );                                 // inv
    invariant forall p :: p in Ps ==> ( Ps_p3_is_run[p] <==> Ps_pc[p] in {P4, P5} );                                     // inv
    // ##########################################################################

    // ##########################################################################
    // 1st phase
    // ##########################################################################
    invariant forall p,i :: p in Ps && 0 <= i < |prep_buf[p]| ==> prep_buf[p][i] == (c, proposal);                       // inv
    invariant forall p :: p in Ps && Ps_p0_is_run[p] ==> Id[p] == c && Val[p] == proposal;                               // inv
    // ##########################################################################

    // ##########################################################################
    // 2nd phase
    // ##########################################################################
    invariant forall p :: p in Ps && |dec_buf[p]| > 0 ==> c_p2_is_run;                                                   // inv
    invariant forall p,i :: p in Ps && c_p2_is_run && 0 <= i < |dec_buf[p]| ==> dec_buf[p][i] == reply;                  // inv
    invariant forall p :: p in Ps && Ps_p2_is_run[p] ==> c_p2_is_run && Decision[p] == reply;                            // inv
    invariant c_p2_is_run ==> (reply == Commit <==> committed);                                                          // inv
    invariant forall p :: p in Ps && Ps_p3_is_run[p] && Decision[p] == Commit ==> Value[p] == Val[p];                    // inv
    // ##########################################################################

    decreases *                                                                                                          // harness
    {
      var p := *; assume p in main_WL;                                                                                   // harness

      if p == c {                                                                                                        // code
        // ################################################################
        // Coordinator
        // ################################################################
        if c_pc == P0 {                                                                                                  // harness
          /* for w in Ps:
               send w (c, proposal)
             end
           */
          if WL != {} { // w in WL                                                                                       // code
            var w := *; assume w in WL;                                                                                  // harness
            prep_buf := prep_buf[w := prep_buf[w] + [(c, proposal)]];                                                    // code
            WL := WL - {w};                                                                                              // harness
          } else {                                                                                                       // harness
            c_pc := P1;                                                                                                  // harness
          } // code
        } else if c_pc == P1 {                                                                                           // harness
          /* for w in Ps:
               msg <- recv
               if msg = Abort
                 abort <- true
               end
             end
           */
          if WL2 != {} { // w in WL2                                                                                     // code
            if |vote_buf| > 0 {                                                                                          // harness
              var w := *; assume w in WL2;                                                                               // harness
              vote := vote_buf[0];                                                                                       // code

              if vote == No {                                                                                            // code
                abort := true;                                                                                           // code
              }                                                                                                          // code

              vote_buf := vote_buf[1..];                                                                                 // harness
              WL2 := WL2 - {w};                                                                                          // harness
            } // harness
          } else {                                                                                                       // harness
            c_pc := P2;                                                                                                  // harness
          } // code
        } else if c_pc == P2 && ! c_p2_is_run {                                                                          // harness
          /* if abort
               reply <- Abort
             else
               reply <- Commit
               committed <- true
             end
           */

          if abort {                                                                                                     // code
            reply     := Abort;                                                                                          // code
            committed := false;                                                                                          // code
          } else {                                                                                                       // code
            reply     := Commit;                                                                                         // code
            committed := true;                                                                                           // code
          } // code

          c_p2_is_run := true;                                                                                           // annot
          c_pc := P3;                                                                                                    // harness
        } else if c_pc == P3 {                                                                                           // harness
          /* for w in Ps:
               send w reply
             end
           */
          if WL3 != {} { // w in WL3                                                                                     // code
            var w := *; assume w in WL3; assume w in dec_buf;                                                            // harness
            dec_buf := dec_buf[w := dec_buf[w] + [reply]];                                                               // code
            WL3 := WL3 - {w};                                                                                            // harness
          } else {                                                                                                       // harness
            c_pc := P4;                                                                                                  // harness
          } // code
        } else if c_pc == P4 {                                                                                           // harness
          /* for w in Ps:
               _ <- recv
             end
           */
          if WL4 != {} { // w in WL4                                                                                     // code
            if |ack_buf| != 0 {                                                                                          // harness
              var w := *;   assume w in WL4;                                                                              // harness
              var ack := ack_buf[0];                                                                                     // code

              ack_buf := ack_buf[1..];                                                                                   // harness
              WL4 := WL4 - {w};                                                                                          // harness
            } // harness
          } else {                                                                                                       // harness
            c_pc := P5;                                                                                                  // harness
          } // code
        } else if c_pc == P5 {                                                                                           // harness
          main_WL := main_WL - {c};                                                                                      // harness
          c_pc := P6;                                                                                                    // harness
        } // harness
      } else {                                                                                                           // code
        // ################################################################
        // Workers
        // ################################################################
        assert p in Ps;                                                                                                  // harness

        var p_pc := Ps_pc[p];                                                                                            // harness

        if p_pc == P0 && |prep_buf[p]| > 0 && ! Ps_p0_is_run[p] {                                                        // harness
          /* (id, val) <- recv
             if *
               msg <- Commit
             else
               msg <- Abort
             end
           */
          var prep := prep_buf[p][0];                                                                                    // code
          Id  := Id [p := prep.0];                                                                                       // code
          Val := Val[p := prep.1];                                                                                       // code
          prep_buf := prep_buf[p := prep_buf[p][1..]];                                                                   // harness

          if * {                                                                                                         // code
            Msg := Msg[p := Yes];                                                                                        // code
          } else {                                                                                                       // code
            Msg := Msg[p := No];                                                                                         // code
          } // code

          Ps_p0_is_run := Ps_p0_is_run[p := true];                                                                       // annot
          Ps_pc := Ps_pc[p := P1];                                                                                       // harness
        } else if p_pc == P1 {                                                                                           // harness
          /* send id msg
           */
          vote_buf := vote_buf + [Msg[p]];                                                                               // code

          Ps_pc := Ps_pc[p := P2];                                                                                       // harness
        } else if p_pc == P2 && |dec_buf[p]| > 0 && ! Ps_p2_is_run[p] {                                                  // harness
          /* decision <- recv
           */
          var msg := dec_buf[p][0];                                                                                      // code
          Decision := Decision[p := msg];                                                                                // code
          dec_buf := dec_buf[p := dec_buf[p][1..]];                                                                      // harness

          Ps_p2_is_run := Ps_p2_is_run[p := true];                                                                       // annot
          Ps_pc := Ps_pc[p := P3];                                                                                       // harness
        } else if p_pc == P3 && ! Ps_p3_is_run[p] {                                                                      // harness
          /* if decision == Commit
               value <- val
             end
             send id Ack
           */
          if Decision[p] == Commit {                                                                                     // code
            Value := Value[p := Val[p]];                                                                                 // code
          } // code
          ack_buf := ack_buf + [Ack];                                                                                    // code

          Ps_p3_is_run := Ps_p3_is_run[p := true];                                                                       // annot
          Ps_pc := Ps_pc[p := P4];                                                                                       // harness
        } else if p_pc == P4 {                                                                                           // harness
          main_WL := main_WL - {p};                                                                                      // harness
          Ps_pc := Ps_pc[p := P5];                                                                                       // harness
        }
      }                                                                                                                  // code
    }

    assert committed ==> (forall p :: p in Ps ==> Value[p] == proposal);                                                 // inv

  }
}
