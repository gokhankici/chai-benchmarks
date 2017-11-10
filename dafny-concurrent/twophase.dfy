module TwoPhaseCommit
{
  datatype VoteType     = Yes | No
  datatype DecisionType = Commit | Abort
  datatype AckType      = Ack
  datatype PC           = P0 | P1 | P2 | P3 | P4 | P5 | P6

  function domain<U,V>(m: map<U,V>) : set<U>
    ensures domain(m) == set u : U | u in m :: u;
    ensures forall u :: u in domain(m) ==> u in m;
  {
    set u : U | u in m :: u
  }

  method TwoPhase( Ps : set<nat> // workers
                 , c  : nat      // coordinator
                 )
    requires forall p :: p in Ps ==> p != c
    decreases *
  {
    // ################################################################
    // Initialize C
    // ################################################################
    var proposal : int := *;
    var committed      := false;
    var abort          := false;
    var reply          := Abort;
    var c_pc           := P0;

    var vote_buf : seq<VoteType> := [];
    var ack_buf : seq<AckType>   := [];
    // ################################################################

    // ################################################################
    // Initialize Ps
    // ################################################################
    var Id       := map i | i in Ps :: 0;
    var Val      := map i | i in Ps :: 0;
    var Value    := map i | i in Ps :: 0;
    var Msg      : map<nat,VoteType> := *;     assume domain(Msg) == Ps;
    var Decision : map<nat,DecisionType> := *; assume domain(Decision) == Ps;
    var Ps_pc    := map i | i in Ps :: P0;

    var prep_buf : map<nat, seq<(nat,nat)>>   := map i | i in Ps :: [];
    var dec_buf : map<nat, seq<DecisionType>> := map i | i in Ps :: [];
    // ################################################################

    var main_WL := Ps + {c};
    var WL  := Ps;
    var WL2 := Ps;
    var WL3 := Ps;
    var WL4 := Ps;
    var vote := *;

    var c_p0_is_run := false;
    var c_p1_is_run := false;
    var c_p2_is_run := false;
    var c_p3_is_run := false;
    var c_p4_is_run := false;

    var Ps_p0_is_run := map p | p in Ps :: false; assume domain(Ps_p0_is_run) == Ps;
    var Ps_p1_is_run := map p | p in Ps :: false; assume domain(Ps_p1_is_run) == Ps;
    var Ps_p2_is_run := map p | p in Ps :: false; assume domain(Ps_p2_is_run) == Ps;
    var Ps_p3_is_run := map p | p in Ps :: false; assume domain(Ps_p3_is_run) == Ps;

    while main_WL != {}
    invariant domain(prep_buf) == Ps;
    invariant domain(dec_buf) == Ps;
    invariant domain(Ps_pc) == Ps;
    invariant domain(Decision) == Ps;
    invariant domain(Val) == Ps;
    invariant domain(Value) == Ps;
    invariant domain(Id) == Ps;
    invariant domain(Msg) == Ps;
    invariant domain(Ps_p0_is_run) == Ps;
    invariant domain(Ps_p1_is_run) == Ps;
    invariant domain(Ps_p2_is_run) == Ps;
    invariant domain(Ps_p3_is_run) == Ps;

    invariant main_WL <= Ps + {c};
    invariant WL <= Ps;
    invariant WL2 <= Ps;

    invariant forall p :: p in Ps && p !in main_WL ==> Ps_pc[p] == P5;

    // ##########################################################################
    // Sequencing
    // ##########################################################################
    invariant c_p2_is_run <==> c_pc in {P3, P4, P5, P6};

    invariant forall p :: p in Ps ==> ( Ps_p0_is_run[p] <==> Ps_pc[p] in {P1, P2, P3, P4, P5} );
    invariant forall p :: p in Ps ==> ( Ps_p2_is_run[p] <==> Ps_pc[p] in {P3, P4, P5} );
    invariant forall p :: p in Ps ==> ( Ps_p3_is_run[p] <==> Ps_pc[p] in {P4, P5} );
    // ##########################################################################

    // ##########################################################################
    // 1st phase
    // ##########################################################################
    invariant forall p,i :: p in Ps && 0 <= i < |prep_buf[p]| ==> prep_buf[p][i] == (c, proposal);
    invariant forall p :: p in Ps && Ps_p0_is_run[p] ==> Id[p] == c && Val[p] == proposal;
    // ##########################################################################

    // ##########################################################################
    // 2nd phase
    // ##########################################################################
    invariant forall p :: p in Ps && |dec_buf[p]| > 0 ==> c_p2_is_run;
    invariant forall p,i :: p in Ps && c_p2_is_run && 0 <= i < |dec_buf[p]| ==> dec_buf[p][i] == reply;
    invariant forall p :: p in Ps && Ps_p2_is_run[p] ==> c_p2_is_run && Decision[p] == reply;
    invariant c_p2_is_run ==> (reply == Commit <==> committed);
    invariant forall p :: p in Ps && Ps_p3_is_run[p] && Decision[p] == Commit ==> Value[p] == Val[p];
    // ##########################################################################

    decreases *
    {
      var p := *; assume p in main_WL;

      if p == c {
        // ################################################################
        // Coordinator
        // ################################################################
        if c_pc == P0 && ! c_p0_is_run {
          /* for w in Ps:
               send w (c, proposal)
             end
           */
          if WL != {} {
            var w := *; assume w in WL;
            prep_buf := prep_buf[w := prep_buf[w] + [(c, proposal)]];
            WL := WL - {w};
          } else {
            c_p0_is_run := true;
            c_pc := P1;
          }
        } else if c_pc == P1 && ! c_p1_is_run {
          /* for w in Ps:
               msg <- recv
               if msg = Abort
                 abort <- true
               end
             end
           */
          if WL2 != {} {
            if |vote_buf| > 0 {
              vote := vote_buf[0];
              var w := *; assume w in WL2;

              if vote == No {
                abort := true;
              }

              vote_buf := vote_buf[1..];
              WL2 := WL2 - {w};
            }
          } else {
            c_p1_is_run := true;
            c_pc := P2;
          }
        } else if c_pc == P2 && ! c_p2_is_run {
          /* if abort
               reply <- Abort
             else
               reply <- Commit
               committed <- true
             end
           */

          if abort {
            reply     := Abort;
            committed := false;
          } else {
            reply     := Commit;
            committed := true;
          }

          c_p2_is_run := true;
          c_pc := P3;
        } else if c_pc == P3 && ! c_p3_is_run {
          /* for w in Ps:
               send w reply
             end
           */
          if WL3 != {} {
            var w := *; assume w in WL;
            dec_buf := dec_buf[w := dec_buf[w] + [reply]];
            WL3 := WL3 - {w};
          } else {
            c_p3_is_run := true;
            c_pc := P4;
          }
        } else if c_pc == P4 && ! c_p4_is_run {
          /* for w in Ps:
               _ <- recv
             end
           */
          if WL4 != {} {
            if |ack_buf| != 0 {
              var w := *;   assume w in WL;
              var ack := ack_buf[0];

              ack_buf := ack_buf[1..];
              WL4 := WL4 - {w};
            }
          } else {
            c_p4_is_run := true;
            c_pc := P5;
          }
        } else if c_pc == P5 {
          main_WL := main_WL - {c};
          c_pc := P6;
        }
      } else {
        // ################################################################
        // Workers
        // ################################################################
        assert p in Ps;

        var p_pc := Ps_pc[p];

        if p_pc == P0 && |prep_buf[p]| > 0 && ! Ps_p0_is_run[p] {
          /* (id, val) <- recv
             if *
               msg <- Commit
             else
               msg <- Abort
             end
           */
          var prep := prep_buf[p][0];
          Id  := Id [p := prep.0];
          Val := Val[p := prep.1];
          prep_buf := prep_buf[p := prep_buf[p][1..]];

          if * {
            Msg := Msg[p := Yes];
          } else {
            Msg := Msg[p := No];
          }

          Ps_p0_is_run := Ps_p0_is_run[p := true];
          Ps_pc := Ps_pc[p := P1];
        } else if p_pc == P1 && ! Ps_p1_is_run[p] {
          /* send id msg
           */
          vote_buf := vote_buf + [Msg[p]];

          Ps_p1_is_run := Ps_p1_is_run[p := true];
          Ps_pc := Ps_pc[p := P2];
        } else if p_pc == P2 && |dec_buf[p]| > 0 && ! Ps_p2_is_run[p] {
          /* decision <- recv
           */
          var msg := dec_buf[p][0];
          Decision := Decision[p := msg];
          dec_buf := dec_buf[p := dec_buf[p][1..]];

          Ps_p2_is_run := Ps_p2_is_run[p := true];
          Ps_pc := Ps_pc[p := P3];
        } else if p_pc == P3 && ! Ps_p3_is_run[p] {
          /* if decision == Commit
               value <- val
             end
             send id Ack
           */
          if Decision[p] == Commit {
            Value := Value[p := Val[p]];
          }
          ack_buf := ack_buf + [Ack];

          Ps_p3_is_run := Ps_p3_is_run[p := true];
          Ps_pc := Ps_pc[p := P4];
        } else if p_pc == P4 {
          main_WL := main_WL - {p};
          Ps_pc := Ps_pc[p := P5];
        }
      }
    }

    assert committed ==> (forall p :: p in Ps ==> Value[p] == proposal);

  }
}
