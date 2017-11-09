// code       : 76
// annot      : 29
// harness    : 51

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
                 )                                                                                                       // code
    requires forall p :: p in Ps ==> p != c                                                                              // annot
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

    var c_p2_is_run := false;                                                                                            // code

    var Ps_p0_is_run := map p | p in Ps :: false; assume domain(Ps_p0_is_run) == Ps;                                     // code
    var Ps_p2_is_run := map p | p in Ps :: false; assume domain(Ps_p2_is_run) == Ps;                                     // code
    var Ps_p3_is_run := map p | p in Ps :: false; assume domain(Ps_p3_is_run) == Ps;                                     // code

    while main_WL != {}                                                                                                  // code
    invariant domain(prep_buf) == Ps;                                                                                    // annot
    invariant domain(dec_buf) == Ps;                                                                                     // annot
    invariant domain(Ps_pc) == Ps;                                                                                       // annot
    invariant domain(Decision) == Ps;                                                                                    // annot
    invariant domain(Val) == Ps;                                                                                         // annot
    invariant domain(Value) == Ps;                                                                                       // annot
    invariant domain(Id) == Ps;                                                                                          // annot
    invariant domain(Msg) == Ps;                                                                                         // annot
    invariant domain(Ps_p0_is_run) == Ps;                                                                                // annot
    invariant domain(Ps_p2_is_run) == Ps;                                                                                // annot
    invariant domain(Ps_p3_is_run) == Ps;                                                                                // annot

    invariant main_WL <= Ps + {c};                                                                                       // annot
    invariant WL <= Ps;                                                                                                  // annot
    invariant WL2 <= Ps;                                                                                                 // annot

    invariant forall p :: p in Ps && p !in main_WL ==> Ps_pc[p] == P5;                                                   // annot

    // ##########################################################################
    // Sequencing
    // ##########################################################################
    invariant c_p2_is_run <==> c_pc in {P3, P4, P5, P6};                                                                 // annot

    invariant forall p :: p in Ps ==> ( Ps_p0_is_run[p] <==> Ps_pc[p] in {P1, P2, P3, P4, P5} );                         // annot
    invariant forall p :: p in Ps ==> ( Ps_p2_is_run[p] <==> Ps_pc[p] in {P3, P4, P5} );                                 // annot
    invariant forall p :: p in Ps ==> ( Ps_p3_is_run[p] <==> Ps_pc[p] in {P4, P5} );                                     // annot
    // ##########################################################################

    // ##########################################################################
    // 1st phase
    // ##########################################################################
    invariant forall p,i :: p in Ps && 0 <= i < |prep_buf[p]| ==> prep_buf[p][i] == (c, proposal);                       // annot
    invariant forall p :: p in Ps && Ps_p0_is_run[p] ==> Id[p] == c && Val[p] == proposal;                               // annot
    // ##########################################################################

    // ##########################################################################
    // 2nd phase
    // ##########################################################################
    invariant forall p :: p in Ps && |dec_buf[p]| > 0 ==> c_p2_is_run;                                                   // annot
    invariant forall p,i :: p in Ps && c_p2_is_run && 0 <= i < |dec_buf[p]| ==> dec_buf[p][i] == reply;                  // annot
    invariant forall p :: p in Ps && Ps_p2_is_run[p] ==> c_p2_is_run && Decision[p] == reply;                            // annot
    invariant c_p2_is_run ==> (reply == Commit <==> committed);                                                          // annot
    invariant forall p :: p in Ps && Ps_p3_is_run[p] && Decision[p] == Commit ==> Value[p] == Val[p];                    // annot
    // ##########################################################################

    decreases *                                                                                                          // annot
    {
      var p := *; assume p in main_WL;                                                                                   // harness

      if p == c {                                                                                                        // harness
        // ################################################################                                              
        // Coordinator                                                                                                   
        // ################################################################                                              
        if c_pc == P0 {                                                                                                  // harness
          /* for w in Ps:                                                                                                
               send w (c, proposal)                                                                                     
             end                                                                                                       
           */                                                                                                         
          if WL != {} {                                                                                                  // code
            var w := *; assume w in WL;                                                                                  // code
            prep_buf := prep_buf[w := prep_buf[w] + [(c, proposal)]];                                                    // code
            WL := WL - {w};                                                                                              // code
          } else {                                                                                                       // harness
            c_pc := P1;                                                                                                  // harness
          }
        } else if c_pc == P1 {                                                                                           // harness
          /* for w in Ps:                                                                                                
               msg <- recv                                                                                               
               if msg = Abort                                                                                            
                 abort <- true                                                                                           
               end                                                                                                       
             end                                                                                                         
           */                                                                                                            
          if WL2 != {} {                                                                                                 // code
            if |vote_buf| > 0 {                                                                                          // harness
              vote := vote_buf[0];                                                                                       // code
              var w := *; assume w in WL2;                                                                               // code

              if vote == No {                                                                                            // code
                abort := true;                                                                                           // code
              }                                                                                                          // code

              vote_buf := vote_buf[1..];                                                                                 // harness
              WL2 := WL2 - {w};                                                                                          // code
            }
          } else {                                                                                                       // harness
            c_pc := P2;                                                                                                  // harness
          }
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
          }                                                                                                              // code

          c_p2_is_run := true;                                                                                           // code
          c_pc := P3;                                                                                                    // harness
        } else if c_pc == P3 {                                                                                           // harness
          /* for w in Ps:                                                                                                
               send w reply                                                                                              
             end                                                                                                         
           */                                                                                                            
          if WL3 != {} {                                                                                                 // code
            var w := *; assume w in WL;                                                                                  // code
            dec_buf := dec_buf[w := dec_buf[w] + [reply]];                                                               // code
            WL3 := WL3 - {w};                                                                                            // code
          } else {                                                                                                       // harness
            c_pc := P4;                                                                                                  // harness
          }
        } else if c_pc == P4 {                                                                                           // harness
          /* for w in Ps:                                                                                                
               _ <- recv                                                                                                 
             end                                                                                                         
           */                                                                                                            
          if WL4 != {} {                                                                                                 // code
            if |ack_buf| != 0 {                                                                                          // harness
              var w := *;   assume w in WL;                                                                              // code
              var ack := ack_buf[0];                                                                                     // code

              ack_buf := ack_buf[1..];                                                                                   // harness
              WL4 := WL4 - {w};                                                                                          // code
            }
          } else {                                                                                                       // harness
            c_pc := P5;                                                                                                  // harness
          }
        } else if c_pc == P5 {                                                                                           // harness
          main_WL := main_WL - {c};                                                                                      // harness
          c_pc := P6;                                                                                                    // harness
        }
      } else {                                                                                                           // harness
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
          }                                                                                                              // code

          Ps_p0_is_run := Ps_p0_is_run[p := true];                                                                       // code
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

          Ps_p2_is_run := Ps_p2_is_run[p := true];                                                                       // code
          Ps_pc := Ps_pc[p := P3];                                                                                       // harness
        } else if p_pc == P3 && ! Ps_p3_is_run[p] {                                                                      // harness
          /* if decision == Commit                                                                                       
               value <- val                                                                                              
             end                                                                                                         
             send id Ack                                                                                                 
           */                                                                                                            
          if Decision[p] == Commit {                                                                                     // code
            Value := Value[p := Val[p]];                                                                                 // code
          }                                                                                                              // code
          ack_buf := ack_buf + [Ack];                                                                                    // code

          Ps_p3_is_run := Ps_p3_is_run[p := true];                                                                       // code
          Ps_pc := Ps_pc[p := P4];                                                                                       // harness
        } else if p_pc == P4 {                                                                                           // harness
          main_WL := main_WL - {p};                                                                                      // harness
          Ps_pc := Ps_pc[p := P5];                                                                                       // harness
        }                                                                                                                
      }                                                                                                                 
    }                                                                                                                  

    assert committed ==> (forall p :: p in Ps ==> Value[p] == proposal);                                                 // annot

  }                                                                                                                   
}                                                                                                                    