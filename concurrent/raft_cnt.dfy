// code       : 71
// annot      : 52
// harness    : 62

module RaftLeaderElection {
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

  datatype Loc = P0 | P1 | P2 | P3 | P4             

  method RaftLeaderElection                                                                                              // code
    ( Fs : set<nat> // followers                                                                                         // code
    , Cs : set<nat> // candidates                                                                                        // code
    )                                                                                                                    // code
    requires |Cs| > 0;                                                                                                   // annot
    requires |Fs| >= 2;                                                                                                  // annot
    requires Fs !! Cs;                                                                                                   // annot
    decreases *                                                                                                          
  {                                                                                                                     
    // #########################################################################                                       
    // follower's local state                                                                                         
    // #########################################################################                                     
    var f_term : map<nat, nat>  := *;                                                                                    // code
    assume domain(f_term) == Fs;                                                                                         // harness

    var f_voted : map<nat, bool> := map f | f in Fs :: false;                                                            // code
    assume domain(f_voted) == Fs;                                                                                        // harness

    var f_vote : map<nat, nat>  := *;                                                                                    // code
    assume domain(f_vote) == Fs;                                                                                         // harness
    assume forall f,c :: f in Fs && c == f_vote[f] ==> c in Cs;                                                          // harness

    var f_pid : map<nat, nat>  := *;                                                                                     // code
    assume domain(f_pid) == Fs;                                                                                          // harness
    assume forall f,c :: f in Fs && c == f_pid[f] ==> c in Cs;                                                           // harness

    // last c worked with                                                                                                
    var f_c  : map<nat,nat> := *;                                                                                        // code
    assume domain(f_c) == Fs;                                                                                            // harness
    assume forall f,c :: f in Fs && c == f_c[f] ==> c in Cs;                                                             // harness

    // worklist of each follower's for loop                                                                             
    var f_WL : map<nat,set<nat>> := map f | f in Fs :: Cs;                                                               // harness
    assume domain(f_WL) == Fs;                                                                                           // harness
    assume forall f,c :: f in Fs && c in f_WL[f] ==> c in Cs;                                                            // harness

    // message buffer -- ReqVote(term : nat, pid : nat)                                                                 
    var f_ReqVote_buf : map<nat,multiset<(nat,nat)>> := map f | f in Fs :: multiset{};                                   // harness
    assume domain(f_ReqVote_buf) == Fs;                                                                                  // harness
    // #########################################################################                                         

    // #########################################################################                                        
    // candidate's local state                                                                                         
    // #########################################################################                                      
    var c_term : map<nat, nat> := *;                                                                                     // code
    assume domain(c_term) == Cs;                                                                                         // harness

    var c_count   : map<nat, nat>  := map c | c in Cs :: 0;     assume domain(c_count) == Cs;                            // code
    var c_leader  : map<nat, bool> := map c | c in Cs :: false; assume domain(c_leader) == Cs;                           // code
    var c_success : map<nat, bool> := map c | c in Cs :: false; assume domain(c_success) == Cs;                          // code

    // last c worked with                                                                                                
    // var c_f  : map<nat,nat> := *;                                                                                    
    var c_f  : map<nat,nat> := *;                                                                                        // code
    assume domain(c_f) == Cs;                                                                                            // harness
    assume forall c,f :: c in Cs && f == c_f[c] ==> f in Fs;                                                             // harness

    // worklist of each follower's for loop                                                                             
    var c_WL : map<nat,set<nat>> := map c | c in Cs :: Fs;                                                               // code
    assume domain(c_WL) == Cs;                                                                                           // harness
    assume forall c,f :: c in Cs && f in c_WL[c] ==> f in Fs;                                                            // harness

    // message buffer -- ReqVoteResp(voteGranted : bool, term : nat)                                                   
    var c_ReqVoteResp_buf : map<nat,multiset<(bool,nat)>> := map c | c in Cs :: multiset{};                              // harness
    assume domain(c_ReqVoteResp_buf) == Cs;                                                                              // harness

    // #########################################################################                                         

    // #########################################################################                                        
    // history                                                                                                         
    // #########################################################################                                      
    // f_votes[f] = Term -> Candidate voted for                                                                      
    var f_votes : map<nat, map<nat, nat>> := *;                                                                          // code
    assume domain(f_votes) == Fs;                                                                                        // harness
    assume forall f,t :: f in Fs ==> (t in f_votes[f] <==> t in (set c | c in Cs :: c_term[c]));                         // annot
    assume forall f,c :: f in Fs && c in Cs && f_voted[f] ==> f_votes[f][c_term[c]] == c;                                // annot
    // #########################################################################                                     

    // #########################################################################                                    
    // global variables                                                                                            
    // #########################################################################                                  
    // program counter                                                                                           
    var f_pc : map<nat,Loc> := map f | f in Fs :: P0; assume domain(f_pc) == Fs;                                         // harness
    var c_pc : map<nat,Loc> := map c | c in Cs :: P0; assume domain(c_pc) == Cs;                                         // harness
    // ######################################################################### 

    // #########################################################################                    
    // sets                                                                                        
    // #########################################################################                  
    // k = Cs -> #{ f | f.term < c.term }                                                        
    var k : map<nat, nat> := map c | c in Cs :: len(Fs);                                                                 // code
    assume domain(k) == Cs;                                                                                              // harness
    // l = Cs -> #{ f | f.term >= c.term && f.votes[c.term] = c }                                                        
    var l : map<nat, nat> := map c | c in Cs :: 0;                                                                       // code
    assume domain(l) == Cs;                                                                                              // harness

    // o_t = Cs -> #{ msg | msg.to == c && msg.voteGranted == True }                                                     
    var o_t : map<nat, nat> := map c | c in Cs :: 0;                                                                     // code
    assume domain(o_t) == Cs;                                                                                            // harness
    // o_f = Cs -> #{ msg | msg.to == c && msg.voteGranted == False }                                                   
    var o_f : map<nat, nat> := map c | c in Cs :: 0;                                                                     // code
    assume domain(o_f) == Cs;                                                                                            // harness
    // #########################################################################                                       

    var main_WL := Cs + Fs;                                                                                              // code

    while main_WL != {}                                                                                                  // code
    // #########################################################################                                         
    // invariants                                                                                                       
    // #########################################################################                                       
    invariant                                                                                                            // annot
      ( domain(f_WL)              == Fs                                                                                  // annot
      && domain(f_ReqVote_buf)     == Fs                                                                                 // annot
      && domain(f_c)               == Fs                                                                                 // annot
      && domain(f_pc)              == Fs                                                                                 // annot
      && domain(f_term)            == Fs                                                                                 // annot
      && domain(f_vote)            == Fs                                                                                 // annot
      && domain(f_voted)           == Fs                                                                                 // annot

      && domain(c_ReqVoteResp_buf) == Cs                                                                                 // annot
      && domain(c_WL)              == Cs                                                                                 // annot
      && domain(c_count)           == Cs                                                                                 // annot
      && domain(c_f)               == Cs                                                                                 // annot
      && domain(c_leader)          == Cs                                                                                 // annot
      && domain(c_pc)              == Cs                                                                                 // annot

      && domain(k)                 == Cs                                                                                 // annot
      && domain(l)                 == Cs                                                                                 // annot
      && domain(f_votes)           == Fs                                                                                 // annot
      && domain(o_t)               == Cs                                                                                 // annot
      && domain(o_f)               == Cs                                                                                 // annot
      );                                                                                                                 
    invariant main_WL <= Fs + Cs;                                                                                        // annot
    invariant forall c,f :: c in Cs && f in c_WL[c] ==> f in Fs;                                                         // annot
    invariant forall f,c :: f in Fs && c in f_WL[f] ==> c in Cs;                                                         // annot
    invariant forall c,f :: c in Cs && f == c_f[c] ==> f in Fs;                                                          // annot
    invariant forall f,c :: f in Fs && c == f_c[f] ==> c in Cs;                                                          // annot
    invariant forall f,c :: f in Fs && f_vote[f] == c ==> c in Cs;                                                       // annot

    // ----------------------------------------------------------------------                                        

    invariant forall c :: c in Cs ==> k[c] >= 0;                                                                         // annot
    invariant forall c :: c in Cs ==> l[c] >= 0;                                                                         // annot
    invariant forall c :: c in Cs ==> c_count[c] >= 0;                                                                   // annot
    invariant forall c :: c in Cs ==> |Fs| >= k[c] + l[c];                                                               // annot

    // ----------------------------------------------------------------------                                         

    invariant forall f :: f in Fs && f !in main_WL ==> f_pc[f] == P2;                                                    // annot
    invariant forall c :: c in Cs && c !in main_WL ==> c_pc[c] == P3;                                                    // annot

    // ----------------------------------------------------------------------                                       

    invariant forall c :: c in Cs ==> o_t[c] >= 0;                                                                       // annot
    invariant forall c :: c in Cs ==> o_f[c] >= 0;                                                                       // annot
    invariant forall c :: c in Cs ==> |c_ReqVoteResp_buf[c]| >= o_t[c] + o_f[c];                                         // annot

    // ----------------------------------------------------------------------                                         

    invariant forall c :: c in Cs ==> l[c] >= o_t[c] + c_count[c];                                                       // annot

    invariant forall c :: c in Cs && c_leader[c] ==> c_count[c] * 2 > |Fs|;                                              // annot

    invariant forall f,t,c :: f in Fs && 0 < |f_ReqVote_buf[f]| && (t,c) in f_ReqVote_buf[f] ==> c in Cs && c_term[c] == t; // annot

    invariant forall f,t :: f in Fs ==> (t in f_votes[f] <==> t in (set c | c in Cs :: c_term[c]));                      // annot
    invariant forall f,c,t :: f in Fs && f_voted[f] && f_vote[f] == c && c_term[c] == t ==> f_votes[f][t] == c;          // annot

    // #########################################################################                                    

    decreases *                                                                                                    
    {                                                                                                              
      var p := *; assume p in main_WL;                                                                                   // harness

      if p in Fs {                                                                                                       // harness
        var f := p;                                                                                                      // harness
        assume f in Fs;                                                                                                  // harness

        if f_pc[f] == P0 {                                                                                               // harness
          /* for c in Cs:                                                                                                
               <P1>                                                                                                     
             done                                                                                                      
             <P2>                                                                                                     
           */                                                                                                        
          if f_WL[f] != {} {                                                                                             // code
            var c := *; assume c in f_WL[f];                                                                             // code

            f_c := f_c[f := c];                                                                                          // code
            f_pc := f_pc[f := P1];                                                                                       // harness
          } else {                                                                                                       // harness
            f_pc := f_pc[f := P2];                                                                                       // harness
          }
        } else if f_pc[f] == P1 {                                                                                        // harness
          if |f_ReqVote_buf[f]| > 0 {                                                                                    // harness
            /* ReqVote(t,pid) <- recv                                                                                    
             */                                                                                                         
            var t := *; var pid := *;                                                                                    // code
            assume (t,pid) in f_ReqVote_buf[f];                                                                          // code

            f_pid := f_pid[f := pid];                                                                                    // code

            f_ReqVote_buf := f_ReqVote_buf[f := f_ReqVote_buf[f] - multiset{(t,pid)}];                                   // harness

            /* if t > term:                                                                                              
                 term <- t                                                                                               
                 voted <- false                                                                                          
               end                                                                                                       
             */                                                                                                          
            if t > f_term[f] {                                                                                           // code
              f_term := f_term[f := t];                                                                                  // code
              f_voted := f_voted[f := false];                                                                            // code
            }                                                                                                            // code

            /* s <- (t >= term && (voted ==> vote == pid))                                                              
             */                                                                                                        
            var s := (t == f_term[f]) && (f_voted[f] ==> f_vote[f] == pid);                                              // code

            /* if s:                                                                                                     
                 voted    <- true                                                                                        
                 vote     <- pid                                                                                         
                 votes[t] <- vote                                                                                        
               end                                                                                                       
             */                                                                                                          
            var term := f_term[f];                                                                                       // code

            if s {                                                                                                       // code
              f_voted := f_voted[f := true];                                                                             // code
              f_vote := f_vote[f := pid];                                                                                // code

              assume k[pid] > 0;                                                                                         // annot
              k := k[pid := k[pid] - 1];                                                                                 // code
              l := l[pid := l[pid] + 1];                                                                                 // code

              f_votes := f_votes[f := f_votes[f][term := pid]];                                                          // code
            }                                                                                                            // code

            /* send pid ReqVoteResp(s,term)                                                                              
             */                                                                                                         

            if * {                                                                                                       // code
              c_ReqVoteResp_buf := c_ReqVoteResp_buf[pid := c_ReqVoteResp_buf[pid] + multiset{(s,term)}];                // code

              if s {                                                                                                     // code
                o_t := o_t[pid := o_t[pid] + 1];                                                                         // code
              } else {                                                                                                   // code
                o_f := o_f[pid := o_f[pid] + 1];                                                                         // code
              }                                                                                                          // code
            }                                                                                                            // code

            f_WL := f_WL[f := f_WL[f] - {f_c[f]}];                                                                       // harness

            f_pc := f_pc[f := P0];                                                                                       // harness
          }
        } else if f_pc[f] == P2 {                                                                                        // harness
          /* exit(0)                                                                                                     
           */                                                                                                           
          main_WL := main_WL - {f};                                                                                      // harness
        }                                                                                                                
      }                                                                                                                 
      else if p in Cs {                                                                                                  // harness
        var c := p;                                                                                                      // harness
        assume c in Cs;                                                                                                  // harness

        if c_pc[c] == P0 {                                                                                               // harness
          /* for f in Fs:                                                                                                
               <P1>                                                                                                      
               <P2>                                                                                                      
             done                                                                                                        
             <P3>                                                                                                        
           */                                                                                                            
          if c_WL[c] != {} {                                                                                             // code
            var f := *; assume f in c_WL[c]; assume f in Fs;                                                             // code
            c_f := c_f[c := f];                                                                                          // code
            c_pc := c_pc[c := P1];                                                                                       // harness
          } else {                                                                                                       // harness
            c_pc := c_pc[c := P3];                                                                                       // harness
          }                                                                                                              
        } else if c_pc[c] == P1 {                                                                                        // harness
          /* send f ReqVote(term,c)                                                                                      
           */                                                                                                           
          var f := c_f[c];                                                                                               // code
          var term := c_term[c];                                                                                         // code

          f_ReqVote_buf := f_ReqVote_buf[f := f_ReqVote_buf[f] + multiset{(term,c)}];                                    // code
          c_pc := c_pc[c := P2];                                                                                         // harness
        } else if c_pc[c] == P2 {                                                                                        // harness
          if * {                                                                                                         // code
            if |c_ReqVoteResp_buf[c]| > 0 {                                                                              // harness
              /* ReqVoteResp(s,t) <- recvTO(f)                                                                           
               */                                                                                                        
              var s := *; var t := *;                                                                                    // code
              assume (s,t) in c_ReqVoteResp_buf[c];                                                                      // code

              c_ReqVoteResp_buf := c_ReqVoteResp_buf[c := c_ReqVoteResp_buf[c] - multiset{(s,t)}];                       // harness

              if s {                                                                                                     // code
                assume o_t[c] > 0;                                                                                       // code
                o_t := o_t[c := o_t[c] - 1];                                                                             // code
              } else {                                                                                                   // code
                assume o_f[c] > 0;                                                                                       // code
                o_f := o_f[c := o_f[c] - 1];                                                                             // code
              }                                                                                                          // code

              /* if s:                                                                                                  
                   count <- count + 1                                                                                  
                 end                                                                                                  
               */                                                                                                    

              if s {                                                                                                     // code
                c_count := c_count[c := c_count[c] + 1];                                                                 // code
              }                                                                                                          // code

              c_WL := c_WL[c := c_WL[c] - {c_f[c]}];                                                                     // harness
              c_pc := c_pc[c := P0];                                                                                     // harness
            }
          } else {                                                                                                       // harness
            // timeout                                                                                                   // harness
            c_WL := c_WL[c := c_WL[c] - {c_f[c]}];                                                                       // harness
            c_pc := c_pc[c := P0];                                                                                       // harness
          }
        } else if c_pc[c] == P3 {                                                                                        // harness
          /* if 2 x count > |Fs|:                                                                                        
               leader <- true                                                                                            
             end                                                                                                         
           */                                                                                                            
          if c_count[c] * 2 > |Fs| {                                                                                     // code
            c_leader := c_leader[c := true];                                                                             // code
          }                                                                                                              // code

          main_WL := main_WL - {c};                                                                                      // harness
        }                                                                                                                
      }                                                                                                                 
    }                                                                                                                  

    assert forall c :: c in Cs && c_leader[c] ==> l[c] * 2 > |Fs|;                                                       // annot

    // this is the reasoning about cardinalities                                                                         
    assume(forall c1,c2 ::                                                                                                                         // annot
      (c1 in Cs && c2 in Cs && l[c1] * 2 > |Fs| && l[c2] * 2 > |Fs|) ==>                                                                           // annot
      (exists f :: f in Fs && f_term[f] == c_term[c1] && f_term[f] == c_term[c2] && f_vote[f] == c1 && f_vote[f] == c2) ||                         // annot
      (exists f :: f in Fs && f_term[f] == c_term[c1] && f_term[f] >  c_term[c2] && f_vote[f] == c1 && f_votes[f][c_term[c2]] == c2) ||            // annot
      (exists f :: f in Fs && f_term[f] > c_term[c1] && f_term[f] > c_term[c2] && f_votes[f][c_term[c1]] == c1 && f_votes[f][c_term[c2]] == c2));  // annot

    assert (forall c1, c2 :: (c0 in Cs && c2 in Cs && c_term[c1] == c_term[c2] && c_leader[c1] && c_leader[c2] ==> c1 == c2));                     // annot
  }                                                                                                                     
}                                                                                                                      
