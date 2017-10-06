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

  method RaftLeaderElection
    ( Fs : set<nat> // followers
    , Cs : set<nat> // candidates
    )
    requires |Cs| > 0;
    requires |Fs| >= 2;
    requires Fs !! Cs;
    decreases *
  {
    // #########################################################################
    // follower's local state
    // #########################################################################
    var f_term : map<nat, nat>  := *;
    assume domain(f_term) == Fs;

    var f_voted : map<nat, bool> := map f | f in Fs :: false;
    assume domain(f_voted) == Fs;

    var f_vote : map<nat, nat>  := *;
    assume domain(f_vote) == Fs;
    assume forall f,c :: f in Fs && c == f_vote[f] ==> c in Cs;

    // last c worked with
    var f_c  : map<nat,nat> := *;
    assume domain(f_c) == Fs;
    assume forall f,c :: f in Fs && c == f_c[f] ==> c in Cs;

    var f_s : map<nat, bool>  := *;
    assume domain(f_s) == Fs;

    var f_pid : map<nat, nat>  := *;
    assume domain(f_pid) == Fs;
    assume forall f,c :: f in Fs && c == f_pid[f] ==> c in Cs;

    var f_t : map<nat, nat>  := *;
    assume domain(f_t) == Fs;

    // worklist of each follower's for loop
    var f_WL : map<nat,set<nat>> := map f | f in Fs :: Cs;
    assume domain(f_WL) == Fs;
    assume forall f,c :: f in Fs && c in f_WL[f] ==> c in Cs;

    // message buffer -- ReqVote(term : nat, pid : nat)
    var f_ReqVote_buf : map<nat,seq<(nat,nat)>> := map f | f in Fs :: [];
    assume forall f,i,c :: f in Fs && 0 <= i < |f_ReqVote_buf[f]| && c == f_ReqVote_buf[f][i].1 ==> c in Cs;
    // #########################################################################

    // #########################################################################
    // candidate's local state
    // #########################################################################
    var c_term : map<nat, nat> := *;
    assume domain(c_term) == Cs;

    var c_count   : map<nat, nat>  := map c | c in Cs :: 0;     assume domain(c_count) == Cs;
    var c_leader  : map<nat, bool> := map c | c in Cs :: false; assume domain(c_leader) == Cs;
    var c_success : map<nat, bool> := map c | c in Cs :: false; assume domain(c_success) == Cs;

    // last c worked with
    // var c_f  : map<nat,nat> := *;
    var c_f  : map<nat,nat> := *;
    assume domain(c_f) == Cs;
    assume forall c,f :: c in Cs && f == c_f[c] ==> f in Fs;

    var c_s : map<nat, bool>  := *;
    assume domain(c_s) == Cs;

    // worklist of each follower's for loop
    var c_WL : map<nat,set<nat>> := map c | c in Cs :: Fs;
    assume domain(c_WL) == Cs;
    assume forall c,f :: c in Cs && f in c_WL[c] ==> f in Fs;

    // message buffer -- ReqVoteResp(voteGranted : bool, term : nat)
    var c_ReqVoteResp_buf : map<nat,seq<(bool,nat)>> := map c | c in Cs :: [];
    assume domain(c_ReqVoteResp_buf) == Cs;

    // #########################################################################

    // #########################################################################
    // history
    // #########################################################################
    // f_votes[f] = Term -> Candidate voted for
    var f_votes : map<nat, map<nat, nat>> := *;
    assume domain(f_votes) == Fs;
    assume forall f,t :: f in Fs ==> (t in f_votes[f] <==> t in (set c | c in Cs :: c_term[c]));
    assume forall f,c :: f in Fs && c in Cs && f_voted[f] ==> f_votes[f][c_term[c]] == c;
    // #########################################################################

    // #########################################################################
    // global variables
    // #########################################################################
    // program counter
    var f_pc : map<nat,Loc> := map f | f in Fs :: P0; assume domain(f_pc) == Fs;
    var c_pc : map<nat,Loc> := map c | c in Cs :: P0; assume domain(c_pc) == Cs;
    // #########################################################################

    // #########################################################################
    // sets
    // #########################################################################
    // k = Cs -> #{ f | f.term < c.term }
    var k : map<nat, nat> := map c | c in Cs :: len(Fs);
    assume domain(k) == Cs;
    // l = Cs -> #{ f | f.term >= c.term && f.votes[c.term] = c }
    var l : map<nat, nat> := map c | c in Cs :: 0;
    assume domain(l) == Cs;

    // o_t = Cs -> #{ msg | msg.to == c && msg.voteGranted == True }
    var o_t : map<nat, nat> := map c | c in Cs :: 0;
    assume domain(o_t) == Cs;
    // o_f = Cs -> #{ msg | msg.to == c && msg.voteGranted == False }
    var o_f : map<nat, nat> := map c | c in Cs :: 0;
    assume domain(o_f) == Cs;
    // #########################################################################

    // #########################################################################
    // sequencing
    // #########################################################################
    var f_p2_is_done : map<nat,bool> := map f | f in Fs :: false;
    assume domain(f_p2_is_done) == Fs;
    // #########################################################################

    var main_WL := Cs + Fs;

    while main_WL != {}
    // #########################################################################
    // invariants
    // #########################################################################
    free invariant
      ( domain(f_WL) == Fs
      && domain(f_ReqVote_buf) == Fs
      && domain(f_c) == Fs
      && domain(f_pc) == Fs
      && domain(f_pid) == Fs
      && domain(f_s) == Fs
      && domain(f_term) == Fs
      && domain(f_t) == Fs
      && domain(f_vote) == Fs
      && domain(f_voted) == Fs
      && domain(f_p2_is_done) == Fs
      
      && domain(c_ReqVoteResp_buf) == Cs
      && domain(c_WL) == Cs
      && domain(c_count) == Cs
      && domain(c_f) == Cs
      && domain(c_s) == Cs
      && domain(c_leader) == Cs
      && domain(c_pc) == Cs

      && domain(k) == Cs
      && domain(l) == Cs
      && domain(f_votes) == Fs
      && domain(o_t) == Cs
      && domain(o_f) == Cs
      );
    free invariant main_WL <= Fs + Cs;
    free invariant forall c,f :: c in Cs && f in c_WL[c] ==> f in Fs;
    free invariant forall f,c :: f in Fs && c in f_WL[f] ==> c in Cs;
    free invariant forall c,f :: c in Cs && f == c_f[c] ==> f in Fs;
    free invariant forall f,c :: f in Fs && c == f_c[f] ==> c in Cs;
    free invariant forall f,c :: f in Fs && c == f_pid[f] ==> c in Cs;
    free invariant forall f,i,c :: f in Fs && 0 <= i < |f_ReqVote_buf[f]| && c == f_ReqVote_buf[f][i].1 ==> c in Cs;

    // ----------------------------------------------------------------------

    free invariant forall c :: c in Cs ==> k[c] >= 0;
    free invariant forall c :: c in Cs ==> l[c] >= 0;
    free invariant forall c :: c in Cs ==> c_count[c] >= 0;
    free invariant forall c :: c in Cs ==> |Fs| >= k[c] + l[c];

    // ----------------------------------------------------------------------

    free invariant forall f :: f in Fs && f !in main_WL ==> f_pc[f] == P4;
    free invariant forall c :: c in Cs && c !in main_WL ==> c_pc[c] == P4;

    // ----------------------------------------------------------------------

    free invariant forall c :: c in Cs ==> o_t[c] >= 0;
    free invariant forall c :: c in Cs ==> o_f[c] >= 0;
    free invariant forall c :: c in Cs ==> |c_ReqVoteResp_buf[c]| >= o_t[c] + o_f[c];

    // ----------------------------------------------------------------------

    invariant forall f,c :: f in Fs && f_pc[f] == P3 && f_pid[f] == c ==> c_pc[c] == P1 || c_pc[c] == P2;

    // invariant forall f,c :: f in Fs && f_pc[f] == P2 && f_pid[f] == c && c_pc[c] == P2 ==> true;
    // invariant forall f,c :: f in Fs && f_pc[f] == P3 && f_pid[f] == c && c_pc[c] == P2 ==> true;
    // invariant forall f,c :: f in Fs && f_pc[f] == P2 && f_pid[f] == c && c_pc[c] == P3 ==> true;
    // invariant forall f,c :: f in Fs && f_pc[f] == P3 && f_pid[f] == c && c_pc[c] == P3 ==> true;
    // invariant forall c :: c in Cs ==> l[c] >= o_t[c] + c_count[c];

    // invariant forall f,c :: f in Fs && f_p2_is_done[f] && f_s[f] && f_pid[f] == c ==> l[c] > o_t[c];
    // invariant forall c :: c in Cs ==> l[c] >= o_t[c] + c_count[c];

    // invariant forall c :: c in Cs && c_leader[c] ==> c_count[c] * 2 > |Fs|;

    // invariant forall f,t :: f in Fs ==> (t in f_votes[f] <==> t in (set c | c in Cs :: c_term[c]));
    // invariant forall f,c :: f in Fs && c in Cs && f_voted[f] ==> f_votes[f][c_term[c]] == c;

    // #########################################################################

    decreases *
    {
      var p := *; assume p in main_WL;

      if p in Fs {
        var f := p;
        assume f in Fs;

        if f_pc[f] == P0 {
          /* for c in Cs:
               <P1>
               <P2>
             done
           */
          if f_WL[f] != {} {
            var c := *; assume c in f_WL[f];
            f_p2_is_done := f_p2_is_done[f := false];

            f_c := f_c[f := c];
            f_pc := f_pc[f := P1];
          } else {
            f_pc := f_pc[f := P4];
          }
        } else if f_pc[f] == P1 {
          /* ReqVote(t,pid) <- recv
           */
          if f_ReqVote_buf[f] != [] {
            var (t,pid) := f_ReqVote_buf[f][0];
            assume pid in Cs;
            
            f_ReqVote_buf := f_ReqVote_buf[f := f_ReqVote_buf[f][1..]];
            
            f_t   := f_t[f := t];
            f_pid := f_pid[f := pid];

            f_pc := f_pc[f := P2];
          }
        } else if f_pc[f] == P2 {
          /* if t > term:
               term <- t
               voted <- false
             end
             
             s <- (t >= term && (voted ==> vote == pid))

             if s:
               voted    <- true
               vote     <- pid
               votes[t] <- vote
             end
           */
          var t := f_t[f];
          var pid := f_pid[f];
          var term := f_term[f];
          
          if t > f_term[f] {
            f_term := f_term[f := t];
            f_voted := f_voted[f := false];
          }

          var s := t == f_term[f] && (f_voted[f] ==> f_vote[f] == pid);
          f_s := f_s[f := s];

          if s {
            f_voted := f_voted[f := true];
            f_vote := f_vote[f := pid];

            assume k[pid] > 0;
            k := k[pid := k[pid] - 1];
            l := l[pid := l[pid] + 1];
            
            f_votes := f_votes[f := f_votes[f][term := pid]];
          }

          f_p2_is_done := f_p2_is_done[f := true];
          f_pc := f_pc[f := P3];
        } else if f_pc[f] == P3 {
          /* send pid ReqVoteResp(s,term)
           */
          var pid := f_pid[f];
          var s := f_s[f];
          var term := f_term[f];
              
          c_ReqVoteResp_buf := c_ReqVoteResp_buf[pid := c_ReqVoteResp_buf[pid] + [(s,term)]];

          if s {
            o_t := o_t[pid := o_t[pid] + 1];
          } else {
            o_f := o_f[pid := o_f[pid] + 1];
          }

          f_WL := f_WL[f := f_WL[f] - {f_c[f]}];

          f_pc := f_pc[f := P0];
        } else if f_pc[f] == P4 {
          /* exit(0)
           */
          main_WL := main_WL - {f};
        }
      }
      else if p in Cs {
        var c := p;
        assume c in Cs;
        
        if c_pc[c] == P0 {
          /* for f in Fs:
               <P1>
               <P2>
             done
           */
          if c_WL[c] != {} {
            var f := *; assume f in c_WL[c]; assume f in Fs;
            c_f := c_f[c := f];
            c_pc := c_pc[c := P1];
          } else {
            c_pc := c_pc[c := P4];
          }
        } else if c_pc[c] == P1 {
          /* send f ReqVote(term,c)
           */
          var f := c_f[c];
          var term := c_term[c];

          f_ReqVote_buf := f_ReqVote_buf[f := f_ReqVote_buf[f] + [(term,c)]];
          c_pc := c_pc[c := P2];
        } else if c_pc[c] == P2 {
          /* ReqVoteResp(s,t) <- recvTO(f)
           */
          if c_ReqVoteResp_buf[c] != [] {
            var (s,t) := c_ReqVoteResp_buf[c][0];
            c_ReqVoteResp_buf := c_ReqVoteResp_buf[c := c_ReqVoteResp_buf[c][1..]];

            c_s := c_s[c := s];

            if s {
              assume o_t[c] > 0;
              o_t := o_t[c := o_t[c] - 1];
            } else {
              assume o_f[c] > 0;
              o_f := o_f[c := o_f[c] - 1];
            }
            
            c_pc := c_pc[c := P3];
          }
        } else if c_pc[c] == P3 {
          /* if s:
               count <- count + 1
             end
           */
          var s := c_s[c];

          if s {
            c_count := c_count[c := c_count[c] + 1];
          }

          c_WL := c_WL[c := c_WL[c] - {c_f[c]}];
          c_pc := c_pc[c := P0];
        } else if c_pc[c] == P4 {
          /* if 2 x count > |Fs|:
               leader <- true
             end
           */
          if c_count[c] * 2 > |Fs| {
            c_leader := c_leader[c := true];
          }

          main_WL := main_WL - {c};
        }
      }
    }

    // assert forall c :: c in Cs && c_leader[c] ==> l[c] * 2 > |Fs|;

    // // this is the reasoning about cardinalities
    // assume(forall c1,c2 ::
    //   (c1 in Cs && c2 in Cs && l[c1] * 2 > |Fs| && l[c2] * 2 > |Fs|) ==>
    //   (exists f :: f in Fs
    //   && f_term[f] == c_term[c1]
    //   && f_term[f] == c_term[c2]
    //   && f_vote[f] == c1
    //   && f_vote[f] == c2) ||
    //   (exists f :: f in Fs
    //   && f_term[f] == c_term[c1]
    //   && f_term[f] >  c_term[c2]
    //   && f_vote[f] == c1
    //   && f_votes[f][c_term[c2]] == c2) ||
    //   (exists f :: f in Fs
    //   && f_term[f] > c_term[c1]
    //   && f_term[f] > c_term[c2]
    //   && f_votes[f][c_term[c1]] == c1
    //   && f_votes[f][c_term[c2]] == c2));

    // assert (forall c1, c2 :: 
    //   (c1 in Cs && c2 in Cs && c_term[c1] == c_term[c2] && c_leader[c1] && c_leader[c2] ==> c1 == c2)
    // );
  }
}
