module RaftLeaderElection {
  function domain<U,V>(m: map<U,V>) : set<U>
    ensures domain(m) == set u : U | u in m :: u;
    ensures forall u :: u in domain(m) ==> u in m;
  {
    set u : U | u in m :: u
  }

  function check_multi_map<U1,U2,V>(m: map<U1,map<U2,V>>, s1: set<U1>, s2: set<U2>) : bool
  {
    domain(m) == s1 && (forall u1 :: u1 in m ==> domain(m[u1]) == s2)
  }

  function method len(s: set<nat>) : (l: nat)
    ensures l == |s|
  {
    |s|
  }

  datatype Loc = P0 | P1 | P2 | P3

  method RaftLeaderElection
    ( Fs : set<nat> // followers
    , Cs : set<nat> // candidates
    )
    requires |Cs| > 0
    requires |Fs| >= 2
    decreases *
  {
    // #########################################################################
    // follower's local state
    // #########################################################################
    var f_currentTerm : map<nat, nat>  := *; assume (forall f :: f in Fs <==> f in f_currentTerm);
    var f_voted       : map<nat, bool> := map f | f in Fs :: false;
    var f_votedFor    : map<nat, nat>  := *; assume (forall f :: f in Fs <==> f in f_votedFor); assume (forall f,c :: f in Fs && c == f_votedFor[f] ==> c in Cs);
    var f_voteGranted : map<nat, bool> := map f | f in Fs :: false;

    // last c worked with
    var f_c  : map<nat,nat> := *; assume (forall f :: f in Fs <==> f in f_c); assume (forall f,c :: f in Fs && c == f_c[f] ==> c in Cs);
    // worklist of each follower's for loop
    var f_WL : map<nat,set<nat>> := map f | f in Fs :: (set c | c in Cs :: c);
    // #########################################################################

    // #########################################################################
    // candidate's local state
    // #########################################################################
    var c_currentTerm : map<nat, nat>  := *; assume (forall c :: c in Cs <==> c in c_currentTerm);
    var c_count       : map<nat, nat>  := map c | c in Cs :: 0;
    var c_isLeader    : map<nat, bool> := map c | c in Cs :: false;
    var c_success     : map<nat, bool> := map c | c in Cs :: false;
    // #########################################################################

    // #########################################################################
    // history
    // #########################################################################
    // f_votedFors[f] = Term -> Candidate voted for
    var f_votedFors : map<nat, map<nat, nat>> := *;
    assume (domain(f_votedFors) == Fs);
    assume (forall f,t :: f in Fs ==> (t in f_votedFors[f] <==> t in (set c | c in Cs :: c_currentTerm[c])));
    assume (forall f,c :: f in Fs && c in Cs && f_voted[f] ==> f_votedFors[f][c_currentTerm[c]] == c);
    // #########################################################################

    // #########################################################################
    // global variables
    // #########################################################################
    // program counter
    var PC : map<nat,Loc> := map f | f in Fs :: P0;
    // #########################################################################

    assume (forall f, c :: f in Fs && c in Cs ==> f_currentTerm[f] < c_currentTerm[c]);

    // #########################################################################
    // sets
    // #########################################################################

    // k = Cs -> #{ f | f.term < c.term }
    var k : map<nat, nat> := map c | c in Cs :: len(Fs);
    // l = Cs -> #{ f | f.term = c.term && f.votedFor = c }
    var l : map<nat, nat> := map c | c in Cs :: 0;
    // m = Cs -> #{ f | f.term > c.term && f_votedFors[f][c.term] = c }
    var m : map<nat, nat> := map c | c in Cs :: 0;

    // o : in-flight messages to c that has voteGranted == True
    // o_t = Cs -> #{ msg | msg.to == c && msg.voteGranted == True }
    var o_t : map<nat, nat> := map c | c in Cs :: 0;
    // o_f = Cs -> #{ msg | msg.to == c && msg.voteGranted == False }
    var o_f : map<nat, nat> := map c | c in Cs :: 0;
    // s = Cs -> #{ f | PC[f] == P2 && f_c[f] == c }
    var s : map<nat, nat> := map c | c in Cs :: 0;

    // #########################################################################

    var WL : set<nat> := set f | f in Fs :: f;
    while WL != {}
    invariant Fs == old(Fs);
    invariant Cs == old(Cs);
    invariant m == old(m);
    invariant c_isLeader == old(c_isLeader);
    invariant c_currentTerm == old(c_currentTerm);
    invariant
      ( domain(f_voted) == Fs
      && domain(f_votedFor) == Fs
      && domain(f_voteGranted) == Fs
      && domain(f_currentTerm) == Fs
      && domain(c_count) == Cs
      && domain(PC) == Fs
      && domain(f_WL) == Fs
      && domain(f_c) == Fs
      && domain(c_success) == Cs
      && domain(c_currentTerm) == Cs
      && domain(k) == Cs && domain(l) == Cs && domain(m) == Cs
      && domain(o_t) == Cs && domain(o_f) == Cs && domain(s) == Cs
      && domain(f_votedFors) == Fs
      );
    invariant (forall f,c :: f in Fs && c == f_votedFor[f] ==> c in Cs);
    invariant (forall f,c :: f in f_WL && c in f_WL[f] ==> c in Cs);
    invariant (forall f,c :: f in Fs && c == f_c[f] ==> c in Cs);
    invariant (forall f :: f in WL ==> f in Fs);
    invariant (forall c :: c in Cs ==> k[c] >= 0);
    invariant (forall c :: c in Cs ==> l[c] >= 0);
    invariant (forall c :: c in Cs ==> m[c] >= 0);
    invariant (forall c :: c in Cs ==> o_t[c] >= 0);
    invariant (forall c :: c in Cs ==> o_f[c] >= 0);
    invariant (forall c :: c in Cs ==> s[c] >= 0);
    invariant (forall c :: c in Cs ==> c_count[c] >= 0);
    invariant (forall c :: c in Cs ==> |Fs| == k[c] + l[c] + m[c]);

    // invariant (forall f :: f in Fs && old(PC[f]) == P0 ==> PC[f] == P0 || PC[f] == P1);
    // invariant (forall f :: f in Fs && old(PC[f]) == P1 ==> PC[f] == P1 || PC[f] == P2);
    // invariant (forall f :: f in Fs && old(PC[f]) == P2 ==> PC[f] == P2 || PC[f] == P1 || PC[f] == P3);
    // invariant (forall f :: f in Fs && old(PC[f]) == P3 ==> PC[f] == P3);

    invariant (forall c :: c in Cs ==> o_t[c] + o_f[c] <= s[c]);
    invariant (forall c :: c in Cs ==> c_count[c] + o_t[c] <= l[c] + m[c]);

    invariant (forall f :: f in (Fs - WL) ==> PC[f] == P3);

    invariant (forall f,t :: f in Fs ==> (t in f_votedFors[f] <==> t in (set c | c in Cs :: c_currentTerm[c])));
    invariant (forall f,c :: f in Fs && f_voted[f] && c == f_votedFor[f] ==> f_votedFors[f][c_currentTerm[c]] == c);
    decreases *
    {
      // pick a follower from the worklist
      var f := *;
      assume f in WL;

      if PC[f] == P0 {
        PC := PC[f := P1];

      } else if PC[f] == P1 {
        // ----------------------------------------------------------------------
        // atomic block of the follower
        // ----------------------------------------------------------------------

        // pick a fresh candidate from the follower's worklist
        var c := *;
        assume c in f_WL[f];

        // note down the picked candidate
        f_c := f_c[f := c];

        // follower receives RequestVote from candidate
        var term : nat := c_currentTerm[c];

        if term > f_currentTerm[f] {
          f_currentTerm := f_currentTerm[f := term];
          f_voted       := f_voted[f := false];
        }

        // store the previous values
        var currentTerm' : nat := f_currentTerm[f];
        var voted' : bool      := f_voted[f];
        var c' : nat           := f_votedFor[f];

        var success := term >= currentTerm' && (voted' ==> c' == c);
        f_voteGranted := f_voteGranted[f := success];

        // if we're voting for c now
        // then decrement the cardinality of k[c] and increment l[c]
        if f_voteGranted[f] {
          assume(k[c] > 0);
          k := k[c := k[c] - 1];
          l := l[c := l[c] + 1];

          f_votedFors := f_votedFors[f := f_votedFors[f][term := c]];

          // send RequestVoteResponse msg with (success : True) to c
          o_t := o_t[c := o_t[c] + 1];

          // if the follower have voted for c' before, but now voted for someone else
          // then decrement the cardinality of l[c'] and increment m[c']
          if voted' {
            assume(l[c'] > 0);
            l := l[c' := l[c'] - 1];
            m := m[c' := m[c'] + 1];
          }
        } else {
          o_f := o_f[c := o_f[c] + 1];
        }

        // if vote is yes, then update the local state
        if f_voteGranted[f] {
          f_voted       := f_voted[f := true];
          f_votedFor    := f_votedFor[f := c];
        }

        // move to the candidate's atomic block
        PC := PC[f := P2];

        s := s[c := s[c] + 1];

        // remove the candidate from the follower's worklist
        f_WL := f_WL[f := f_WL[f] - {c}];

      } else if PC[f] == P2 {
        // ----------------------------------------------------------------------
        // atomic block of the candidate
        // ----------------------------------------------------------------------

        var c := f_c[f];

        c_success := c_success[c := f_voteGranted[f]];

        if c_success[c] {
          // remove the RequestVoteResponse msg with (success : True) from the queue
          assume o_t[c] > 0;
          o_t := o_t[c := o_t[c] - 1];

          c_count := c_count[c := c_count[c] + 1];
        } else {
          assume o_f[c] > 0;
          o_f := o_f[c := o_f[c] - 1];
        }

        assume(s[c] > 0);
        s := s[c := s[c] - 1];

        // if the follower's work list is empty, be done with it
        if f_WL[f] == {} {
          // move to the end
          PC := PC[f := P3];
          WL := WL - {f};
        } else {
          // move to the follower's first atomic block
          PC := PC[f := P1];
        }
      }

    }

    assert(forall f :: f in Fs ==> PC[f] == P3);

    assume(forall c :: c in Cs ==> |(set f | f in Fs && PC[f] == P2 && f_c[f] == c :: f)| == s[c]);

    assert(forall c :: c in Cs ==> s[c] == 0);
    assert(forall c :: c in Cs ==> o_t[c] == 0);

    assert(forall c :: c in Cs ==> ! c_isLeader[c]);

    assert(forall c :: c in Cs ==> c_count[c] <= l[c] + m[c]);

    var WL_Cs := Cs;
    while WL_Cs != {}
    invariant (forall c :: c in WL_Cs ==> c in Cs);
    invariant (domain(c_isLeader) == Cs);
    invariant (c_count == old(c_count));
    invariant (forall c :: c in WL_Cs ==> ! c_isLeader[c]); // why should I supply this ?
    invariant (forall c :: c in (Cs - WL_Cs) && c_isLeader[c] ==> c_count[c] * 2 > |Fs|);
    decreases WL_Cs
    {
      var c := *;
      assume c in WL_Cs;

      if c_count[c] * 2 > |Fs| {
        c_isLeader := c_isLeader[c := true];
      }
      
      WL_Cs := WL_Cs - {c};
    }

    assume(forall c1,c2 ::
      (c1 in Cs && c2 in Cs && (l[c1] + m[c1]) * 2 > |Fs| && (l[c2] + m[c1]) * 2 > |Fs|) ==>
      (exists f :: f in Fs
      && f_currentTerm[f] == c_currentTerm[c1]
      && f_currentTerm[f] == c_currentTerm[c2]
      && f_votedFor[f] == c1
      && f_votedFor[f] == c2) ||
      (exists f :: f in Fs
      && f_currentTerm[f] == c_currentTerm[c1]
      && f_currentTerm[f] >  c_currentTerm[c2]
      && f_votedFor[f]    == c1
      && f_votedFors[f][c_currentTerm[c2]] == c2) ||
      (exists f :: f in Fs
      && f_currentTerm[f] > c_currentTerm[c1]
      && f_currentTerm[f] > c_currentTerm[c2]
      && f_votedFors[f][c_currentTerm[c1]] == c1
      && f_votedFors[f][c_currentTerm[c2]] == c2));
     
    assert (forall c1, c2 :: 
      (c1 in Cs && c2 in Cs && c_currentTerm[c1] == c_currentTerm[c2] && c_isLeader[c1] && c_isLeader[c2] ==> c1 == c2)
    );
      
  }

}

