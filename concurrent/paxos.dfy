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

  datatype Loc = P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7

  datatype Msg_Acc =
      Prepare(no: int)
    | Accept(no: int, val: int)

  datatype Msg_Phase =
      OneB
    | TwoB

  datatype Msg_Prop = Value(no: int, val: int, phase: Msg_Phase)

  method PaxosSingle
    ( Ps : set<nat>
    , As : set<nat>
    )
    requires |Ps| > 0
    requires |As| >= 2
    requires Ps !! As
    decreases *
  {
    // #########################################################################
    // Proposer local state
    // #########################################################################

    // proposed value of the proposer
    var Prop_V : map<nat, int> := *;
    assume domain(Prop_V) == Ps;

    // proposal number of the proposal
    var Prop_N : map<nat, nat> := *;
    assume domain(Prop_N) == Ps;
    assume forall p :: p in Ps ==> Prop_N[p] > 0;
    assume forall p1,p2 :: p1 in Ps && p2 in Ps ==> (p1 == p2 <==> Prop_N[p1] == Prop_N[p2]);

    // max seen proposal number
    var Prop_Max : map<nat, int> := map p | p in Ps :: (-1);

    // proposer's program counter
    var Prop_PC  : map<nat, Loc>  := map p | p in Ps :: P0;

    // heard of count
    var Prop_HO       : map<nat, nat>  := map p | p in Ps :: 0;
    var Prop_HO2      : map<nat, nat>  := map p | p in Ps :: 0;

    // is proposer in the second phase ?
    var Prop_Ready    : map<nat, bool> := map p | p in Ps :: false;

    var Prop_Decided  : map<nat, bool> := map p | p in Ps :: false;

    var Prop_a   : map<nat, nat> := *;
    assume domain(Prop_a) == Ps;
    assume forall p,a :: p in Ps && a == Prop_a[p] ==> a in As;

    var Prop_WL  : map<nat, set<nat>> := map p | p in Ps :: As;
    var Prop_WL2 : map<nat, set<nat>> := map p | p in Ps :: As;

    // #########################################################################
    // Acceptor State
    // #########################################################################

    // value of the highest numbered proposal accepted by the acceptor
    var Acc_MaxV : map<nat, int> := *;
    assume domain(Acc_MaxV) == As;

    // highest accepted proposal's number
    var Acc_Max_Accepted_N : map<nat, int> := map a | a in As :: (-1);

    // max proposal number seen
    var Acc_Max_Seen_N : map<nat, int> := map a | a in As :: (-1);

    // all accepted proposal numbers
    var Acc_Ns  : map<nat, set<int>> := map a | a in As :: {};

    // acceptor's program counter
    var Acc_PC  : map<nat, Loc> := map a | a in As :: P0;

    // #########################################################################
    // Message soups
    // #########################################################################

    var Acc_Soup  : map<nat, multiset<(nat,Msg_Acc)>>  := map a | a in As :: multiset{};
    var Prop_Soup : map<nat, multiset<(nat,Msg_Prop)>> := map p | p in Ps :: multiset{};

    var Acc_Soup_Hist  : map<nat, set<(nat,Msg_Acc)>>  := map a | a in As :: {}; 
    var Prop_Soup_Hist : map<nat, set<(nat,Msg_Prop)>> := map p | p in Ps :: {};

    // #########################################################################
    // Message histories
    // #########################################################################

    var OneA_Hist : set<nat>                     := {};
    var OneB_Hist : map<nat, set<(int,int,int)>> := map a | a in As :: {};
    var TwoA_Hist : set<(int,int)>               := {};
    var TwoB_Hist : map<nat, set<(int,int)>>     := map a | a in As :: {};

    // #########################################################################
    // Other history variables
    // #########################################################################

    // (a,n) in Joined_Rnd ==> a has seen a proposal msg numbered n
    var Joined_Rnd : map<nat, set<int>> := map a | a in As :: {};

    // #########################################################################
    // Set cardinalities
    // #########################################################################

    // k[p] := #{a in A | p.n in a.ns}
    // i.e. number of acceptors have accepted p's proposal
    var k : map<nat, nat> := map p | p in Ps :: 0;

    // k_pending[p] := #{(a,Value(no,val,TwoB)) in Prop_Soup[p] | no == p.n}
    // i.e. number of messages in flight that will increment the `p.ho2` 
    // variable upon receive
    var k_pending : map<nat, nat> := map p | p in Ps :: 0;

    // l[p] := #{a in A | p.n !in a.ns && a.max <= p.n}
    // i.e. number of acceptors may accept p's proposal
    var l : map<nat, nat> := map p | p in Ps :: len(As);

    // m[p] := #{a in A | p.n !in a.ns && a.max > p.n}
    // i.e. number of acceptors will never accept p's proposal
    var m : map<nat, nat> := map p | p in Ps :: 0;

    // #########################################################################

    var WL_main := Ps + As;

    while WL_main != {}
    invariant WL_main <= Ps + As;
    invariant
        ( domain(Acc_Ns)         == As
        && domain(Acc_Max_Seen_N)        == As
        && domain(Acc_Max_Accepted_N)          == As
        && domain(Acc_Soup)       == As
        && domain(Acc_MaxV)          == As 

        && domain(Prop_Decided)   == Ps
        && domain(Prop_HO)        == Ps
        && domain(Prop_HO2)       == Ps
        && domain(Prop_Max)       == Ps
        && domain(Prop_N)         == Ps
        && domain(Prop_PC)        == Ps
        && domain(Prop_Ready)     == Ps
        && domain(Prop_Soup)      == Ps
        && domain(Prop_V)         == Ps
        && domain(Prop_WL)        == Ps
        && domain(Prop_WL2)       == Ps
        && domain(Prop_a)         == Ps

        && domain(k)              == Ps
        && domain(k_pending)      == Ps
        && domain(l)              == Ps
        && domain(m)              == Ps

        && domain(OneB_Hist)      == As
        && domain(TwoB_Hist)      == As
        && domain(Joined_Rnd)     == As

        && domain(Prop_Soup_Hist) == Ps
        && domain(Acc_Soup_Hist)  == As
        );
    invariant forall a:nat,pid:nat,msg:Msg_Acc :: a in As && (pid,msg) in Acc_Soup[a] ==> pid in Ps;
    invariant forall p:nat,pid:nat,msg:Msg_Prop :: p in Ps && (pid,msg) in Prop_Soup[p] ==> pid in As;
    invariant forall p:nat,pid:nat,msg:Msg_Prop :: p in Ps && (pid,msg) in Prop_Soup_Hist[p] ==> pid in As;
    invariant forall p,a :: p in Ps && a == Prop_a[p] ==> a in As;
    invariant forall p :: p in Ps ==> Prop_WL[p] <= As && Prop_WL2[p] <= As;

    // ----------------------------------------------------------------------

    invariant forall n,v1,v2 :: (n,v1) in TwoA_Hist && (n,v2) in TwoA_Hist ==> v1 == v2; // (5)
    invariant forall a,p,n,v :: a in As && (p,Accept(n,v)) in Acc_Soup[a] ==> Prop_PC[p] !in {P0, P1, P2} && n == Prop_N[p] && v == Prop_V[p];
    invariant forall n,v :: (n,v) in TwoA_Hist ==> exists p :: p in Ps && n == Prop_N[p] && v == Prop_V[p] && Prop_PC[p] !in {P0, P1, P2};

    // ----------------------------------------------------------------------

    invariant forall a,n,v :: a in As && (n,v) in TwoB_Hist[a] ==> (n,v) in TwoA_Hist; // (6)
    invariant forall a,msg :: a in As && msg in Acc_Soup[a] ==> msg in Acc_Soup_Hist[a];
    invariant forall a,n,v :: a in As && (n,v) in TwoB_Hist[a] ==> (exists p :: p in Ps && (p, Accept(n,v)) in Acc_Soup_Hist[a]);
    invariant forall a,n,v,p :: a in As && (p, Accept(n,v)) in Acc_Soup_Hist[a] ==> (n,v) in TwoA_Hist;
      
    // ----------------------------------------------------------------------

    invariant forall p :: p in Ps && Prop_Decided[p] ==> k[p] > |As|/2; // (7)
    invariant forall p :: p in Ps ==> Prop_HO2[p] + k_pending[p] <= k[p];
    invariant forall p :: p in Ps ==> k_pending[p] >= 0;

    // ----------------------------------------------------------------------

    invariant forall a,vote :: a in As && vote in TwoB_Hist[a]==> vote.0 >= 0; // (11)

    // ----------------------------------------------------------------------

    invariant forall a,msg,n :: a in As && msg in Acc_Soup[a] && msg.1 == Prepare(n) ==> n >= 0;
    invariant forall n :: n in OneA_Hist ==> n >= 0;

    // ...HERE...

    // invariant forall a,msg_1b,msg_2b :: a in As && msg_1b in OneB_Hist[a] && msg_2b in TwoB_Hist[a] && msg_1b.1 < 0 ==> msg_2b.0 >= msg_1b.0 // (8)

    // ----------------------------------------------------------------------

    // invariant forall a,n,n',v :: a in As && (n,n',v) in OneB_Hist[a] && n' > 0 ==> n' < n && (n',v) in TwoB_Hist[a]; // (9)

    // ----------------------------------------------------------------------

    // invariant forall a,n,n',n'',v,v' :: a in As && (n,n',v) in OneB_Hist[a] && (n'',v') !in TwoB_Hist[a] && n' > 0 ==> ! (n' < n'' < n) ; // (10)

    // ----------------------------------------------------------------------

    // invariant forall p,n,v :: p in Ps && Prop_N[p] == n && (n,v) in TwoA_Hist ==> m[p] > |As|/2; // (13)

    // ----------------------------------------------------------------------

    // invariant forall a,n1,n2 :: a in As && n1 < n2 && n2 in Joined_Rnd[a] ==> n1 < Acc_Max_Seen_N[a]; // (14)
    // ?==>? invariant forall a,n :: a in As && n in Joined_Rnd[a] ==> n <= Acc_Max_Seen_N[a];

    // ----------------------------------------------------------------------

    // invariant forall a,msg :: a in As && msg in OneB_Hist[a] ==> msg.0 in Joined_Rnd[a]; // (15)

    // ----------------------------------------------------------------------

    // invariant forall p1,p2 :: p1 in Ps && p2 in Ps && Prop_Decided[p1] && Prop_Decided[p2] ==> Prop_V[p1] == Prop_V[p2]; // (4) (safety property)

    // ----------------------------------------------------------------------

    decreases *
    {
      var processToRun := *; assume processToRun in WL_main;

      if processToRun in As {
        var a := processToRun;

        /* while true
             (pid, msg) <- recv
             match msg {
               Prepare(no) =>
                 if max_1a < no {
                   max_1a <- no
                 }
               Accept(no,val) =>
                 if max_1a <= no {
                   if max_2a < no {
                     max_2a <- no
                     v      <- val
                   }
                   ts <- ts U {no}
                 }
             }
             send pid (n, v)
           done
         */
        if Acc_Soup[a] != multiset{} {
          var pid := *;
          var msg := *;

          assume (pid,msg) in Acc_Soup[a];
          Acc_Soup := Acc_Soup[a := Acc_Soup[a] - multiset{(pid,msg)}];

          var phase;

          match msg {
            case Prepare(no) =>
              if Acc_Max_Seen_N[a] < no {
                var onea_wl := Ps;
                while onea_wl != {}
                invariant onea_wl <= Ps;
                invariant domain(l) == Ps && domain(m) == Ps;
                decreases |onea_wl|
                {
                  var p' := *; assume p' in onea_wl;

                  if Prop_N[p'] !in Acc_Ns[a] &&
                    Prop_N[p'] >= Acc_Max_Seen_N[a] &&
                    Prop_N[p'] < no &&
                    l[p'] > 0 {
                      m := m[p' := m[p'] + 1];
                      l := l[p' := l[p'] - 1];
                  }
                  onea_wl := onea_wl - {p'};
                }

                Acc_Max_Seen_N := Acc_Max_Seen_N[a := no];
                Joined_Rnd := Joined_Rnd[a := Joined_Rnd[a] + {no}];
              }

              phase := OneB;
            case Accept(no,val) =>
              if Acc_Max_Seen_N[a] <= no  {
                Acc_Ns := Acc_Ns[a := Acc_Ns[a] + {no}];

                if Acc_Max_Accepted_N[a] <= no {
                  Acc_MaxV    := Acc_MaxV    [a := val];
                  Acc_Max_Accepted_N := Acc_Max_Accepted_N [a := no];
                }

                assume l[pid] > 0;
                k := k[pid := k[pid] + 1];
                l := l[pid := l[pid] - 1];
              }

              phase := TwoB;
          }

          if * {
            var n := Acc_Max_Accepted_N[a];
            var v := Acc_MaxV[a];

            var resp := (a, Value(n, v, phase));

            Prop_Soup := Prop_Soup[pid := Prop_Soup[pid] + multiset{resp}];
            Prop_Soup_Hist := Prop_Soup_Hist[pid := Prop_Soup_Hist[pid] + {resp}];

            // history variable update
            match msg {
              case Prepare(no) =>
                OneB_Hist := OneB_Hist[a := OneB_Hist[a] + {(no, n, v)}];
              case Accept(no,val) =>
                if Acc_Max_Seen_N[a] <= no {
                  TwoB_Hist := TwoB_Hist[a := TwoB_Hist[a] + {(no,val)}];
                  k_pending := k_pending[pid := k_pending[pid] + 1];
                }
            }
          }
        }
      }

      else if processToRun in Ps {
        var p := processToRun;

        if Prop_PC[p] == P0 {
          /* for a in A:
               <P1>
               <P2>
             done
           */
          if Prop_WL[p] != {} {
            var a := *; assume a in Prop_WL[p];

            Prop_a := Prop_a[p := a];
            Prop_WL := Prop_WL[p := Prop_WL[p] - {a}];
            Prop_PC := Prop_PC[p := P1];
          } else {
            Prop_PC := Prop_PC[p := P3];
          }

        } else if Prop_PC[p] == P1 {
          /* send a (p, Prepare(n))
           */
          var a := Prop_a[p];
          var n := Prop_N[p];

          Acc_Soup := Acc_Soup[a := Acc_Soup[a] + multiset{(p, Prepare(n))}];
          Acc_Soup_Hist := Acc_Soup_Hist[a := Acc_Soup_Hist[a] + {(p, Prepare(n))}];

          // history update
          OneA_Hist := OneA_Hist + {n};

          Prop_PC := Prop_PC[p := P2];

        } else if Prop_PC[p] == P2 {
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

          if * {
            if Prop_Soup[p] != multiset{} {
              var pid := *;
              var msg := *;

              assume (pid,msg) in Prop_Soup[p];
              Prop_Soup := Prop_Soup[p := Prop_Soup[p] - multiset{(pid,msg)}];

              match msg {
                case Value(no, val, OneB) =>
                  var max := Prop_Max[p];
                  if no > max {
                    Prop_Max := Prop_Max[p := no];
                    Prop_V   := Prop_V  [p := val];
                  }
                  Prop_HO := Prop_HO[p := Prop_HO[p] + 1];
              }

              Prop_WL := Prop_WL[p := Prop_WL[p] - {a}];
              Prop_PC := Prop_PC[p := P0];
            }
          } else {
            Prop_WL := Prop_WL[p := Prop_WL[p] - {a}];
            Prop_PC := Prop_PC[p := P0];
          }

        } else if Prop_PC[p] == P3 {
          /* if 2 x ho > |A| {
               ready <- true
               <P4>
             }
             <P7>
           */
          var ho := Prop_HO[p];
          if ho * 2 > |As| {
            Prop_Ready := Prop_Ready[p := true];
            Prop_PC    := Prop_PC   [p := P4];
          } else {
            Prop_PC := Prop_PC[p := P7];
          }

        } else if Prop_PC[p] == P4 {
          /* for a in A:
               <P5>
               <P6>
             done
           */
          if Prop_WL2[p] != {} {
            var a := *; assume a in Prop_WL2[p];

            Prop_a := Prop_a[p := a];
            Prop_WL2 := Prop_WL2[p := Prop_WL2[p] - {a}];
            Prop_PC := Prop_PC[p := P5];
          } else {
            Prop_PC := Prop_PC[p := P7];
          }

        } else if Prop_PC[p] == P5 {
          /* send a (p, Accept(n))
           */
          var a := Prop_a[p];
          var n := Prop_N[p];
          var v := Prop_V[p];

          Acc_Soup := Acc_Soup[a := Acc_Soup[a] + multiset{(p, Accept(n,v))}];
          Acc_Soup_Hist := Acc_Soup_Hist[a := Acc_Soup_Hist[a] + {(p, Accept(n,v))}];

          // history update
          TwoA_Hist := TwoA_Hist + {(n,v)};

          Prop_PC := Prop_PC[p := P6];

        } else if Prop_PC[p] == P6 {
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

          if * {
            if Prop_Soup[p] != multiset{} {
              var pid := *;
              var msg := *;

              assume (pid,msg) in Prop_Soup[p];
              Prop_Soup := Prop_Soup[p := Prop_Soup[p] - multiset{(pid,msg)}];

              match msg {
                case Value(no, val, TwoB) =>
                  var n := Prop_N[p];
                  if no == n {
                    Prop_HO2 := Prop_HO2[p := Prop_HO2[p] + 1];
                    assume k_pending[p] > 0;
                    k_pending := k_pending[p := k_pending[p] - 1];
                  }
              }

              Prop_WL := Prop_WL[p := Prop_WL[p] - {a}];
              Prop_PC := Prop_PC[p := P4];
            }
          } else {
            Prop_WL := Prop_WL[p := Prop_WL[p] - {a}];
            Prop_PC := Prop_PC[p := P4];
          }

        } else if Prop_PC[p] == P7 {
          /* if ho2 * 2 > |A| {
               decided <- true
             }
           */
          var ho2 := Prop_HO2[p];
          if ho2 * 2 > |As| {
            Prop_Decided := Prop_Decided[p := true];
          }
          WL_main := WL_main - {p};
        }
      }
    }

    // forall p1,p2 :: p1.decided && p2.decided ==> p1.v == p2.v
    // assert forall p1,p2 :: p1 in Ps && p2 in Ps && Prop_Decided[p1] && Prop_Decided[p2] ==> Prop_V[p1] == Prop_V[p2];

  }
}
