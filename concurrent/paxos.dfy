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
      Proposal(no: int)
    | Accept(no: int, val: int)

  datatype Msg_Prop =
      Value(no: int, val: int)

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

    // max seen proposal number
    var Prop_Max : map<nat, int> := map p | p in Ps :: (-1);

    // proposer's program counter
    var Prop_PC  : map<nat, Loc>  := map p | p in Ps :: P0;

    // heard of count
    var Prop_HO       : map<nat, nat>  := map p | p in Ps :: 0;

    // is proposer in the second phase ?
    var Prop_Ready    : map<nat, bool> := map p | p in Ps :: false;

    var Prop_Decided  : map<nat, bool> := map p | p in Ps :: false;

    var Prop_a   : map<nat, nat> := *;
    assume domain(Prop_a) == Ps;

    var Prop_WL  : map<nat, set<nat>> := map p | p in Ps :: As;
    var Prop_WL2 : map<nat, set<nat>> := map p | p in Ps :: As;

    // #########################################################################
    // Acceptor State
    // #########################################################################

    // value accepted by the acceptor
    var Acc_V : map<nat, int> := *;
    assume domain(Acc_V) == As;

    // accepted proposal's number
    var Acc_N   : map<nat, int>       := map a | a in As :: (-1);

    // max proposal number seen
    var Acc_Max : map<nat, int>       := map a | a in As :: (-1);

    // all accepted proposal numbers
    var Acc_Ns  : map<nat, set<int>>  := map a | a in As :: {};

    // acceptor's program counter
    var Acc_PC  : map<nat, Loc>       := map a | a in As :: P0;

    // #########################################################################
    // Message soups
    // #########################################################################

    var Acc_Soup  : map<nat, multiset<(nat,Msg_Acc)>>  := map a | a in As :: multiset{};
    var Prop_Soup : map<nat, multiset<(nat,Msg_Prop)>> := map p | p in Ps :: multiset{};

    // #########################################################################
    // Set cardinalities
    // #########################################################################

    // k[p] := #{a in A | p.n in a.ns}
    // i.e. number of acceptors have accepted p's proposal
    var k : map<nat, nat> := map p | p in Ps :: 0;

    // l[p] := #{a in A | p.n !in a.ns && a.max <= p.n}
    // i.e. number of acceptors may accept p's proposal
    var l : map<nat, nat> := map p | p in Ps :: len(As);

    // m[p] := #{a in A | p.n !in a.ns && a.max > p.n}
    // i.e. number of acceptors will never accept p's proposal
    var m : map<nat, nat> := map p | p in Ps :: 0;

    // #########################################################################

    var WL_main := Ps + As;

    while WL_main != {}
    invariant Ps == old(Ps);
    invariant As == old(As);
    invariant WL_main <= Ps + As;
    invariant
        ( domain(Acc_Ns)       == As
        && domain(Acc_Max)      == As
        && domain(Acc_N)        == As
        && domain(Acc_Soup)     == As
        && domain(Acc_V)        == As 

        && domain(Prop_Decided) == Ps
        && domain(Prop_HO)      == Ps
        && domain(Prop_N)       == Ps
        && domain(Prop_PC)      == Ps
        && domain(Prop_Ready)   == Ps
        && domain(Prop_Soup)    == Ps
        && domain(Prop_V)       == Ps
        && domain(Prop_WL)      == Ps
        && domain(Prop_WL2)     == Ps
        && domain(Prop_a)       == Ps

        && domain(k)            == Ps
        && domain(l)            == Ps
        && domain(m)            == Ps
        );
    invariant forall a:nat,pid:nat,msg:Msg_Acc :: a in As && (pid,msg) in Acc_Soup[a] ==> pid in Ps;
    invariant forall p:nat,pid:nat,msg:Msg_Prop :: p in Ps && (pid,msg) in Prop_Soup[p] ==> pid in As;
    invariant forall p,a :: p in Ps && a == Prop_a[p] ==> a in As;
    invariant forall p :: p in Ps ==> Prop_WL[p] <= As && Prop_WL2[p] <= As;
    decreases *
    {
      var processToRun := *; assume processToRun in WL_main;

      if processToRun in As {
        var a := processToRun;

        /* while true
             (pid, msg) <- recv
             match msg {
               Proposal(no) => 
                 if max < no {
                   max <- no
                 }
               Accept(no,val) =>
                 if max <= no {
                   v  <- val
                   n  <- no
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

          match msg {
            case Proposal(no) =>
              if Acc_Max[a] < no {
                Acc_Max := Acc_Max[a := no];
              }
            case Accept(no,val) =>
              if Acc_Max[a] <= no {
                Acc_V  := Acc_V [a := val];
                Acc_N  := Acc_N [a := no];
                Acc_Ns := Acc_Ns[a := Acc_Ns[a] + {no}];
              }
          }

          if * {
            var n := Acc_N[a];
            var v := Acc_V[a];

            Prop_Soup := Prop_Soup[pid := Prop_Soup[pid] + multiset{(a,Value(n, v))}];
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
            assert a in As;

            Prop_a := Prop_a[p := a];
            Prop_WL := Prop_WL[p := Prop_WL[p] - {a}];
            Prop_PC := Prop_PC[p := P1];
          } else {
            Prop_PC := Prop_PC[p := P3];
          }

        } else if Prop_PC[p] == P1 {
          /* send a (p, Proposal(n))
           */
          var a := Prop_a[p];
          var n := Prop_N[p];

          Acc_Soup := Acc_Soup[a := Acc_Soup[a] + multiset{(p, Proposal(n))}];

          Prop_PC := Prop_PC[p := P2];

        } else if Prop_PC[p] == P2 {
          /* reply <- recvTO(a);
             match reply {
               None => 
                 return ()
               Some Value(no, val) =>
                 if no > max {
                   max <- no
                   v   <- val
                 }
                 ho <- ho + 1
             }
           */
          var a := Prop_a[p];

          if * {
            if Prop_Soup[p] != multiset{} {
              var pid := *;
              var msg := *;

              assume (pid,msg) in Prop_Soup[p];
              Prop_Soup := Prop_Soup[p := Prop_Soup[a] - multiset{(pid,msg)}];

              match msg {
                case Value(no, val) =>
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
               ho <- 0
               ready <- true
               <P4>
             }
             <P7>
           */
          var ho := Prop_HO[p];
          if ho * 2 > |As| {
            Prop_HO    := Prop_HO   [p := 0];
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
            assert a in As;

            Prop_a := Prop_a[p := a];
            Prop_WL2 := Prop_WL2[p := Prop_WL2[p] - {a}];
            Prop_PC := Prop_PC[p := P5];
          } else {
            Prop_PC := Prop_PC[p := P7];
          }

        } else if Prop_PC[p] == P5 {
          /* send a (p, Proposal(n))
           */
          var a := Prop_a[p];
          var n := Prop_N[p];
          var v := Prop_V[p];

          Acc_Soup := Acc_Soup[a := Acc_Soup[a] + multiset{(p, Accept(n,v))}];

          Prop_PC := Prop_PC[p := P6];

        } else if Prop_PC[p] == P6 {
          /* reply <- recvTO(a);
             match reply {
               None => 
                 return ()
               Some Value(no, val) =>
                 if no = n {
                   ho <- ho + 1
                 }
             }
           */
          var a := Prop_a[p];

          if * {
            if Prop_Soup[p] != multiset{} {
              var pid := *;
              var msg := *;

              assume (pid,msg) in Prop_Soup[p];
              Prop_Soup := Prop_Soup[p := Prop_Soup[a] - multiset{(pid,msg)}];

              match msg {
                case Value(no, val) =>
                  var n := Prop_N[p];
                  if no == n {
                    Prop_HO := Prop_HO[p := Prop_HO[p] + 1];
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
          var ho := Prop_HO[p];
          if ho * 2 > |As| {
            Prop_Decided := Prop_Decided[p := true];
          }
          WL_main := WL_main - {p};
        }
      }
    }
  }
}
