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
      Proposal(n: int)
    | Accept(n: int, val: int)

  datatype Msg_Prop =
      Value(vt: int, v: int)

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
    var X        : map<nat, int> := *; assume (forall p :: p in Ps <==> p in X);
    var X_T      : map<nat, int> := map p | p in Ps :: (-1);
    var T        : map<nat, nat> := *; assume (forall p :: p in Ps <==> p in T);
    var HO       : map<nat, nat> := map p | p in Ps :: 0;
    var Ready    : map<nat, bool>     := map p | p in Ps :: false;
    var Decided  : map<nat, bool>     := map p | p in Ps :: false;
    var Prop_PC  : map<nat, Loc>      := map p | p in Ps :: P0;
    var Prop_WL  : map<nat, set<nat>> := map p | p in Ps :: As;
    var Prop_WL2 : map<nat, set<nat>> := map p | p in Ps :: As;
    var Prop_a   : map<nat, nat> := *; assume (forall p :: p in Ps <==> p in Prop_a); assume(forall p,a :: p in Ps && a == Prop_a[p] ==> a in As);
    // #########################################################################

    // #########################################################################
    // Acceptor State
    // #########################################################################
    var V       : map<nat, int> := *; assume (forall a :: a in As <==> a in V);
    var V_T     : map<nat, int> := map a | a in As :: (-1);
    var Max     : map<nat, int> := map a | a in As :: (-1);
    var Ts      : map<nat, set<int>>  := map a | a in As :: {};
    // #########################################################################

    // #########################################################################
    // Message soups
    // #########################################################################
    var Acc_Soup  : map<nat, multiset<(nat,Msg_Acc)>>  := map a | a in As :: multiset{};
    var Prop_Soup : map<nat, multiset<(nat,Msg_Prop)>> := map p | p in Ps :: multiset{};
    // #########################################################################

    // #########################################################################
    // Set cardinalities
    // #########################################################################
    var k : map<nat, nat> := map p | p in Ps :: 0;
    var l : map<nat, nat> := map p | p in Ps :: len(As);
    var m : map<nat, nat> := map p | p in Ps :: 0;
    // #########################################################################

    var WL_main := Ps + As;

    while WL_main != {}
    invariant Ps == old(Ps);
    invariant As == old(As);
    invariant WL_main <= Ps + As;
    invariant
        ( domain(Ts)        == As
        && domain(Max)       == As
        && domain(V)         == As 
        && domain(V_T)       == As
        && domain(Prop_WL)   == Ps
        && domain(Prop_WL2)  == Ps
        && domain(Prop_PC)   == Ps
        && domain(X)         == Ps
        && domain(X_T)       == Ps
        && domain(HO)        == Ps
        && domain(k)         == Ps
        && domain(l)         == Ps
        && domain(m)         == Ps
        && domain(Decided)   == Ps
        && domain(Ready)     == Ps

        && domain(Acc_Soup)  == As
        && domain(Prop_Soup) == Ps
        && domain(Prop_a)    == Ps
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

        if Acc_Soup[a] != multiset{} {
          var pid := *;
          var msg := *;

          assume (pid,msg) in Acc_Soup[a];
          Acc_Soup := Acc_Soup[a := Acc_Soup[a] - multiset{(pid,msg)}];

          match msg {
            case Proposal(n) =>
              if Max[a] < n {
                Max := Max[a := n];
              }
            case Accept(n,val) =>
              if Max[a] <= n {
                V   := V[a := val];
                V_T := V_T[a := n];
                Ts  := Ts[a := Ts[a] + {n}];
              }
          }

          var vt := V_T[a];
          var v  := V[a];

          if * {
            Prop_Soup := Prop_Soup[pid := Prop_Soup[pid] + multiset{(a,Value(vt, v))}];
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
          /* send a (p, Proposal(t))
           */
          var a := Prop_a[p];
          var t := T[p];
          Acc_Soup := Acc_Soup[a := Acc_Soup[a] + multiset{(p, Proposal(t))}];
          Prop_PC := Prop_PC[p := P2];
        } else if Prop_PC[p] == P2 {
          /* Value(vt,v) <- recvTO(a);
             if vt > xt {
               xt <- vt
               x  <- v
             }
             ho <- ho + 1
           */

          // TODO
        } else if Prop_PC[p] == P3 {
          /* if 2 x ho > |A| {
               ho <- 0
               ready <- true
               <P4>
             }
           */
          var ho := HO[p];
          if ho * 2 > |As| {
            HO := HO[p := 0];
            Ready := Ready[p := true];
            Prop_PC := Prop_PC[p := P4];
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
        } else if Prop_PC[p] == P4 {
          // TODO
        } else if Prop_PC[p] == P5 {
          // TODO
        } else if Prop_PC[p] == P6 {
          // TODO
        } else if Prop_PC[p] == P7 {
          var ho := HO[p];
          if ho * 2 > |As| {
            Decided := Decided[p := true];
          }
          WL_main := WL_main - {p};
        }
      }
    }
  }
}
