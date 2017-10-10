module PaxosSingle {

  function domain<U,V>(m: map<U,V>) : set<U>
	  ensures domain(m) == set u : U | u in m :: u;
	  ensures forall u :: u in domain(m) ==> u in m;
  {
		  set u : U | u in m :: u
  }

  datatype Loc = P0 | P1 | P2 | P3 | P4 | P5 | P6 ;

  datatype Msg =
      Proposal(pid: nat, n: int)
    | Accept(pid: nat, n: int, val: int)
    | Value(pid: nat, vt: int, v: int);

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
    var X       : map<nat, int> := *; assume (forall p :: p in Ps <==> p in X);
    var X_T     : map<nat, int> := map p | p in Ps :: (-1);
    var T       : map<nat, nat> := *; assume (forall p :: p in Ps <==> p in T);
    var HO      : map<nat, nat> := map p | p in Ps :: 0;
    var Ready   : map<nat, bool>     := map p | p in Ps :: false;
    var Decided : map<nat, bool>     := map p | p in Ps :: false;
    var PC      : map<nat, Loc>      := map p | p in Ps :: P0;
    var WL_As   : map<nat, set<nat>> := map p | p in Ps :: As;
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
    var Acc_Soup  : map<nat, multiset<Msg>> := map a | a in As :: multiset{};
    var Prop_Soup : map<nat, multiset<Msg>> := map p | p in Ps :: multiset{};
    // #########################################################################

    // #########################################################################
    // Set cardinalities
    // #########################################################################
    var k : map<nat, nat> := map p | p in Ps :: 0;
    var l : map<nat, nat> := map p | p in Ps :: |As|;
    var m : map<nat, nat> := map p | p in Ps :: 0;
    // #########################################################################

    var WL_main := Ps + As;

    while WL_main != {}
    invariant Ps == old(Ps);
    invariant As == old(As);
    invariant WL_main <= Ps + As;
    invariant
        ( domain(Vs)      == As
        && domain(Max)     == As
        && domain(V)       == As 
        && domain(V_T)     == As
        && domain(WL_As)   == Ps
        && domain(PC)      == Ps
        && domain(X)       == Ps
        && domain(X_T)     == Ps
        && domain(HO)      == Ps
        && domain(k)       == Ps
        && domain(l)       == Ps
        && domain(m)       == Ps
        && domain(Decided) == Ps
        && domain(Ready)   == Ps
        );
    decreases *
    {
      var processToRun := *; assume processToRun in WL_main;

      if processToRun in As {
        var a := processToRun;

        if Acc_Soup[a] != multiset{} {
          var msg := *; assume msg in Acc_Soup[a];

          match msg {
            case Proposal(pid,n) =>
              if Max[a] < n {
                Max := Max[a := n];
              }
          }{
            case Accept(pid,n,val) =>
              if Max[a] <= n {
                V   := V[a := val];
                V_T := V_T[a := n];
                Ts  := Ts[a := Ts[a] + {n}];
              }
          }{
            case Value(pid,vt,v) =>
              {}
          }
        }
      }
      else if processToRun in Ps {
        var p := processToRun;

      }
      
    }
  }

}
