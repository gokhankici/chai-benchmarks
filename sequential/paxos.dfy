module PaxosSingle {

  function method len(s: set<nat>) : (l: nat)
    ensures l == |s|
  {
    |s|
  }

  function domain<U,V>(m: map<U,V>) : set<U>
	  ensures domain(m) == set u : U | u in m :: u;
	  ensures forall u :: u in domain(m) ==> u in m;
  {
		  set u : U | u in m :: u
  }

  predicate TA(a:int) { true }
  predicate TP(a:int) { true }

  datatype Loc = P0 | P1 | P2
  method PaxosSingle
    ( Ps : set<nat>
    , As : set<nat>
    )
    requires |Ps| > 0
    requires |As| >= 2
    decreases *
  {
    // Proposer local state
    var X       : map<nat, int> := *; assume (forall p :: p in Ps <==> p in X);
    var X_T     : map<nat, int> := map p | p in Ps :: (-1);
    var T       : map<nat, nat> := *; assume (forall p :: p in Ps <==> p in T);
    assume forall p1,p2 :: p1 in Ps && p2 in Ps ==> (T[p1] == T[p2] <==> p1 == p2);
    var HO      : map<nat, nat> := map p | p in Ps :: 0;
    var Ready   : map<nat, bool>     := map p | p in Ps :: false;
    var Decided : map<nat, bool>     := map p | p in Ps :: false;
    var PC      : map<nat, Loc>      := map p | p in Ps :: P0;
    var WL_As   : map<nat, set<nat>> := map p | p in Ps :: As;
    // Acceptor State
    var V       : map<nat, int> := *; assume (forall a :: a in As <==> a in V);
    var V_T     : map<nat, int> := map a | a in As :: (-1);
    var Max     : map<nat, int> := map a | a in As :: (-1);
    var Ts      : map<nat, set<int>>  := map a | a in As :: {};

    // Set cardinalities
    var k : map<nat, nat> := map p | p in Ps :: 0;
    var l : map<nat, nat> := map p | p in Ps :: len(As);
    var m : map<nat, nat> := map p | p in Ps :: 0;

    var WL_Ps := Ps;
    while WL_Ps != {}
    free invariant Ps == old(Ps);
    free invariant As == old(As);
    free invariant
        ( domain(Ts) == As
        && domain(Max) == As
        && domain(V) == As 
        && domain(V_T) == As
        && domain(WL_As) == Ps
        && domain(PC) == Ps
        && domain(X) == Ps
        && domain(X_T) == Ps
        && domain(T) == Ps
        && domain(HO) == Ps
        && domain(k) == Ps
        && domain(l) == Ps
        && domain(m) == Ps
        && domain(Decided) == Ps
        && domain(Ready) == Ps
        )
    free invariant (forall p :: p in WL_Ps ==> p in Ps);
    free invariant (forall p :: forall a :: p in Ps && a in WL_As[p] ==> a in As);
    free invariant (forall p :: p in Ps ==> k[p] >= 0)
    free invariant (forall p :: p in Ps ==> l[p] >= 0)
    free invariant (forall p :: p in Ps ==> m[p] >= 0)
    // Helper Lemmas
    free invariant (forall p :: (p in Ps && PC[p] == P0) ==> !Ready[p])
    free invariant (forall p :: (p in Ps && PC[p] == P1) ==> Ready[p])
    free invariant (forall p :: p in Ps && Decided[p] ==> PC[p] == P2 && HO[p] > |As|/2 && Ready[p])
    free invariant (forall p :: p in Ps && !Ready[p] ==> k[p] == 0)
    free invariant (forall p :: p in Ps && Ready[p] ==> k[p] >= HO[p])
    free invariant (forall p :: p in Ps ==> |As| == k[p] + l[p] + m[p])
    free invariant (forall p :: p in Ps && k[p] > 0 ==> PC[p] != P0)

    // invariant (forall a, p :: p in Ps && a in As && l[p] > |As|/2 && k[p] == 0 ==> V_T[a] < T[p])

    // --- from assume ---

    free invariant forall p1,p2 :: p1 in Ps && p2 in Ps ==> (T[p1] == T[p2] <==> p1 == p2);
    // invariant forall a,t :: a in As && t in Ts[a] ==> V_T[a] >= t;
    invariant forall a :: a in As ==> Max[a] >= V_T[a];
    // invariant forall p,a :: p in Ps && a in As && Ready[p] && V_T[a] >= T[p] && k[p]+l[p] > |As|/2 ==> V[a] == X[p];

    // invariant forall p,a :: p in Ps && a in As && X_T[p] >= 0 ==> (X[p] == V[a] && X_T[p] == V_T[a]);
    // invariant forall p1,p2 :: p1 in Ps && p2 in Ps && l[p1] > |As|/2 ==> (!Ready[p2] || T[p2] < T[p1]);
    // invariant forall p1,p2 :: p1 in Ps && p2 in Ps && (Ready[p1] && k[p1]+l[p1] > |As|/2 && Ready[p2]) ==> (X_T[p2] >= T[p1] && X_T[p2] >= 0);

    // ---

    decreases *
    {
      var p0 := *; assume p0 in WL_Ps;
      var a2 := *; assume a2 in As;

      // Prepare phase loop
      if (PC[p0] == P0)
      {
        if (WL_As[p0] != {})
        {
          var a0 := *;
          assume a0 in WL_As[p0];

          //Body of loop
          if (T[p0] > Max[a0])
          {
            Max := Max[a0 := T[p0]];
            if * {
              if (V_T[a0] > X_T[p0]) {
                X   := X[p0 := V[a0]];
                X_T := X_T[p0 := V_T[a0]];
              }
                HO := HO[p0 := HO[p0] + 1];
            }
            var p2 := *; assume p2 in Ps && p2 != p0;
            if (T[p2] <= Max[a0])
            {
              assume (l[p2] > 0);
              l := l[p2 := l[p2] - 1];
              m := m[p2 := m[p2] + 1];
            }
          }
          
          WL_As := WL_As[p0 := WL_As[p0] - {a0}];
        }
        else 
        {
          if HO[p0] > |As|/2 {
            HO := HO[p0 := 0];
            Ready := Ready[p0 := true];
            PC := PC[p0 := P1];
            WL_As := WL_As[p0 := As];
          } else {
            PC := PC[p0 := P2];
            WL_Ps := WL_Ps - {p0};
          }
        }
      }

      else if (PC[p0] == P1)
      {
        // assume Ready[p0];
        // assume k[p0] >= HO[p0];

        if (WL_As[p0] != {})
        {
          var a0 := *;
          assume a0 in WL_As[p0];

          // Body of loop
          if (T[p0] >= Max[a0])
          {
            V   := V[a0 := X[p0]];
            V_T := V_T[a0 := T[p0]];
            Ts  := Ts[a0 := Ts[a0] + {T[p0]}];

            // Cardinality updates
            assume (l[p0] > 0);
            k := k[p0 := k[p0] + 1];
            l := l[p0 := l[p0] - 1];
            if * {
              var hn' := HO[p0] + 1;
              HO := HO[p0 := hn'];
            }
          }
          WL_As := WL_As[p0 := WL_As[p0] - {a0}];
        }
        else
        {
          if HO[p0] > |As|/2 {
            Decided := Decided[p0 := true];
          }
          PC := PC[p0 := P2];
          WL_Ps := WL_Ps - {p0};
        }
      }

      // assert (forall a,p1, p2 :: (a in As && p1 in Ps && p2 in Ps && Decided[p1] && Decided[p2] &&
      //   ((k[p1] > |As|/2 && k[p2] > |As|/2) ==> (V_T[a] >= T[p1] && V_T[a] >= T[p2])) &&
      //   l[p1] >= 0 && l[p2] >= 0)
      //   ==>
      //   X[p1] == X[p2]);
                  
    }
  }

}
