module ConcDB
{
  predicate Param<T>(N:nat, X:array<T>)
  {
    X != null && X.Length == N
  }

  predicate Eq(x:int, y:int) { x == y }

  method ChooseWL(P:set<nat>, WL:set<nat>) returns (i:nat)
    ensures (i in WL && i in P);
  {
    i := *;
    assume (i in WL && i in P);
  }

  method ConcDBSeq
    ( Cs : set<nat>
    )
    decreases *
  {
    //Client Variables
    var PC      : map<nat, nat> := map i | i in Cs :: 0;
    var X       : map<nat, int> := map i | i in Cs :: 0;
    var V       : map<nat, int> := map i | i in Cs :: 0;
    var Status  : map<nat, int> := map i | i in Cs :: 0;
    var Vp      : map<nat, int> := map i | i in Cs :: 0;
    
    //Database Variables
    var DbID : nat;
    var DbMsgType : nat;
    var DbMsgKey : int;
    var DbMsgVal : int;
    var DbResponse : int;
    var DbDb : map<int,int> := map[];
    
    var ClientWL := Cs;

    while ClientWL != {}
    invariant (Cs == old(Cs))
    invariant (forall c :: c in ClientWL ==> c in Cs)
    invariant (forall c :: c in PC <==> c in Cs)
    invariant (forall c :: c in X  <==> c in Cs)
    invariant (forall c :: c in V  <==> c in Cs)
    invariant (forall c :: c in Vp <==> c in Cs)
    invariant (forall c :: c in Status <==> c in Cs)
    invariant (forall c :: forall k :: c in Cs && Eq(k,X[c]) ==> (
                 (PC[c] == 0)
               || (PC[c] == 1 && Status[c] != 4  && k in DbDb)
               || (PC[c] == 1 && Status[c] == 4 && k in DbDb && DbDb[k] == V[c])
               || (PC[c] == 2 && Status[c] == 4 && k in DbDb && V[c] == Vp[c] && DbDb[k] == Vp[c])
               )
            )
      decreases *
    {
      var c := ChooseWL(Cs, ClientWL);
      if PC[c] == 0
      {
        var k    := *;
        var v    := *;
        X        := X[c := k];
        V        := V[c := v];
        DbID     := c;
        DbMsgKey := X[c];
        DbMsgVal := V[c];

        if DbMsgKey in DbDb {
          DbResponse := 3;
        } else {
          DbDb := DbDb[DbMsgKey := DbMsgVal];
          DbResponse := 4;
        }

        Status := Status[c := DbResponse];
        PC     := PC[c := 1];

      } else if PC[c] == 1 {
        if (Status[c] == 4) {
          DbMsgType := 1;
          DbMsgKey := X[c];
          if DbMsgKey in DbDb {
            DbResponse := DbDb[DbMsgKey];
          } else {
            DbResponse := *;
          }
          Vp := Vp[c := DbResponse];
          PC := PC[c := 2];
          ClientWL := ClientWL - {c};
          assert (Vp[c] == V[c]);
        }
      }
    }
  }
  
}
