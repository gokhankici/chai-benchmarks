class PingProtocol
{

  method PingSeq( Ps : set<nat>
                )
  {
    var X  := map i | i in Ps :: 0;

    // Master chooses Val
    var Val := *;

    // Iterate over processes
    var WL := Ps;
    while WL != {}
      invariant forall p :: p in Ps <==> p in X;
      invariant forall p :: p in Ps && p !in WL ==> X[p] == Val;
      decreases |WL|
    {
      var p := *;
      assume (p in WL && p in Ps);

      X := X[p := Val];
      WL := WL - {p};
    }

    assert (forall p :: p in Ps ==> X[p] == Val);
  }
}
