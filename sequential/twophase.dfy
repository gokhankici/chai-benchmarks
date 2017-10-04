module TwoPhaseCommit
{

  datatype Message = Init | Commit | Abort

  method TwoPhase( Ps : set<nat>
                 , c  : nat
                 )
  {
    // Initialize C
    var proposal := *;
    var committed := false;
    var abort    := false;
    var reply    := Abort;
    var cMsg;
    // Initialize Ps
    var Id       := map i | i in Ps :: 0;
    var Val      := map i | i in Ps :: 0;
    var Value    := map i | i in Ps :: 0;
    var Msg      := map i | i in Ps :: Init;
    var Decision := map i | i in Ps :: Init;
    var WL;

   /* //prepare phase
      1: for p in P do
        p.id <- c; 
        p.val <- c.proposal
      end;
    */
    WL := Ps;
    while WL != {}
    invariant forall p :: p in WL ==> p in Ps;
    invariant forall p :: p in Ps <==> p in Val 
    invariant forall p :: p in Ps && p !in WL ==> Val[p] == proposal
    decreases |WL|
    {
      var p := *; assume (p in WL && p in Ps);
      Id    := Id[p := c];
      Val   := Val[p := proposal];

      WL := WL - {p};
    }
    /* 2: for p in P do
      if * then 
          c.msg <- commit
          p.msg <- commit
       else
         c.abort <- true;
         c.msg <- abort
         p.msg <- abort
       end;  
      end;
    */
    WL := Ps;
    while WL != {}
    decreases |WL|
    {
      var p := *; assume (p in WL && p in Ps);
      if * {
        cMsg := Commit;
        Msg := Msg[p := cMsg];
      } else {
        abort := true;
        cMsg := Abort;
        Msg := Msg[p := cMsg];
      }
      WL := WL - {p};
    }

    /*
    // commit phase
    3: if c.abort=false then 
       c.reply <-commit;
       c.committed<-true
    else
       c.reply<-abort
    end;
    Commit = 0
    Abord  = 1
    */

    if abort {
      reply := Abort;
    } else{
      reply := Commit;
      committed := true;
    }

   /*
   4: for p in P do
      p.decision <- c.reply;
      if p.decision=commit then
         p.value <- p.val
      end
   end
   */
    WL := Ps;
    while WL != {}
    invariant (forall p :: p in Ps <==> p in Value)
    invariant (forall p :: p in Ps && p !in WL && committed ==> Value[p] == Val[p])
    decreases |WL|
    {
      var p := *; assume (p in WL && p in Ps);
      Decision := Decision[p := reply];
      if Decision[p] == Commit {
        Value := Value[p := Val[p]];
      }

      WL := WL - {p};
    }

    assert (forall p :: p in Ps && committed ==> Value[p] == proposal);
  }
}
