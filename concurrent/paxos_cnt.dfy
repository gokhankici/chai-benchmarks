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

  datatype Loc = P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 

  datatype Msg_Acc =                                                                                                     // code
      Prepare(no: int)                                                                                                   // code
    | Accept(no: int, val: int)                                                                                          // code

  datatype Msg_Phase =                                                                                                   // code
      OneB                                                                                                               // code
    | TwoB                                                                                                               // code

  datatype Msg_Prop = Value(max_seen_n: int, max_accepted_n: int, max_val: int, phase: Msg_Phase)                        // code

  method {:timeLimit 0} PaxosSingle                                                                                      // code
    ( Ps : set<nat>                                                                                                      // code
    , As : set<nat>                                                                                                      // code
    )                                                      
    requires |Ps| > 0                                                                                                    // annot
    requires |As| >= 2                                                                                                   // annot
    requires Ps !! As                                                                                                    // annot
    decreases *                                                                                                          
  { 
    // #########################################################################                                         
    // Proposer local state                                                                                              
    // #########################################################################                                         

    // proposed value of the proposer                                                                                   
    var Prop_V : map<nat, int> := *;                                                                                     // code
    assume domain(Prop_V) == Ps;                                                                                         // harness

    // proposal number of the proposal                                                                                   
    var Prop_N : map<nat, nat> := *;                                                                                     // code
    assume domain(Prop_N) == Ps;                                                                                         // harness
    assume forall p :: p in Ps ==> Prop_N[p] > 0;                                                                        // harness
    assume forall p1,p2 :: p1 in Ps && p2 in Ps ==> (p1 == p2 <==> Prop_N[p1] == Prop_N[p2]);                            // annot

    // max seen proposal number                                                                                   
    var Prop_Max : map<nat, int> := map p | p in Ps :: (-1);                                                             // code

    // proposer's program counter                                                                                
    var Prop_PC  : map<nat, Loc>  := map p | p in Ps :: P0;                                                              // code

    // heard of count                                                                                           
    var Prop_HO       : map<nat, nat>  := map p | p in Ps :: 0;                                                          // code
    var Prop_HO2      : map<nat, nat>  := map p | p in Ps :: 0;                                                          // code

    // is proposer in the second phase ?                                                                       
    var Prop_Ready    : map<nat, bool> := map p | p in Ps :: false;                                                      // code

    var Prop_Decided  : map<nat, bool> := map p | p in Ps :: false;                                                      // code

    var Prop_Exec_P5 : map<nat, bool> := map p | p in Ps :: false;                                                       // code
    var Prop_Exec_P6 : map<nat, bool> := map p | p in Ps :: false;                                                       // code

    var Prop_a   : map<nat, nat> := *;                                                                                   // code
    assume domain(Prop_a) == Ps;                                                                                         // harness
    assume forall p,a :: p in Ps && a == Prop_a[p] ==> a in As;                                                          // harness

    var Prop_WL  : map<nat, set<nat>> := map p | p in Ps :: As;                                                          // harness
    var Prop_WL2 : map<nat, set<nat>> := map p | p in Ps :: As;                                                          // harness

    // #########################################################################                                         
    // Acceptor State                                                                                                    
    // #########################################################################                                         

    // value of the highest numbered proposal accepted by the acceptor                                                   
    var Acc_MaxV : map<nat, int> := *;                                                                                   // code
    assume domain(Acc_MaxV) == As;                                                                                       // harness

    // highest accepted proposal's number                                                                                
    var Acc_Max_Accepted_N : map<nat, int> := map a | a in As :: (-1);                                                   // code

    // max proposal number seen                                                                                         
    var Acc_Max_Seen_N : map<nat, int> := map a | a in As :: (-1);                                                       // code

    // all accepted proposal numbers                                                                                     
    var Acc_Ns  : map<nat, set<int>> := map a | a in As :: {};                                                           // code

    // acceptor's program counter                                                                                       
    var Acc_PC  : map<nat, Loc> := map a | a in As :: P0;                                                                // code

    // #########################################################################                                         
    // Message soups                                                                                                     
    // #########################################################################                                         

    var Acc_Soup  : map<nat, multiset<(nat,Msg_Acc)>>  := map a | a in As :: multiset{};                                 // harness
    var Prop_Soup : map<nat, multiset<(nat,Msg_Prop)>> := map p | p in Ps :: multiset{};                                 // harness

    var Acc_Soup_Hist  : map<nat, set<(nat,Msg_Acc)>>  := map a | a in As :: {};                                         // code
    var Prop_Soup_Hist : map<nat, set<(nat,Msg_Prop)>> := map p | p in Ps :: {};                                         // code

    // #########################################################################                                         
    // Message histories                                                                                                
    // #########################################################################                                       

    var OneA_Hist : set<nat>                     := {};                                                                  // code
    var OneB_Hist : map<nat, set<(int,int,int)>> := map a | a in As :: {};                                               // code
    var TwoA_Hist : set<(int,int)>               := {};                                                                  // code
    var TwoB_Hist : map<nat, set<(int,int)>>     := map a | a in As :: {};                                               // code

    // #########################################################################                                      
    // Other history variables                                                                                       
    // #########################################################################                                    

    // (a,n) in Joined_Rnd ==> a has seen a proposal msg numbered n                                                
    var Joined_Rnd : map<nat, set<int>> := map a | a in As :: {};                                                        // code

    // #########################################################################                                         
    // Set cardinalities                                                                                                
    // #########################################################################                                       

    // k[p] := #{a in A | p.n in a.ns}                                                                                
    // i.e. number of acceptors have accepted p's proposal                                                           
    var k : map<nat, nat> := map p | p in Ps :: 0;                                                                       // code

    // k_pending[p] := #{(a,Value(no,val,TwoB)) in Prop_Soup[p] | no == p.n}                                        
    // i.e. number of messages in flight that will increment the `p.ho2`                                           
    // variable upon receive                                                                                      
    var k_pending : map<nat, nat> := map p | p in Ps :: 0;                                                               // code

    // l[p] := #{a in A | p.n !in a.ns && a.max <= p.n}                                                          
    // i.e. number of acceptors may accept p's proposal                                                         
    var l : map<nat, nat> := map p | p in Ps :: len(As);                                                                 // code

    // m[p] := #{a in A | p.n !in a.ns && a.max > p.n}                                                         
    // i.e. number of acceptors will never accept p's proposal                                                
    var m : map<nat, nat> := map p | p in Ps :: 0;                                                                       // code

    // #########################################################################                             

    var WL_main := Ps + As;                                                                                              // harness

    while WL_main != {}                                                                                                  // code
    free invariant WL_main <= Ps + As;                                                                                   // annot
    free invariant                                                                                                       // annot
        ( domain(Acc_Ns)             == As                                                                               // annot
        && domain(Acc_Max_Seen_N)     == As                                                                              // annot
        && domain(Acc_Max_Accepted_N) == As                                                                              // annot
        && domain(Acc_Soup)           == As                                                                              // annot
        && domain(Acc_MaxV)           == As                                                                              // annot

        && domain(Prop_Decided) == Ps                                                                                    // annot
        && domain(Prop_HO)      == Ps                                                                                    // annot
        && domain(Prop_HO2)     == Ps                                                                                    // annot
        && domain(Prop_Max)     == Ps                                                                                    // annot
        && domain(Prop_N)       == Ps                                                                                    // annot
        && domain(Prop_PC)      == Ps                                                                                    // annot
        && domain(Prop_Ready)   == Ps                                                                                    // annot
        && domain(Prop_Exec_P5) == Ps                                                                                    // annot
        && domain(Prop_Exec_P6) == Ps                                                                                    // annot
        && domain(Prop_Soup)    == Ps                                                                                    // annot
        && domain(Prop_V)       == Ps                                                                                    // annot
        && domain(Prop_WL)      == Ps                                                                                    // annot
        && domain(Prop_WL2)     == Ps                                                                                    // annot
        && domain(Prop_a)       == Ps                                                                                    // annot

        && domain(k)         == Ps                                                                                       // annot
        && domain(k_pending) == Ps                                                                                       // annot
        && domain(l)         == Ps                                                                                       // annot
        && domain(m)         == Ps                                                                                       // annot

        && domain(OneB_Hist)  == As                                                                                      // annot
        && domain(TwoB_Hist)  == As                                                                                      // annot
        && domain(Joined_Rnd) == As                                                                                      // annot

        && domain(Prop_Soup_Hist) == Ps                                                                                  // annot
        && domain(Acc_Soup_Hist)  == As                                                                                  // annot
        );                                                                                                               
    free invariant forall a:nat,pid:nat,msg:Msg_Acc :: a in As && (pid,msg) in Acc_Soup[a] ==> pid in Ps;                // annot
    free invariant forall p:nat,pid:nat,msg:Msg_Prop :: p in Ps && (pid,msg) in Prop_Soup[p] ==> pid in As;              // annot
    free invariant forall p:nat,pid:nat,msg:Msg_Prop :: p in Ps && (pid,msg) in Prop_Soup_Hist[p] ==> pid in As;         // annot
    free invariant forall p,a :: p in Ps && a == Prop_a[p] ==> a in As;                                                  // annot
    free invariant forall p :: p in Ps ==> Prop_WL[p] <= As && Prop_WL2[p] <= As;                                        // annot
    free invariant forall p :: p in Ps && Prop_Ready[p] ==> Prop_HO[p] > |As|/2;                                         // annot

    // ----------------------------------------------------------------------                                         

    free invariant forall n,v1,v2 :: (n,v1) in TwoA_Hist && (n,v2) in TwoA_Hist ==> v1 == v2; // (5)                     // annot
    free invariant forall a,p,n,v :: a in As && (p,Accept(n,v)) in Acc_Soup[a] ==> Prop_PC[p] !in {P0, P1, P2} && n == Prop_N[p] && v == Prop_V[p]; // annot
    free invariant forall n,v :: (n,v) in TwoA_Hist ==> exists p :: p in Ps && n == Prop_N[p] && v == Prop_V[p] && Prop_PC[p] !in {P0, P1, P2}; // annot
    free invariant forall p :: p in Ps ==> (Prop_Ready[p] ==> Prop_PC[p] !in {P0, P1, P2});                              // annot
    free invariant forall p :: p in Ps && Prop_PC[p] in {P4, P5, P6, P7} ==> Prop_Ready[p];                              // annot
    free invariant forall p :: p in Ps && Prop_Decided[p] ==> Prop_Ready[p];                                             // annot

    // ----------------------------------------------------------------------                                        

    free invariant forall a,n,v :: a in As && (n,v) in TwoB_Hist[a] ==> (n,v) in TwoA_Hist; // (6)                       // annot
    free invariant forall a,msg :: a in As && msg in Acc_Soup[a] ==> msg in Acc_Soup_Hist[a];                            // annot
    free invariant forall a,n,v :: a in As && (n,v) in TwoB_Hist[a] ==> (exists p :: p in Ps && (p, Accept(n,v)) in Acc_Soup_Hist[a]); // annot
    free invariant forall a,n,v,p :: a in As && (p, Accept(n,v)) in Acc_Soup_Hist[a] ==> (n,v) in TwoA_Hist;             // annot

    // ----------------------------------------------------------------------                                       

    free invariant forall p :: p in Ps ==> k[p] >= 0 && l[p] >= 0 && m[p] >= 0;                                          // annot
    free invariant forall p :: p in Ps ==> |As| == k[p] + l[p] + m[p];                                                   // annot
    free invariant forall p :: p in Ps && k[p] > |As|/2 ==> m[p] <= |As|/2;                                              // annot

    free invariant forall p :: p in Ps && Prop_Decided[p] ==> k[p] > |As|/2; // (7)                                      // annot
    free invariant forall p :: p in Ps ==> Prop_HO2[p] + k_pending[p] <= k[p];                                           // annot
    free invariant forall p :: p in Ps ==> k_pending[p] >= 0;                                                            // annot

    // ----------------------------------------------------------------------                                      

    free invariant forall a,vote :: a in As && vote in TwoB_Hist[a]==> vote.0 >= 0; // (11)                              // annot

    // ----------------------------------------------------------------------                                     

    free invariant forall a,no,maxn,maxv :: a in As && (no, maxn, maxv) in OneB_Hist[a] ==> no in Joined_Rnd[a]; // (15) // annot

    // ----------------------------------------------------------------------                                    

    free invariant forall a,n :: a in As && n in Joined_Rnd[a] ==> n <= Acc_Max_Seen_N[a]; // (14)                       // annot

    // ----------------------------------------------------------------------                                   

    free invariant forall a,msg,n :: a in As && msg in Acc_Soup[a] && msg.1 == Prepare(n) ==> n >= 0;                    // annot
    free invariant forall n :: n in OneA_Hist ==> n >= 0;                                                                // annot

    // ----------------------------------------------------------------------                                  

	  free invariant forall p,n,v :: (n,v) in TwoA_Hist && p in Ps && Prop_N[p] == n ==> Prop_Ready[p];                     // annot

    // ----------------------------------------------------------------------                                 

    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!                                                                     
    // !!! Required to prove the safety property !!!                                                                     
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!                                                                     
	  // free invariant forall p,p' :: p in Ps && p' in Ps && Prop_Ready[p'] && Prop_N[p] < Prop_N[p'] && Prop_V[p] != Prop_V[p'] ==> m[p] > |As|/2;
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!                                                                     

    // ----------------------------------------------------------------------                                           

    // invariant forall p1,p2 :: p1 in Ps && p2 in Ps && Prop_Decided[p1] && Prop_Decided[p2] ==> Prop_V[p1] == Prop_V[p2]; // (4) (safety property)

    // ----------------------------------------------------------------------                                           

    decreases *                                                                                                         
    {                                                                                                                   
      var processToRun := *; assume processToRun in WL_main;                                                             // harness

      if processToRun in As {                                                                                            // harness
        var a := processToRun;                                                                                           // harness

        /* while true                                                                                                    
             (pid, msg) <- recv                                                                                          
             match msg {                                                                                                 
               Prepare(no) =>                                                                                            
                 if max1 < no {                                                                                          
                   max1 <- no                                                                                            
                 }                                                                                                       
               Accept(no,val) =>                                                                                         
                 if max1 <= no {                                                                                         
                   ns <- ns U {no}                                                                                       
                   if max2 < no {                                                                                        
                     max2 <- no                                                                                          
                     v    <- val                                                                                         
                   }                                                                                                     
                 }                                                                                                       
             }                                                                                                           
             send pid (max1, max2, v)                                                                                    
           done                                                                                                          
         */                                                                                                              
        if Acc_Soup[a] != multiset{} {                                                                                   // harness
          var pid := *;                                                                                                  // code
          var msg := *;                                                                                                  // code

          assume (pid,msg) in Acc_Soup[a];                                                                               // code
          Acc_Soup := Acc_Soup[a := Acc_Soup[a] - multiset{(pid,msg)}];                                                  // harness

          var phase;                                                                                                     // code
          var old_max_seen_n := Acc_Max_Seen_N[a];                                                                       // code

          match msg {                                                                                                    // code
            case Prepare(no) =>                                                                                          // code
              if old_max_seen_n < no {                                                                                   // code
                // update counters m & l                                                                                 
                var onea_wl := Ps;                                                                                       // code
                while onea_wl != {}                                                                                      // code
                invariant onea_wl <= Ps;                                                                                 // annot
                invariant domain(l) == Ps && domain(m) == Ps;                                                            // annot
                invariant forall p :: p in Ps ==> k[p] >= 0 && l[p] >= 0 && m[p] >= 0;                                   // annot
                invariant forall p :: p in Ps ==> |As| == k[p] + l[p] + m[p];                                            // annot
                decreases |onea_wl|                                                                                      // annot
                {                                                                                                        
                  var p' := *; assume p' in onea_wl;                                                                     // code

                  if Prop_N[p'] !in Acc_Ns[a] &&                                                                         // code
                    Prop_N[p'] >= Acc_Max_Seen_N[a] &&                                                                   // code
                    Prop_N[p'] < no &&                                                                                   // code
                    l[p'] > 0 {                                                                                          // code
                      m := m[p' := m[p'] + 1];                                                                           // code
                      l := l[p' := l[p'] - 1];                                                                           // code
                  }                                                                                                      // code
                  onea_wl := onea_wl - {p'};                                                                             // code
                }                                                                                                       

                Acc_Max_Seen_N := Acc_Max_Seen_N[a := no];                                                               // code
                Joined_Rnd := Joined_Rnd[a := Joined_Rnd[a] + {no}];                                                     // code
              }                                                                                                          

              phase := OneB;                                                                                             // code
            case Accept(no,val) =>                                                                                       // code
              if old_max_seen_n <= no  {                                                                                 // code
                Acc_Ns := Acc_Ns[a := Acc_Ns[a] + {no}];                                                                 // code

                if Acc_Max_Accepted_N[a] <= no {                                                                         // code
                  Acc_MaxV := Acc_MaxV[a := val];                                                                        // code
                  Acc_Max_Accepted_N := Acc_Max_Accepted_N [a := no];                                                    // code
                }

                assume l[pid] > 0;                                                                                       // code
                k := k[pid := k[pid] + 1];                                                                               // code
                l := l[pid := l[pid] - 1];                                                                               // code
              }                                                                                                          // code

              phase := TwoB;                                                                                             // code
          }                                                                                                              // code

          if * {                                                                                                         // code
            var max_seen_n     := Acc_Max_Seen_N[a];                                                                     // code
            var max_accepted_n := Acc_Max_Accepted_N[a];                                                                 // code
            var maxv           := Acc_MaxV[a];                                                                           // code

            var resp := (a, Value(max_seen_n, max_accepted_n, maxv, phase));                                             // code

            Prop_Soup := Prop_Soup[pid := Prop_Soup[pid] + multiset{resp}];                                              // code
            Prop_Soup_Hist := Prop_Soup_Hist[pid := Prop_Soup_Hist[pid] + {resp}];                                       // code

            // history variable update                                                                                   // code
            match msg {                                                                                                  // code
              case Prepare(no) =>                                                                                        // code
                if old_max_seen_n < no {                                                                                 // code
                  OneB_Hist := OneB_Hist[a := OneB_Hist[a] + {(no, max_accepted_n, maxv)}];                              // code
                }                                                                                                        // code
              case Accept(no,val) =>                                                                                     // code
                if old_max_seen_n <= no {                                                                                // code
                  TwoB_Hist := TwoB_Hist[a := TwoB_Hist[a] + {(no,val)}];                                                // code
                  k_pending := k_pending[pid := k_pending[pid] + 1];                                                     // code
                }                                                                                                        // code
            }                                                                                                            // code
          }                                                                                                              // code
        }                                                                                                                // code
      }                                                                                                                  // code

      else if processToRun in Ps {                                                                                       // code
        var p := processToRun;                                                                                           // code

        if Prop_PC[p] == P0 {                                                                                            // code
          /* for a in A:                                                                                                 // code
               <P1>                                                                                                      // code
               <P2>                                                                                                      // code
             done                                                                                                        // code
           */                                                                                                            // code
          if Prop_WL[p] != {} {                                                                                          // code
            var a := *; assume a in Prop_WL[p];                                                                          // code

            Prop_a := Prop_a[p := a];                                                                                    // code
            Prop_WL := Prop_WL[p := Prop_WL[p] - {a}];                                                                   // code
            Prop_PC := Prop_PC[p := P1];                                                                                 // code
          } else {                                                                                                       // code
            Prop_PC := Prop_PC[p := P3];                                                                                 // code
          }                                                                                                              // code

        } else if Prop_PC[p] == P1 {                                                                                     // code
          /* send a (p, Prepare(n))                                                                                      // code
           */                                                                                                            // code
          var a := Prop_a[p];                                                                                            // code
          var n := Prop_N[p];                                                                                            // code

          Acc_Soup := Acc_Soup[a := Acc_Soup[a] + multiset{(p, Prepare(n))}];                                            // code
          Acc_Soup_Hist := Acc_Soup_Hist[a := Acc_Soup_Hist[a] + {(p, Prepare(n))}];                                     // code

          // history update                                                                                              // code
          OneA_Hist := OneA_Hist + {n};                                                                                  // code

          Prop_PC := Prop_PC[p := P2];                                                                                   // code

        } else if Prop_PC[p] == P2 {                                                                                     // code
          /* reply <- recvTO(a);                                                                                         // code
             match reply {                                                                                               // code
               None =>                                                                                                   // code
                 return ()                                                                                               // code
               Some Value(no, val, OneB) =>                                                                              // code
                 if no > max {                                                                                           // code
                   max <- no                                                                                             // code
                   v   <- val                                                                                            // code
                 }                                                                                                       // code
                 ho <- ho + 1                                                                                            // code
             }                                                                                                           // code
           */                                                                                                            // code
          var a := Prop_a[p];                                                                                            // code
          var n := Prop_N[p];                                                                                            // code

          if * {                                                                                                         // code
            if Prop_Soup[p] != multiset{} {                                                                              // code
              var pid := *;                                                                                              // code
              var msg := *;                                                                                              // code

              assume (pid,msg) in Prop_Soup[p];                                                                          // code
              Prop_Soup := Prop_Soup[p := Prop_Soup[p] - multiset{(pid,msg)}];                                           // code

              if msg.max_seen_n < n {                                                                                    // code
                if msg.max_accepted_n > Prop_Max[p] {                                                                    // code
                  Prop_Max := Prop_Max[p := msg.max_accepted_n];                                                         // code
                  Prop_V   := Prop_V  [p := msg.max_val];                                                                // code
                }                                                                                                        // code
                Prop_HO := Prop_HO[p := Prop_HO[p] + 1];                                                                 // code
              }                                                                                                          // code

              Prop_PC := Prop_PC[p := P0];                                                                               // code
            }                                                                                                            // code
          } else {                                                                                                       // code
            Prop_PC := Prop_PC[p := P0];                                                                                 // code
          }                                                                                                              // code

        } else if Prop_PC[p] == P3 {                                                                                     // code
          /* if 2 x ho > |A| {                                                                                           // code
               ready <- true                                                                                             // code
               <P4>                                                                                                      // code
             }                                                                                                           // code
             <P8>                                                                                                        // code
           */                                                                                                            // code
          var ho := Prop_HO[p];                                                                                          // code
          if ho * 2 > |As| {                                                                                             // code
            Prop_Ready := Prop_Ready[p := true];                                                                         // code
            Prop_PC    := Prop_PC   [p := P4];                                                                           // code
          } else {                                                                                                       // code
            Prop_PC := Prop_PC[p := P8];                                                                                 // code
          }                                                                                                              // code

        } else if Prop_PC[p] == P4 {                                                                                     // code
          /* for a in A:                                                                                                 // code
               <P5>                                                                                                      // code
               <P6>                                                                                                      // code
             done                                                                                                        // code
             <P7>                                                                                                        // code
           */                                                                                                            // code
          if Prop_WL2[p] != {} {                                                                                         // code
            var a := *; assume a in Prop_WL2[p];                                                                         // code

            Prop_a := Prop_a[p := a];                                                                                    // code
            Prop_WL2 := Prop_WL2[p := Prop_WL2[p] - {a}];                                                                // code
            Prop_PC := Prop_PC[p := P5];                                                                                 // code
          } else {                                                                                                       // code
            Prop_PC := Prop_PC[p := P7];                                                                                 // code
          }                                                                                                              // code

        } else if Prop_PC[p] == P5 {                                                                                     // code
          /* send a (p, Accept(n))                                                                                       // code
           */                                                                                                            // code
          var a := Prop_a[p];                                                                                            // code
          var n := Prop_N[p];                                                                                            // code
          var v := Prop_V[p];                                                                                            // code

          Acc_Soup := Acc_Soup[a := Acc_Soup[a] + multiset{(p, Accept(n,v))}];                                           // code
          Acc_Soup_Hist := Acc_Soup_Hist[a := Acc_Soup_Hist[a] + {(p, Accept(n,v))}];                                    // code

          // history update                                                                                              // code
          TwoA_Hist := TwoA_Hist + {(n,v)};                                                                              // code
          Prop_Exec_P5 := Prop_Exec_P5[p := true];                                                                       // code

          Prop_PC := Prop_PC[p := P6];                                                                                   // code

        } else if Prop_PC[p] == P6 {                                                                                     // code
          /* reply <- recvTO(a);                                                                                         // code
             match reply {                                                                                               // code
               None =>                                                                                                   // code
                 return ()                                                                                               // code
               Some Value(no, val, TwoB) =>                                                                              // code
                 if no = n {                                                                                             // code
                   ho2 <- ho2 + 1                                                                                        // code
                 }                                                                                                       // code
             }                                                                                                           // code
           */                                                                                                            // code
          var a := Prop_a[p];                                                                                            // code

          if * {                                                                                                         // code
            if Prop_Soup[p] != multiset{} {                                                                              // code
              var pid := *;                                                                                              // code
              var msg := *;                                                                                              // code

              assume (pid,msg) in Prop_Soup[p];                                                                          // code
              Prop_Soup := Prop_Soup[p := Prop_Soup[p] - multiset{(pid,msg)}];                                           // code

              if Prop_N[p] >= msg.max_seen_n {                                                                           // code
                Prop_HO2 := Prop_HO2[p := Prop_HO2[p] + 1];                                                              // code
                assume k_pending[p] > 0;                                                                                 // code
                k_pending := k_pending[p := k_pending[p] - 1];                                                           // code
              }                                                                                                          // code

              Prop_Exec_P6 := Prop_Exec_P6[p := true];                                                                   // code
              Prop_PC := Prop_PC[p := P4];                                                                               // code
            }                                                                                                            // code
          } else {                                                                                                       // code
            Prop_Exec_P6 := Prop_Exec_P6[p := true];                                                                     // code
            Prop_PC := Prop_PC[p := P4];                                                                                 // code
          }                                                                                                              // code

        } else if Prop_PC[p] == P7 {                                                                                     // code
          /* if ho2 * 2 > |A| {                                                                                          // code
               decided <- true                                                                                           // code
             }                                                                                                           // code
           */                                                                                                            // code
          var ho2 := Prop_HO2[p];                                                                                        // code
          if ho2 * 2 > |As| {                                                                                            // code
            Prop_Decided := Prop_Decided[p := true];                                                                     // code
          }                                                                                                              // code
          Prop_PC := Prop_PC[p := P8];                                                                                   // code
        } else if Prop_PC[p] == P8 {                                                                                     // code
          WL_main := WL_main - {p};                                                                                      // code
        }                                                                                                                // code
      }                                                                                                                  // code
    }                                                                                                                    // code
  }                                                                                                                      // code
}                                                                                                                        // code
