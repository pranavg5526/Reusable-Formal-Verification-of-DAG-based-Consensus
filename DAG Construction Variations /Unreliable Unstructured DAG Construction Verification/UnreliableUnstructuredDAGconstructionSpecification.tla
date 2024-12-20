----------------------- MODULE hashgraphCommunication -----------------------


EXTENDS FiniteSets,
        Integers,
        Sequences,
        TLAPS,
        TLC

CONSTANTS EventSet,                    \* possible set of events
          f,                           \* maximum number of byzentine faulty processes allowed 
          r,                           \* bound on number of witnesses an honest process creates
          k,                           \* bound on number of events a honest process creates
          WitnessSet,                  \* possible set of witnesses
          Path(_, _),                  \* path function via parent relation among events
          PossibleWitnessOfEvent(_),   \* possible witness of a event from based on its history
          Blocks

----------------------------------------------------------------------------
ASSUME fAs == f \in Nat

ProcessSet == 1..(3*f+1)

Frames == 1..r

BlockIds == 1..k


ASSUME PathAs == 
  \A e \in EventSet, u \in EventSet: 
      Path(e, u) = IF e = u THEN TRUE
                   ELSE IF e.id = 1 THEN FALSE
                        ELSE Path(e.selfparent, u) \/ Path(e.otherparent, u)

DonotSeeFork(v, u) == 
  /\ Path(v, u) 
  /\ \A x \in EventSet: ( /\ x.id = u.id 
                          /\ x.source = u.source)
                            => Path(v, x) = FALSE
Sees(v, u) ==
  /\ Path(v, u)
  /\ \A x \in EventSet: (x.source = u.source /\ Path(u, x) => DonotSeeFork(v, x))
  
StronglySees(e, a) == 
  \E B \in SUBSET(EventSet): 
      /\ Cardinality({ q \in ProcessSet : \E x \in B: x.source = q }) > 2*f
      /\ \A z \in B : Path(e, z) = TRUE /\ Sees(z, a)
                                  
max(a, b) == IF a <= b THEN b ELSE a

ASSUME PossibleWitnessOfEventAs == 
  \A e \in EventSet:                                       
     PossibleWitnessOfEvent(e) = 
       IF e.id = 1 
       THEN [frame |-> 1,
             source |-> e.source, 
             block |-> e.block, 
             event |-> e, 
             stronglysees |-> {}, 
             witness |-> TRUE]
       ELSE LET x == max( PossibleWitnessOfEvent(e.selfparent).frame, 
                               PossibleWitnessOfEvent(e.otherparent).frame)
            IN LET A == {a \in EventSet : 
                           \/ (StronglySees(e, a) =>
                               /\ PossibleWitnessOfEvent(a).frame = x 
                               /\ PossibleWitnessOfEvent(a).witness = TRUE) 
                           \/ FALSE} 
               IN IF Cardinality({q \in ProcessSet : 
                                   \E a \in A : a.source = q}) > 2*f 
                  THEN [frame |-> x+1, 
                        source |-> e.source, 
                        block |-> e.block, 
                        event |-> e, 
                        stronglysees |-> A, 
                        witness |-> TRUE]
                  ELSE LET B == {a \in EventSet : 
                                   \/ (StronglySees(e, a) =>
                                       /\ PossibleWitnessOfEvent(a).frame = x-1 
                                       /\ PossibleWitnessOfEvent(a).witness = TRUE) 
                                   \/ FALSE}
                       IN [frame |-> x, 
                           source |-> e.source, 
                           block |-> e.block, 
                           event |-> e, 
                           stronglysees |-> B, 
                           witness |-> x > PossibleWitnessOfEvent(e.selfparent).frame]

WitnessOfEvent(e) == 
  IF PossibleWitnessOfEvent(e).witness = FALSE THEN "Nil"
  ELSE [frame |-> PossibleWitnessOfEvent(e).frame, 
        source |-> PossibleWitnessOfEvent(e).source, 
        block |-> PossibleWitnessOfEvent(e).block, 
        event |-> PossibleWitnessOfEvent(e).event, 
        stronglysees |-> PossibleWitnessOfEvent(e).stronglysees]


ASSUME WitnessSetTypeAs ==
  WitnessSet \in SUBSET([frame : Frames,
                         source : ProcessSet,
                         block : Blocks,
                         event : EventSet,
                         stronglysees : SUBSET(WitnessSet)])

ASSUME WitnessSetAs == 
  /\ \A e \in WitnessSet: \A a \in e.stronglysees : a.frame = e.frame-1
  /\ \A e \in EventSet: WitnessOfEvent(e) \in WitnessSet
  /\ \A e \in WitnessSet: WitnessOfEvent(e.event) = e
  
Genesis(p) == [source |-> p,
               block |-> "Empty",
               id |-> 1,
               selfparent |-> "Nil",
               otherparent |-> "Nil"]

ASSUME EventSetTypeAs == 
  /\ EventSet \in SUBSET([source : ProcessSet,
                          block : Blocks,
                          id : BlockIds,
                          selfparent : EventSet \cup {"Nil"},
                          otherparent : EventSet \cup {"Nil"}])

ASSUME EventSetAs == \A p \in ProcessSet: Genesis(p) \in EventSet

ASSUME BlocksAs == "Empty" \in Blocks                  
----------------------------------------------------------------------------                     

VARIABLE witnessDAG, hashgraph, tip, faulty

vars == 
  << witnessDAG, hashgraph, tip, faulty >>

TypeOK == 
  /\ witnessDAG \in [ProcessSet -> [Frames -> 
                      [ProcessSet -> SUBSET(WitnessSet)]]]
  /\ hashgraph \in [ProcessSet -> [ProcessSet -> 
                      [BlockIds -> SUBSET(EventSet)]]]
  /\ tip \in [ProcessSet -> EventSet]
  /\ faulty \in SUBSET(ProcessSet)

Init ==
  /\ witnessDAG = [p \in ProcessSet |-> [l \in Frames |->
                       [q \in ProcessSet |-> {}]]]
  /\ hashgraph = [p \in ProcessSet |-> [q \in ProcessSet |-> 
                       [x \in BlockIds |-> IF x = 1 /\ p = q THEN {Genesis(p)}
                                           ELSE {}]]]
  /\ tip = [p \in ProcessSet |-> Genesis(p)]
  /\ faulty = {}

---------------------------------------------------------------------------

ProcessFailureTn(p) == 
  /\ Cardinality(faulty) < f
  /\ p \notin faulty
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<witnessDAG, hashgraph, tip>>

---------------------------------------------------------------------------
   
FaultyChangeHashgraphTn(p, q, x, E) ==
   /\ p \in faulty
   /\ hashgraph' = [hashgraph EXCEPT ![p][q][x] = E]
   /\ UNCHANGED <<witnessDAG, faulty, tip>>
   
---------------------------------------------------------------------------

ReceiveEventTn(e, p, z) ==  
   /\ e \notin hashgraph[p][e.source][e.id] /\ e.source # p 
   /\ e \in hashgraph[e.source][e.source][e.id]
   /\ e.id # 1 => 
       /\ e.id > 1
       /\ e.selfparent.source = e.source /\ e.selfparent.id = e.id-1
       /\ e.otherparent.source # e.source
       /\ \A u \in EventSet: Path(e, u) => u \in hashgraph[p][u.source][u.id]
   /\ e.id = 1 => e.selfparent = "Nil" /\ e.otherparent = "Nil"
   /\ z.source = p /\ z.otherparent = e
   /\ z.selfparent = tip[p] /\ z.id = tip[p].id+1
   /\ \A u \in EventSet: Path(z, u) => u \in hashgraph[p][u.source][u.id]
   /\ \A u \in EventSet: u.source = p /\ u \in hashgraph[p][u.source][u.id] 
           => Path(z, u) /\ u.id < z.id
   /\ tip' = [tip EXCEPT ![p] = z]
   /\ hashgraph' = [hashgraph EXCEPT ![p] = 
                     [q \in ProcessSet |-> [l \in BlockIds |-> 
                                 IF q = z.source /\ l = z.id 
                                 THEN hashgraph[p][q][l] \cup {z}
                                 ELSE IF q = e.source /\ l = e.id 
                                      THEN hashgraph[p][q][l] \cup {e}
                                      ELSE hashgraph[p][q][l]]]]
   /\ UNCHANGED <<witnessDAG, faulty>>

---------------------------------------------------------------------------

DecideWitnessTn(e, p) == 
   /\ e \in hashgraph[p][e.source][e.id]
   /\ WitnessOfEvent(e) # "Nil"
   /\ \A u \in WitnessOfEvent(e).stronglysees : 
             u \in witnessDAG[p][u.frame][u.source]
   /\ witnessDAG' = 
       [witnessDAG EXCEPT ![p][WitnessOfEvent(e).frame][WitnessOfEvent(e).source] 
          = witnessDAG[p][WitnessOfEvent(e).frame][WitnessOfEvent(e).source] 
              \cup {WitnessOfEvent(e)}]
   /\ UNCHANGED <<hashgraph, tip, faulty>> 

---------------------------------------------------------------------------

Next == 
  \E e \in EventSet, z \in EventSet, x \in BlockIds, 
     p \in ProcessSet, q \in ProcessSet, E \in SUBSET(EventSet):
        \/ ProcessFailureTn(p)
        \/ FaultyChangeHashgraphTn(p, q, x, E)
        \/ ReceiveEventTn(e, p, z)
        \/ DecideWitnessTn(e, p)
        
Spec == 
  Init /\ [][Next]_vars

---------------------------------------------------------------------------

UniqueStronglyseen == 
  \A p \in ProcessSet, q \in ProcessSet, e \in WitnessSet, a \in WitnessSet: 
      (/\ p \notin faulty /\ q \notin faulty
       /\ a.frame = e.frame 
       /\ a.source = e.source 
       /\ \E s \in WitnessSet: /\ s \in witnessDAG[q][s.frame][s.source] 
                               /\ a \in s.stronglysees
       /\ \E l \in WitnessSet: /\ l \in witnessDAG[p][l.frame][l.source] 
                               /\ e \in l.stronglysees) => a = e

Safety == Spec => []UniqueStronglyseen

--------------------------------------------------------------------------- 
=============================================================================
\* Modification History
\* Last modified Sun Sep 22 16:54:53 AEST 2024 by pgho0778
\* Created Wed Sep 11 12:22:10 AEST 2024 by pgho0778