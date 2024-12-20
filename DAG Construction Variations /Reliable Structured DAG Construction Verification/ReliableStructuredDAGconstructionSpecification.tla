-------------- MODULE ReliableBcastCommunicationSpecification --------------
(* The DAG-Rider Specification defines a state transition system  for the  *)
(* DAG-Rider protocol, and its safety properties. The article for the      *)
(* protocol can be found here:   https://arxiv.org/abs/2102.08325          *)

EXTENDS FiniteSets,
        Integers,
        Sequences,
        TLAPS,
        TLC

-----------------------------------------------------------------------------

(*--------------------------------CONSTANTS--------------------------------*)

(* NumProcessors is the number of participating processes in the protocol. *)
(* We assume this is non zero. We number processes 1 to NumProcessors,     *)
(* and define ProcessorSet as the set of participating processes.          *) 
(* We define maximum allowed process failures (f) as the *)
(* greatest integer less than one third of the total number of processes.  *)

CONSTANT NumProcessors

ASSUME NumProcessorAsm == 
   NumProcessors \in Nat\{0}

f == 
   (NumProcessors-1) \div 3

ProcessorSet == 
   1..NumProcessors

ASSUME ProcSetAsm == 
   "History" \notin ProcessorSet

-----------------------------------------------------------------------------

(* NumWaves is the number of waves after which the protocol will stop, we  *)
(* assume this is non zero. We number waves from 1 to NumWaves and define  *)
(* WaveSet as the set of waves. A wave consists of 4 rounds. We define     *)
(* RoundSet as set of rounds along with an initial round 0.                *)

CONSTANT NumWaves

ASSUME NumWaveAsm == 
   NumWaves \in Nat\{0}

WaveSet == 
   1..NumWaves

RoundSet == 
   0..(4*NumWaves)

-----------------------------------------------------------------------------

(* BlockSet is a set of blocks that can be proposed by participating proc- *)
(* esses.                                                                  *)

CONSTANT BlockSet

-----------------------------------------------------------------------------

(* ChooseLeader(_) is function that maps WaveSet to ProcessorSet.          *)

CONSTANT ChooseLeader(_)

-----------------------------------------------------------------------------

(* Since we have bounded the number waves, there is a finite set off vert- *)
(* ices (VertexSet), which can be created by the participating processes.  *)
(* To define VertexSet, we first define ZeroRoundVertexSet (i.e.,a set of  *)
(* dummy vertices in round 0 of the DAG). Then, we define set              *)
(* UntilRoundVertex(r), which is set of vertices till round r. It is       *)
(* important to note that a vertex as defined in DAG-rider is not a vertex *)
(* but a rooted DAG (aka. downset). The downset stores the entire causal   *)
(* history of the node.                                                    *) 

ZeroRoundVertex(p) == 
   [round |-> 0, 
    source |-> p, 
    block |-> "Empty", 
    strongedges |-> {}, 
    weakedges |-> {}]

ZeroRoundVertexSet == 
   {ZeroRoundVertex(p) : p \in ProcessorSet}

RECURSIVE UntilRoundVertex(_)

UntilRoundVertex(r) == 
  IF r = 0
  THEN ZeroRoundVertexSet
  ELSE UntilRoundVertex(r-1) \cup [round : {r}, 
                                   source : ProcessorSet, 
                                   block : BlockSet, 
                                   strongedges : SUBSET(UntilRoundVertex(r-1)),
                                   weakedges : SUBSET(UntilRoundVertex(r-1))]  

VertexSet == UntilRoundVertex(4*NumWaves)

-----------------------------------------------------------------------------

(* When a vertex is broadcast the broadcast tags the vertex with its sender*)
(* and the round in which it was sent. TaggedVertexSet is set of all such  *)
(* tagged vertices.                                                        *)

TaggedVertexSet == 
   [sender : ProcessorSet, inRound : RoundSet, vertex : VertexSet]

-----------------------------------------------------------------------------

(* NilVertex(p, r) is a vertex which represents the non-existence of a mes-*)
(* sage and whose block is Nil. To make the DAG more expressive we assume  *)
(* that DAG of every process has a vertex in every round created by every  *)
(*  process. In practice, a process q might not have added a vertex created*)
(* by process p in round r in this case we assume that it has a Nil-       *)
(* Vertex(p, r).  We define NilVertexSet as the set of all nil vertices.   *)

NilVertex(p, r) == 
   [round |-> r,
    source |-> p,
    block |-> "Nil",
    strongedges |-> {},
    weakedges |-> {}]

NilVertexSet == 
   {NilVertex(p, r) : p \in ProcessorSet, r \in RoundSet}

-----------------------------------------------------------------------------

(*--------------------------STATE-VARIABLES--------------------------------*)

(* For every process p, blocksToPropose stores a sequence of blocks that   *)
(* are proposed but not yet initialized to order (blocks whose vertex is  *)
(* not yet created by the process).                                        *)

VARIABLE blocksToPropose

BlocksToProposeType == 
   blocksToPropose \in [ProcessorSet -> Seq(BlockSet)]

InitBlocksToPropose ==  
   blocksToPropose = [p \in ProcessorSet |-> <<>> ]

-----------------------------------------------------------------------------

(* For every process p, broadcastNetwork stores set of  TaggedVertices that*)
(* are broadcasted but not yet received by p. Additionally it also stores  *)
(* history of all the TaggedVertices ever broadcasted on the network.      *)

VARIABLE broadcastNetwork

BroadcastNetworkType == 
   broadcastNetwork \in [ProcessorSet \cup 
                         {"History"} ->SUBSET(TaggedVertexSet)]

InitBroadcastNetwork == 
   broadcastNetwork = [p \in ProcessorSet \cup {"History"} |-> {}]

-----------------------------------------------------------------------------

(* For every process p and round r, broadcastRecord stores weather or not  *)
(* process p broadcasted a vertex in round r.                              *)

VARIABLE broadcastRecord

BroadcastRecordType == 
   broadcastRecord \in [ProcessorSet -> [RoundSet -> BOOLEAN]]

InitBroadcastRecord == 
   broadcastRecord = [p \in ProcessorSet |-> 
      [ r \in RoundSet |-> IF r = 0 THEN TRUE ELSE FALSE ]]

-----------------------------------------------------------------------------

(* For every process p, buffer stores set of vertices received by p via    *)
(* the broadcast.                                                          *)

VARIABLE buffer

BufferType == 
   buffer \in [ProcessorSet -> SUBSET(VertexSet)]

InitBuffer ==
   buffer = [p \in ProcessorSet |-> {}]

-----------------------------------------------------------------------------

(* For every process p, round r, process q, dag stores vertex in the DAG   *)
(* of process p created by process q in round r, if such a vertex does not *)
(* exists in the DAG then it stores NilVertex(q, r).                       *)

VARIABLE dag

DagType == 
   dag \in [ProcessorSet -> 
      [RoundSet  -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]

InitDag == 
   dag = [p \in ProcessorSet |-> 
      [r \in RoundSet  |-> [q \in ProcessorSet |-> 
         IF r = 0 
         THEN ZeroRoundVertex(q) 
         ELSE NilVertex(q, r)]]]

-----------------------------------------------------------------------------

(* For every process p, round stores the round of DAG construction for     *)
(* process p.                                                              *) 

VARIABLE round

RoundType == 
   round \in [ProcessorSet -> RoundSet]

InitRound == 
   round = [p \in ProcessorSet |-> 0]

-----------------------------------------------------------------------------

VARIABLE faulty

FaultyType == 
    faulty \in SUBSET(ProcessorSet)
    
InitFaulty ==
    faulty = {}
-----------------------------------------------------------------------------

(*-------------------------STATE-TRANSITIONS-------------------------------*)

(* Before defining transitions we define some useful functions:            *)
(*  (1) Path(u, v): Boolean function that returns true if v is in causal   *)
(*      history of u.                                                      *)
(*  (2) StrongPath(u, v): Boolean function that returns true if v is in    *)
(*      strong causal history of u.                                        *)
(*  (3) InAddedVertex(p, r): Function on a system state. Returns added     *)
(*      vertices in round r of p's current DAG.                            *)
(*  (4) UntilAddedVertex(p, r): Function on a system state. Returns added  *)
(*      till round r of p's current DAG.                                   *)
(*  (5) NoPathVertices(p, r): Function on a system state. Returns set of   *)
(*      added vertices till round r of p's current DAG, which do not have  *)
(*      path from any of the added vertex in round r.                      *)
(*  (3) WaveLeader(p, w): Function on a system state. Returns p's leader   *)
(*      vertex of wave w.                                                  *)

RECURSIVE Path(_, _)
Path(u, v) == 
   IF u = v
   THEN TRUE
   ELSE IF u.round = 0
        THEN FALSE
        ELSE \E x \in u.weakedges \cup u.strongedges : Path(x, v)

RECURSIVE StrongPath(_, _)
StrongPath(u, v) == 
   IF u = v
   THEN TRUE
   ELSE IF u.round = 0
        THEN FALSE
        ELSE \E x \in u.strongedges : StrongPath(x, v)

InAddedVertex(p, r) == 
   {v \in VertexSet : v.round = r /\ dag[p][r][v.source] = v}

UntilAddedVertex(p, r) == {v \in VertexSet : v.round <= r /\ dag[p][v.round][v.source] = v}

AddedVertices(p) == {v \in VertexSet : dag[p][v.round][v.source] = v}

NoPathVertices(p, r) == {v \in UntilAddedVertex(p, r) : 
                         (\A w \in InAddedVertex(p, r) : ~Path(w,v))}                         

WaveLeader(p, w) == dag[p][4*w-3][ChooseLeader(w)]

-----------------------------------------------------------------------------

ProcessFailureTn(p) == 
  /\ Cardinality(faulty) < f
  /\ p \notin faulty
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<blocksToPropose, broadcastNetwork, broadcastRecord, buffer, dag, 
          round>>

-----------------------------------------------------------------------------

(* Transition ProposeTn(p, b) encodes process p proposing block b.         *)

ProposeTn(p, b) == 
   /\ blocksToPropose' = [blocksToPropose EXCEPT 
         ![p] = Append(blocksToPropose[p], b)]
   /\ UNCHANGED <<broadcastNetwork, broadcastRecord, buffer, dag, round, faulty>>

-----------------------------------------------------------------------------

(* Transition NextRoundTn(p) encodes process p moving to the next round of *)
(* DAG construction.  Upon completion of the current round process p moves *)
(* to the next round by creating (CreateVertex) and broadcasting (Broadcast*)
(* a new vertex. Additionally, when next round leads to a new wave it tries*)
(* to decide the current wave (ReadyWave), if decide condition is satisfied*)
(* it takes UpdateDecidedWaveTn in LeaderConsensus.                        *)

CreateVertex(p, r) == 
   [round |-> r, 
    source |-> p, 
    block |-> Head(blocksToPropose[p]), 
    strongedges |-> InAddedVertex(p, r-1),
    weakedges |-> NoPathVertices(p, r-1)]

Broadcast(p, r, v) == 
   IF broadcastRecord[p][r] = FALSE
   THEN /\ broadcastRecord' = [broadcastRecord EXCEPT ![p][r] = TRUE]
        /\ broadcastNetwork' = [q \in ProcessorSet \cup {"History"} 
              |-> broadcastNetwork[q] \cup 
                  {[sender |-> p, inRound |-> r, vertex |-> v]}]
   ELSE UNCHANGED <<broadcastNetwork, broadcastRecord>>


NextRoundTn(p) ==  
   /\ round[p]+1 \in RoundSet
   /\ Cardinality(InAddedVertex(p, round[p])) > 2*f
   /\ blocksToPropose[p] # <<>>
   /\ Broadcast(p, round[p]+1, CreateVertex(p, round[p]+1))
   /\ round' = [round EXCEPT ![p] = round[p]+1]
   /\ blocksToPropose' = [blocksToPropose EXCEPT 
         ![p] = Tail(blocksToPropose[p])]
   /\ UNCHANGED <<buffer, dag, faulty>>


-----------------------------------------------------------------------------

(* Transition ReceiveVertexTn(p, q, r, v) encodes process p receiving      *)
(* vertex v created in round r by process q.                               *)

ReceiveVertexTn(p, q, r, v) == 
   /\ [sender |-> q, inRound |-> r, vertex |-> v] \in broadcastNetwork[p]
   /\ p \notin faulty => v.source = q
   /\ p \notin faulty => v.round = r
   /\ p \notin faulty => Cardinality(v.edges) > 2*f
   /\ buffer' = [buffer EXCEPT ![p] = buffer[p] \cup {v}]
   /\ broadcastNetwork' = [broadcastNetwork EXCEPT 
         ![p] = broadcastNetwork[p] \ 
             {[sender |-> q, inRound |-> r, vertex |-> v]}]
   /\ UNCHANGED <<blocksToPropose, broadcastRecord, dag, round, faulty>>

-----------------------------------------------------------------------------

(* Transition AddVertexTn(p, v) encodes process p adding  vertex v from the*)
(* buffer to the DAG. Additionally, if v is a leader vertex of some wave   *)
(* then UpdateWaveTn is performed on LeaderConsensus. For this update, we  *)
(* compute set of waves whose leader vertex in p, is in strong causal      *)
(* history of v (ReachableWaveLeaders).                                    *)

AddVertexTn(p, v) == 
   /\ v \in buffer[p]
   /\ p \notin faulty => v.round <= round[p]
   /\ p \notin faulty => dag[p][v.round][v.source] = NilVertex(v.source, v.round)
   /\ p \notin faulty => v.edges \in InAddedVertex(p, v.round -1)
   /\ dag'= [dag EXCEPT ![p][v.round][v.source] = v]
   /\ UNCHANGED <<blocksToPropose, broadcastNetwork, 
                  broadcastRecord, buffer, round, faulty>>

-----------------------------------------------------------------------------

FaultyBcastTn(p ,v, r) ==
   /\ p \in faulty
   /\ Broadcast(p, r, v)
   /\ UNCHANGED <<blocksToPropose, buffer, dag, round, faulty>>


(*--------------------------TRANSITION-SYSTEM------------------------------*)

(* To complete the transition system specification, we define Init, Next,  *)
(* vars, Spec. Typical TLA+ macro names for the initial state, possible    *)
(* actions leading to the next state, the variables, and the system spec-  *)
(* ification, respectively.                                                *)

StateType ==
   /\ BlocksToProposeType
   /\ BroadcastNetworkType
   /\ BroadcastRecordType
   /\ BufferType
   /\ DagType
   /\ RoundType
   /\ FaultyType

Init == 
   /\ InitBlocksToPropose
   /\ InitBroadcastNetwork
   /\ InitBroadcastRecord
   /\ InitBuffer
   /\ InitDag
   /\ InitRound
   /\ InitFaulty

Next == 
   \E p \in ProcessorSet, r \in RoundSet, v \in VertexSet, b \in BlockSet: 
      \E q \in ProcessorSet\{p}: 
         \/ ProposeTn(p, b)
         \/ NextRoundTn(p)
         \/ ReceiveVertexTn(p, q, r, v)
         \/ AddVertexTn(p, v)
         \/ ProcessFailureTn(p)
         \/ FaultyBcastTn(p ,v, r)

vars == <<blocksToPropose, broadcastNetwork, broadcastRecord, buffer, dag, 
          round, faulty>>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(*--------------------------SAFETY-INVARIANTS------------------------------*)

(* DagConsistency state that if vertex created by a process o in a round r *)
(* is added to the DAG of process p and q then they are the same vertices. *)
(* Note that a vertex stores its entire causal history, thus their causal  *)
(* histories are same.                                                     *)

DagConsistency == 
   \A p, q \in ProcessorSet, r \in RoundSet, o \in ProcessorSet: 
     (/\ p \notin faulty
      /\ q \notin faulty
      /\ r # 0 
      /\ dag[p][r][o] \in VertexSet 
      /\ dag[q][r][o] \in VertexSet ) => dag[p][r][o] = dag[q][r][o]

-----------------------------------------------------------------------------

=============================================================================
