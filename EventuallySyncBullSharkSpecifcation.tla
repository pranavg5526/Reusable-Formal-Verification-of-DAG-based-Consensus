---------------------- MODULE FMBullsharkSpecifcation ----------------------

EXTENDS FiniteSets,
        Integers,
        Sequences,
        TLAPS,
        TLC

-----------------------------------------------------------------------------

(*--------------------------------CONSTANTS--------------------------------*)

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

CONSTANT NumWaves

ASSUME NumWaveAsm == 
   NumWaves \in Nat\{0}

WaveSet == 
   1..NumWaves

RoundSet == 
   0..(2*NumWaves)


LEMMA NonEmptyWaves == WaveSet # {}
      BY NumWaveAsm DEF WaveSet
-----------------------------------------------------------------------------

CONSTANT BlockSet

-----------------------------------------------------------------------------

CONSTANT ChooseLeader(_)

-----------------------------------------------------------------------------

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

VertexSet == UntilRoundVertex(2*NumWaves)

-----------------------------------------------------------------------------

TaggedVertexSet == 
   [sender : ProcessorSet, inRound : RoundSet, vertex : VertexSet]

-----------------------------------------------------------------------------

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

VARIABLE blocksToPropose

BlocksToProposeType == 
   blocksToPropose \in [ProcessorSet -> Seq(BlockSet)]

InitBlocksToPropose ==  
   blocksToPropose = [p \in ProcessorSet |-> <<>> ]

-----------------------------------------------------------------------------

VARIABLE broadcastNetwork

BroadcastNetworkType == 
   broadcastNetwork \in [ProcessorSet \cup 
                         {"History"} ->SUBSET(TaggedVertexSet)]

InitBroadcastNetwork == 
   broadcastNetwork = [p \in ProcessorSet \cup {"History"} |-> {}]

-----------------------------------------------------------------------------

VARIABLE broadcastRecord

BroadcastRecordType == 
   broadcastRecord \in [ProcessorSet -> [RoundSet -> BOOLEAN]]

InitBroadcastRecord == 
   broadcastRecord = [p \in ProcessorSet |-> 
      [ r \in RoundSet |-> IF r = 0 THEN TRUE ELSE FALSE ]]

-----------------------------------------------------------------------------

VARIABLE buffer

BufferType == 
   buffer \in [ProcessorSet -> SUBSET(VertexSet)]

InitBuffer ==
   buffer = [p \in ProcessorSet |-> {}]

-----------------------------------------------------------------------------

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

VARIABLE commitWithRef, 
         decidedWave,
         leaderReachablity,
         leaderSeq,
         faultyLC

-----------------------------------------------------------------------------

LeaderConsensus == 
   INSTANCE FMLeaderConsensusVerification 
   WITH NumWaves <- NumWaves,
        NumProcessors <- NumProcessors,
        f <- f,
        commitWithRef <- commitWithRef,
        decidedWave <- decidedWave,
        leaderReachablity <- leaderReachablity,
        leaderSeq <- leaderSeq,
        faulty <- faultyLC

-----------------------------------------------------------------------------

(*-------------------------STATE-TRANSITIONS-------------------------------*)

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

WaveLeader(p, w) == dag[p][2*w-1][ChooseLeader(w)]

-----------------------------------------------------------------------------

ProcessFailureTn(p) == 
  /\ Cardinality(faulty) < f
  /\ p \notin faulty
  /\ faulty' = faulty \cup {p}
  /\ LeaderConsensus!ProcessFailureTn(p)
  /\ UNCHANGED <<blocksToPropose, broadcastNetwork, broadcastRecord, buffer, dag, 
          round>>

-----------------------------------------------------------------------------

ProposeTn(p, b) == 
   /\ blocksToPropose' = [blocksToPropose EXCEPT 
         ![p] = Append(blocksToPropose[p], b)]
   /\ UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<broadcastNetwork, broadcastRecord, buffer, dag, round, faulty>>

-----------------------------------------------------------------------------

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

TryCommiting(p, Q, w) ==
   IF Cardinality({u \in Q: WaveLeader(p, w) \in u.edges})> f
   THEN LeaderConsensus!UpdateDecidedWaveTn(p, w)
   ELSE UNCHANGED LeaderConsensus!vars

NextRoundTn(p) ==  
   /\ round[p]+1 \in RoundSet
   /\ Cardinality(InAddedVertex(p, round[p])) > 2*f
   /\ blocksToPropose[p] # <<>>
   /\ Broadcast(p, round[p]+1, CreateVertex(p, round[p]+1))
   /\ round' = [round EXCEPT ![p] = round[p]+1]
   /\ blocksToPropose' = [blocksToPropose EXCEPT 
         ![p] = Tail(blocksToPropose[p])]
   /\ UNCHANGED LeaderConsensus!vars
   /\ IF round[p]>0 /\ (round[p] % 2) = 0 
      THEN TryCommiting(p, InAddedVertex(p, round[p]), (round[p] \div 2)) 
      ELSE UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<buffer, dag, faulty>>


-----------------------------------------------------------------------------

ReceiveVertexTn(p, q, r, v) == 
   /\ [sender |-> q, inRound |-> r, vertex |-> v] \in broadcastNetwork[p]
   /\ p \notin faulty => v.source = q
   /\ p \notin faulty => v.round = r
   /\ p \notin faulty => Cardinality(v.edges) > 2*f
   /\ buffer' = [buffer EXCEPT ![p] = buffer[p] \cup {v}]
   /\ broadcastNetwork' = [broadcastNetwork EXCEPT 
         ![p] = broadcastNetwork[p] \ 
             {[sender |-> q, inRound |-> r, vertex |-> v]}]
   /\ UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<blocksToPropose, broadcastRecord, dag, round, faulty>>

-----------------------------------------------------------------------------

ReachableWaveLeaders(p, v) == 
   {w \in WaveSet : StrongPath(v, WaveLeader(p, w))}


AddVertexTn(p, v) == 
   /\ v \in buffer[p]
   /\ p \notin faulty => v.round <= round[p]
   /\ p \notin faulty => dag[p][v.round][v.source] = NilVertex(v.source, v.round)
   /\ p \notin faulty => v.edges \in InAddedVertex(p, v.round -1)
   /\ dag'= [dag EXCEPT ![p][v.round][v.source] = v]
   /\ IF p \notin faulty THEN 
        IF v.round % 2 = 1 /\ v.source = ChooseLeader((v.round \div 2)+1) 
        THEN LeaderConsensus!UpdateWaveTn(p, 
             (v.round \div 2)+1, ReachableWaveLeaders(p, v)) 
        ELSE UNCHANGED LeaderConsensus!vars
      ELSE UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<blocksToPropose, broadcastNetwork, 
                  broadcastRecord, buffer, round, faulty>>

-----------------------------------------------------------------------------

FaultyBcastTn(p ,v, r) ==
   /\ p \in faulty
   /\ Broadcast(p, r, v)
   /\ UNCHANGED LeaderConsensus!vars
   /\ UNCHANGED <<blocksToPropose, buffer, dag, round, faulty>>

-----------------------------------------------------------------------------

(*--------------------------TRANSITION-SYSTEM------------------------------*)

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
   /\ LeaderConsensus!Init

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
          round, faulty, decidedWave, leaderReachablity, leaderSeq, faultyLC, commitWithRef>>

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

(*--------------------------SAFETY-INVARIANTS------------------------------*)

DagConsistency == 
   \A p, q \in ProcessorSet, r \in RoundSet, o \in ProcessorSet: 
     (/\ p \notin faulty
      /\ q \notin faulty
      /\ r # 0 
      /\ dag[p][r][o] \in VertexSet 
      /\ dag[q][r][o] \in VertexSet ) => dag[p][r][o] = dag[q][r][o]

-----------------------------------------------------------------------------

LeaderConsistency == 
   \A p, q \in ProcessorSet: 
      p \notin faultyLC /\ q \notin faultyLC /\ decidedWave[p] <= decidedWave[q] => 
         LeaderConsensus!IsPrefix(leaderSeq[p].current, leaderSeq[q].current)

LeaderMonotonicity == 
   \A p \in ProcessorSet: p \notin faultyLC =>
      LeaderConsensus!IsPrefix(leaderSeq[p].last, leaderSeq[p].current)

-----------------------------------------------------------------------------

Safety == Spec => [](DagConsistency /\ LeaderConsistency /\ LeaderMonotonicity)



=============================================================================
\* Modification History
\* Last modified Sat Jun 15 19:44:19 AEST 2024 by Pranav
\* Created Sat Jun 15 18:37:45 AEST 2024 by Pranav
