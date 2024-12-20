---------------------------- MODULE AlephProofs ----------------------------
EXTENDS AlephSpecification,
        FiniteSets,
        Integers,
        Sequences,
        TLAPS,
        TLC

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

(* Inductive Invariants *)

IndInv1 == 
   \A p, q \in ProcessorSet, r \in RoundSet: 
      r # 0 
      /\ dag[p][r][q] \in VertexSet => dag[p][r][q] \in buffer[p]

IndInv2 == 
   \A m \in broadcastNetwork["History"]: 
      broadcastRecord[m.sender][m.inRound] = TRUE

IndInv3 == 
   \A p \in ProcessorSet: 
       \A m \in broadcastNetwork[p]: 
           m \in broadcastNetwork["History"]

IndInv6 == 
   \A p, q \in ProcessorSet, r \in RoundSet: p \notin faulty =>
      dag[p][r][q].source = q 
      /\ dag[p][r][q].round = r

IndInv4 == 
   \A p \in ProcessorSet: 
      (\A v \in buffer[p] : p \notin faulty =>
         [ sender |-> v.source, inRound |-> v.round, vertex |-> v] \in broadcastNetwork["History"])

IndInv5 == 
   \A m, o \in broadcastNetwork["History"]: 
      m.sender = o.sender /\ m.inRound = o.inRound => m = o

-----------------------------------------------------------------------------

LEMMA VertexSetDefPlt == VertexSet' = VertexSet

LEMMA TailTypePlt == ASSUME NEW S \in Seq(BlockSet), S # <<>>
      PROVE Tail(S) \in Seq(BlockSet)

LEMMA ZeroRoundVertexInVertexSetPlt == \A p \in ProcessorSet : ZeroRoundVertex(p) \in VertexSet

LEMMA NilVertexInNilVertexSetPlt == \A p \in ProcessorSet, r \in RoundSet : NilVertex(p, r) \in NilVertexSet

LEMMA NilVertexNotInVertexSetPlt == \A p \in ProcessorSet, r \in RoundSet : NilVertex(p, r) \notin VertexSet

LEMMA CreateVertexTypePlt == ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet
                  PROVE CreateVertex(p, r) \in VertexSet

LEMMA VertexTypePlt == ASSUME NEW v \in VertexSet
                    PROVE v \in [round : RoundSet, source : ProcessorSet, strongedges : SUBSET(VertexSet), weakedges : SUBSET(VertexSet)]

LEMMA DivProperty1Plt == ASSUME NEW n \in Nat, NEW x \in 0..4*n, x % 4 = 1
                 PROVE (x \div 4)+1 \in 1..n

LEMMA DivProperty2Plt == ASSUME NEW n \in Nat, NEW x \in 0..4*n, x % 4 = 0, x>0
                  PROVE (x \div 4) \in 1..n

LEMMA 0IsRoundPlt == 0 \in RoundSet

-----------------------------------------------------------------------------

LEMMA TypeLem == Spec => []StateType
 <1>1 Init => StateType
      <2>1 0 \in RoundSet
           BY 0IsRoundPlt
      <2>2 ASSUME NEW r \in RoundSet
           PROVE IF r = 0 THEN TRUE ELSE FALSE \in BOOLEAN
           OBVIOUS
      <2>3 ASSUME Init
           PROVE dag \in [ProcessorSet -> [RoundSet  -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]
           <3>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet
                PROVE  dag[p][r][q] \in VertexSet \cup NilVertexSet
                <4>1 dag[p][r][q] =  IF r = 0 THEN ZeroRoundVertex(q) ELSE NilVertex(q, r)
                     BY <3>3, <2>3 DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound
                <4>2 ZeroRoundVertex(q) \in VertexSet
                     BY <3>3, ZeroRoundVertexInVertexSetPlt
                <4>3 NilVertex(q, r) \in NilVertexSet
                     BY <3>3, NilVertexInNilVertexSetPlt
                <4> QED BY <4>1, <4>2, <4>3
           <3> QED BY <2>3, <3>3 DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound
      <2> QED BY <2>1, <2>2, <2>3 DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
 <1>2 ASSUME [Next]_vars, StateType
      PROVE StateType'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW v \in VertexSet, Broadcast(p, r, v)
           PROVE /\ broadcastNetwork' \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
                 /\ broadcastRecord' \in [ProcessorSet -> [RoundSet -> BOOLEAN]]
           <3>1 CASE broadcastRecord[p][r] = FALSE   
                <4>1 [broadcastRecord EXCEPT ![p][r] = TRUE] \in [ProcessorSet -> [RoundSet -> BOOLEAN]]
                     BY <2>1, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                <4>2 [q \in ProcessorSet \cup {"History"} |-> broadcastNetwork[q] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}] \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
                     <5>1 [sender |-> p, inRound |-> r, vertex |-> v] \in TaggedVertexSet
                          BY <2>1 DEF TaggedVertexSet
                     <5> QED BY <2>1, <1>2, <5>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                <4> QED BY <4>1, <4>2, <3>1, <2>1, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
           <3>2 CASE broadcastRecord[p][r] = TRUE
                BY <3>2, <1>2, <2>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
           <3> QED BY <3>1, <3>2, <1>2, <2>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
      <2>2 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p, b)
           PROVE StateType'
           <3>3 blocksToPropose[p] \in Seq(BlockSet)
                BY  <2>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
           <3>1  Append(blocksToPropose[p], b) \in Seq(BlockSet)
                 BY <3>3 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
           <3>2 blocksToPropose' \in [ProcessorSet -> Seq(BlockSet)]
                BY <3>1, <2>2, <1>2 DEF ProposeTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
           <3> QED BY <3>2, <2>2, <1>2, VertexSetDefPlt DEF ProposeTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, TaggedVertexSet
      <2>3 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE StateType'
            <3>1 [round EXCEPT ![p] = round[p]+1] \in [ProcessorSet -> RoundSet]
                 BY <2>3, <1>2 DEF NextRoundTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
            <3>2 [blocksToPropose EXCEPT ![p] = Tail(blocksToPropose[p])] \in [ProcessorSet -> Seq(BlockSet)]
                 <4>1 blocksToPropose[p] \in Seq(BlockSet) /\ blocksToPropose[p] # <<>>
                      BY <2>3, <1>2, <2>3 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, NextRoundTn
                 <4>2 Tail(blocksToPropose[p]) \in Seq(BlockSet)
                      BY <4>1, TailTypePlt
                 <4> QED BY <4>2, <2>3, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
            <3> QED BY <3>1, <3>2, <2>3, <1>2, <2>1, VertexSetDefPlt, CreateVertexTypePlt DEF NextRoundTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, TaggedVertexSet
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, NEW q \in ProcessorSet, p # q, ReceiveVertexTn(p, q, r, v)
           PROVE StateType'
           <3>1 buffer' \in [ProcessorSet -> SUBSET(VertexSet)]
                BY <2>4, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
           <3>2 broadcastNetwork' \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
                BY <2>4, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
           <3> QED BY <3>1, <3>2, <2>4, <1>2, <2>1, VertexSetDefPlt DEF ReceiveVertexTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, TaggedVertexSet
      <2>5 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p, v)
           PROVE StateType'
           <3>1 dag' \in [ProcessorSet -> [RoundSet -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]
                <4>1 v.round \in RoundSet /\ v.source \in ProcessorSet \*/\ v.source \in ProcessorSet
                     BY VertexTypePlt, <2>5
                <4>2 dag' = [dag EXCEPT ![p][v.round][v.source] = v]
                     BY <2>5, <1>2  DEF AddVertexTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                <4> QED BY <4>1, <4>2, <2>5, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
           <3> QED BY <3>1, <2>5, <1>2, VertexSetDefPlt DEF AddVertexTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, TaggedVertexSet
      <2>6 CASE UNCHANGED vars
           BY <2>6, <2>1, <1>2, VertexSetDefPlt DEF vars, TaggedVertexSet, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE StateType'
           BY <2>8, <2>1, <1>2, VertexSetDefPlt DEF FaultyBcastTn, TaggedVertexSet, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>9 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, DecideFameTn(p, g, d)
           PROVE StateType'
           BY <1>2, <2>9 DEF vars1, DecideFameTn, StateType, BAPOrdering!DecideFameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>10 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, VoteTn(p, g, d)
           PROVE StateType'
           BY <1>2, <2>10 DEF vars1, VoteTn, StateType, BAPOrdering!VoteTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>11 ASSUME NEW p \in ProcessorSet, NEW u \in RoundSet, NEW g \in VertexSet, DecideFrameTn(p, u)
           PROVE StateType'
           BY <1>2, <2>11 DEF vars1, DecideFrameTn, StateType, BAPOrdering!DecideFrameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2> QED  BY <2>2, <2>3, <2>4, <2>5, <2>6, <1>2, <2>8, <2>9, <2>10, <2>11 DEF Next
 <1> QED BY <1>1, <1>2, PTL DEF Spec

LEMMA IndInv1Lem == Spec => []IndInv1
 <1>1 Init => IndInv1
      <2>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, NEW r \in RoundSet, r # 0, Init
           PROVE dag[p][r][q] \notin VertexSet
           <3>1 dag[p][r][q] = NilVertex(q, r)
                BY <2>1 DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound
           <3> QED BY <3>1, NilVertexNotInVertexSetPlt
      <2> QED BY <2>1 DEF IndInv1
 <1>2 ASSUME [Next]_vars, StateType, StateType', IndInv1
      PROVE IndInv1'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p, b)
           PROVE IndInv1'
           BY VertexSetDefPlt, <2>1, <1>2 DEF IndInv1, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE IndInv1'
           BY VertexSetDefPlt, <2>2, <1>2 DEF IndInv1, NextRoundTn
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p, q, r, v)
           PROVE IndInv1'
           <3>1 ASSUME NEW t \in ProcessorSet
                PROVE  buffer[t] \in SUBSET(buffer'[t])
                <4>1 CASE t = p
                     BY <4>1, <2>3, <1>2 DEF ReceiveVertexTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                <4>2 CASE t # p
                     BY <4>2, <2>3, <1>2 DEF ReceiveVertexTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                <4> QED BY <4>1, <4>2
           <3> QED BY VertexSetDefPlt, <2>3, <1>2, <3>1 DEF IndInv1, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p, v)
           PROVE IndInv1'
           <3>1 ASSUME NEW q \in ProcessorSet, NEW t \in ProcessorSet, NEW r \in RoundSet, r # 0, dag'[q][r][t] \in VertexSet
                PROVE dag'[q][r][t] \in buffer'[q]
                <4>1 CASE q = p /\ r = v.round /\ t = v.source
                     <5>1 dag'[q][r][t] = v
                          BY <4>1, <3>1, <2>4, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, AddVertexTn
                     <5>2 v \in buffer'[q]
                          BY <4>1, <2>4, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, AddVertexTn
                     <5> QED BY <5>1, <4>1, <5>2
                <4>2 CASE p # q \/ v.source # t \/ v.round # r
                     <5>1 dag'[q][r][t] = dag[q][r][t] /\ buffer'[q] = buffer[q]
                          BY <4>2, <3>1, <2>4, <1>2 DEF AddVertexTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                     <5> QED BY <5>1, <3>1, <1>2 DEF IndInv1
                <4> QED BY <4>1, <4>2
           <3> QED BY <3>1, VertexSetDefPlt, <1>2 DEF IndInv1
      <2>5 CASE UNCHANGED vars
           BY VertexSetDefPlt, <2>5, <1>2 DEF IndInv1, vars
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE IndInv1'
           BY <2>8, <2>1, <1>2, VertexSetDefPlt DEF IndInv1, FaultyBcastTn, TaggedVertexSet, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>9 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, DecideFameTn(p, g, d)
           PROVE IndInv1'
           BY <1>2, <2>9 DEF vars1, DecideFameTn, IndInv1, BAPOrdering!DecideFameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>10 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, VoteTn(p, g, d)
           PROVE IndInv1'
           BY <1>2, <2>10 DEF vars1, VoteTn, IndInv1, BAPOrdering!VoteTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>11 ASSUME NEW p \in ProcessorSet, NEW u \in RoundSet, NEW g \in VertexSet, DecideFrameTn(p, u)
           PROVE IndInv1'
           BY <1>2, <2>11 DEF vars1, DecideFrameTn, IndInv1, BAPOrdering!DecideFrameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2, <2>8, <2>9, <2>10, <2>11 DEF Next
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec

LEMMA IndInv2Lem == Spec => []IndInv2
 <1>1 Init => IndInv2
      BY DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound, IndInv2
 <1>2 ASSUME [Next]_vars, StateType, StateType', IndInv2
      PROVE IndInv2'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p, b)
           PROVE IndInv2'
           BY VertexSetDefPlt, <2>1, <1>2 DEF IndInv2, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE IndInv2'
           <3>1 ASSUME NEW r \in RoundSet, NEW v \in VertexSet, Broadcast(p, r, v)
                PROVE IndInv2'
                <4>1 CASE broadcastRecord[p][r] = FALSE
                     <5>1 broadcastNetwork'["History"] = broadcastNetwork["History"] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}
                          BY <3>1, <2>2, <1>2, <4>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
                     <5>2 broadcastRecord' = [broadcastRecord EXCEPT ![p][r] = TRUE]
                          BY <3>1, <2>2, <1>2, <4>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
                     <5>3 ASSUME NEW m \in broadcastNetwork'["History"]
                          PROVE broadcastRecord'[m.sender][m.inRound] = TRUE
                          <6>1 m.sender \in ProcessorSet /\ m.inRound \in RoundSet
                               <7>1 broadcastNetwork'["History"] \in SUBSET[sender : ProcessorSet, inRound : RoundSet, vertex : VertexSet']
                                    BY <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, TaggedVertexSet
                               <7> QED BY <7>1, <5>3
                          <6>2 CASE m \in broadcastNetwork["History"]
                               <7>1 broadcastRecord[m.sender][m.inRound] = TRUE
                                    BY <6>2, <1>2 DEF IndInv2
                               <7>2 ASSUME NEW a \in ProcessorSet, NEW b \in RoundSet
                                    PROVE broadcastRecord'[a][b] = broadcastRecord[a][b] \/ broadcastRecord'[a][b] = TRUE
                                    <8>1 CASE a = p /\ b = r
                                         BY <8>1, <5>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                                    <8>2 CASE a # p \/ b # r
                                         BY <8>2, <5>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                                    <8> QED BY <8>1, <8>2
                               <7> QED BY <7>1, <7>2, <6>1
                          <6>3 CASE m = [sender |-> p, inRound |-> r, vertex |-> v]
                               BY <6>3, <5>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                          <6> QED BY <6>2, <6>3, <5>1
                     <5> QED BY <1>2, <5>3 DEF IndInv2
                <4>2 CASE broadcastRecord[p][r] = TRUE
                     <5>1 UNCHANGED <<broadcastNetwork, broadcastRecord>>
                          BY <4>2, <2>2, <3>1 DEF Broadcast
                     <5> QED BY <5>1, <1>2 DEF IndInv2
                <4> QED BY <4>1, <4>2, <3>1, <2>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
           <3> QED BY VertexSetDefPlt, <2>2, <1>2, CreateVertexTypePlt, <3>1 DEF IndInv2, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p, q, r, v)
           PROVE IndInv2'
           <3>1 broadcastNetwork'["History"] =  broadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1, <2>3, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
           <3>2 broadcastRecord' = broadcastRecord
                BY <2>3 DEF ReceiveVertexTn
           <3> QED BY <3>1, <3>2, VertexSetDefPlt, <2>3, <1>2 DEF IndInv2, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p, v)
           PROVE IndInv2'
           BY VertexSetDefPlt, <2>4, <1>2 DEF IndInv2, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDefPlt, <2>5, <1>2 DEF IndInv2, vars
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE IndInv2'
           <3>1 ASSUME Broadcast(p, r, v)
                PROVE IndInv2'
                <4>1 CASE broadcastRecord[p][r] = FALSE
                     <5>1 broadcastNetwork'["History"] = broadcastNetwork["History"] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}
                          BY <3>1, <2>8, <2>2, <1>2, <4>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
                     <5>2 broadcastRecord' = [broadcastRecord EXCEPT ![p][r] = TRUE]
                          BY <3>1, <2>8, <2>2, <1>2, <4>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
                     <5>3 ASSUME NEW m \in broadcastNetwork'["History"]
                          PROVE broadcastRecord'[m.sender][m.inRound] = TRUE
                          <6>1 m.sender \in ProcessorSet /\ m.inRound \in RoundSet
                               <7>1 broadcastNetwork'["History"] \in SUBSET[sender : ProcessorSet, inRound : RoundSet, vertex : VertexSet']
                                    BY <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, TaggedVertexSet
                               <7> QED BY <7>1, <5>3
                          <6>2 CASE m \in broadcastNetwork["History"]
                               <7>1 broadcastRecord[m.sender][m.inRound] = TRUE
                                    BY <6>2, <1>2 DEF IndInv2
                               <7>2 ASSUME NEW a \in ProcessorSet, NEW b \in RoundSet
                                    PROVE broadcastRecord'[a][b] = broadcastRecord[a][b] \/ broadcastRecord'[a][b] = TRUE
                                    <8>1 CASE a = p /\ b = r
                                         BY <8>1, <5>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                                    <8>2 CASE a # p \/ b # r
                                         BY <8>2, <5>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                                    <8> QED BY <8>1, <8>2
                               <7> QED BY <7>1, <7>2, <6>1
                          <6>3 CASE m = [sender |-> p, inRound |-> r, vertex |-> v]
                               BY <6>3, <5>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                          <6> QED BY <6>2, <6>3, <5>1
                     <5> QED BY <1>2, <5>3 DEF IndInv2
                <4>2 CASE broadcastRecord[p][r] = TRUE
                     <5>1 UNCHANGED <<broadcastNetwork, broadcastRecord>>
                          BY <4>2, <2>2, <3>1, <2>8 DEF Broadcast
                     <5> QED BY <5>1, <1>2 DEF IndInv2
                <4> QED BY <4>1, <4>2, <3>1, <2>8, <2>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
           <3> QED BY <3>1, <2>8 DEF FaultyBcastTn
      <2>9 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, DecideFameTn(p, g, d)
           PROVE IndInv2'
           BY <1>2, <2>9 DEF vars1, DecideFameTn, IndInv2, BAPOrdering!DecideFameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>10 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, VoteTn(p, g, d)
           PROVE IndInv2'
           BY <1>2, <2>10 DEF vars1, VoteTn, IndInv2, BAPOrdering!VoteTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>11 ASSUME NEW p \in ProcessorSet, NEW u \in RoundSet, NEW g \in VertexSet, DecideFrameTn(p, u)
           PROVE IndInv2'
           BY <1>2, <2>11 DEF vars1, DecideFrameTn, IndInv2, BAPOrdering!DecideFrameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2> QED  BY <2>1,  <2>2, <2>3, <2>4, <2>5, <1>2, <2>8, <2>9, <2>10, <2>11 DEF Next
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec

LEMMA IndInv3Lem == Spec => []IndInv3
 <1>1 Init => IndInv3
      BY DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound, IndInv3
 <1>2 ASSUME [Next]_vars, StateType, StateType', IndInv3
      PROVE IndInv3'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p, b)
           PROVE IndInv3'
           BY VertexSetDefPlt, <2>1, <1>2 DEF IndInv3, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE IndInv3'
           BY VertexSetDefPlt, <2>2, <1>2 DEF IndInv3, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p, q, r, v)
           PROVE IndInv3'
           <3>1 broadcastNetwork'["History"] =  broadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1, <2>3, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
           <3>2 \A z \in ProcessorSet : broadcastNetwork'[z] \in SUBSET(broadcastNetwork[z])
                BY <2>3, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
           <3> QED BY <3>1, <3>2, <2>3, <1>2 DEF IndInv3, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p, v)
           PROVE IndInv3'
           BY VertexSetDefPlt, <2>4, <1>2 DEF IndInv3, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDefPlt, <2>5, <1>2 DEF IndInv3, vars
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE IndInv3'
           BY VertexSetDefPlt, <2>8, <1>2 DEF IndInv3, FaultyBcastTn, Broadcast
      <2>9 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, DecideFameTn(p, g, d)
           PROVE IndInv3'
           BY <1>2, <2>9 DEF vars1, DecideFameTn, IndInv3, BAPOrdering!DecideFameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>10 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, VoteTn(p, g, d)
           PROVE IndInv3'
           BY <1>2, <2>10 DEF vars1, VoteTn, IndInv3, BAPOrdering!VoteTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>11 ASSUME NEW p \in ProcessorSet, NEW u \in RoundSet, NEW g \in VertexSet, DecideFrameTn(p, u)
           PROVE IndInv3'
           BY <1>2, <2>11 DEF vars1, DecideFrameTn, IndInv3, BAPOrdering!DecideFrameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2, <2>8, <2>9, <2>10, <2>11 DEF Next
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec

LEMMA IndInv4Lem == Spec => []IndInv4
 <1>1 Init => IndInv4
      BY DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound, IndInv4
 <1>2 ASSUME [Next]_vars, StateType, StateType', IndInv4, IndInv3
      PROVE IndInv4'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p, b)
           PROVE IndInv4'
           BY VertexSetDefPlt, <2>1, <1>2 DEF IndInv4, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE IndInv4'
           BY VertexSetDefPlt, <2>2, <1>2 DEF IndInv4, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p, q, r, v)
           PROVE IndInv4'
           <3>1 broadcastNetwork'["History"] =  broadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1, <2>3, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
           <3>2 ASSUME NEW t \in ProcessorSet, NEW u \in buffer'[t], t \notin faulty'
                PROVE [ sender |-> u.source, inRound |-> u.round, vertex |-> u] \in broadcastNetwork'["History"]
                <4>1 CASE p = t
                     <5>1 buffer'[p] = buffer[p] \cup {v}
                          BY <4>1, <2>3, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
                     <5>4 t \notin faulty 
                          BY <3>2, <2>3 DEF ReceiveVertexTn
                     <5>2 CASE u = v
                          <6>1 [sender |-> q, inRound |-> r, vertex |-> v] \in broadcastNetwork["History"]
                               BY <2>3, <1>2, <5>4 DEF ReceiveVertexTn, IndInv3
                          <6>2 q = v.source /\ r = v.round
                               BY <4>1, <5>4, <2>3 DEF ReceiveVertexTn
                          <6> QED BY <6>1, <5>2, <3>1, <6>2
                     <5>3 CASE u # v
                          <6>1 u \in buffer[p]
                               BY <5>1, <5>3, <3>2, <4>1
                          <6> QED BY <6>1, <3>1, <3>2, <1>2, <5>4, <4>1 DEF IndInv4
                     <5> QED BY <5>2, <5>3
                <4>2 CASE p # t
                     <5>4 t \notin faulty 
                          BY <3>2, <2>3 DEF ReceiveVertexTn
                     <5>1 buffer'[t] = buffer[t]
                          BY <4>2, <2>3, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
                     <5> QED BY <5>1, <3>1, <3>2, <1>2, <5>4 DEF IndInv4
                <4> QED BY <4>1, <4>2
           <3> QED BY <3>2, <2>3, <1>2 DEF IndInv4, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p, v)
           PROVE IndInv4'
           BY VertexSetDefPlt, <2>4, <1>2 DEF IndInv4, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDefPlt, <2>5, <1>2 DEF IndInv4, vars
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE IndInv4'
           BY VertexSetDefPlt, <2>8, <1>2 DEF IndInv4, FaultyBcastTn, Broadcast
      <2>9 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, DecideFameTn(p, g, d)
           PROVE IndInv4'
           BY <1>2, <2>9 DEF vars1, DecideFameTn, IndInv4, BAPOrdering!DecideFameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>10 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, VoteTn(p, g, d)
           PROVE IndInv4'
           BY <1>2, <2>10 DEF vars1, VoteTn, IndInv4, BAPOrdering!VoteTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>11 ASSUME NEW p \in ProcessorSet, NEW u \in RoundSet, NEW g \in VertexSet, DecideFrameTn(p, u)
           PROVE IndInv4'
           BY <1>2, <2>11 DEF vars1, DecideFrameTn, IndInv4, BAPOrdering!DecideFrameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2, <2>8, <2>9, <2>10, <2>11 DEF Next
 <1> QED BY <1>1, <1>2, TypeLem, IndInv3Lem, PTL DEF Spec

LEMMA IndInv5Lem == Spec => []IndInv5
 <1>1 Init => IndInv5
      BY DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound, IndInv5
 <1>2 ASSUME [Next]_vars, StateType, StateType', IndInv5, IndInv2
      PROVE IndInv5'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p, b)
           PROVE IndInv5'
           BY VertexSetDefPlt, <2>1, <1>2 DEF IndInv5, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE IndInv5'
           <3>1 ASSUME NEW r \in RoundSet, NEW v \in VertexSet, Broadcast(p, r, v)
                PROVE IndInv5'
                <4>1 CASE broadcastRecord[p][r] = FALSE
                     <5>1 broadcastNetwork'["History"] = broadcastNetwork["History"] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}
                          BY <3>1, <2>2, <1>2, <4>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
                     <5>2 broadcastRecord' = [broadcastRecord EXCEPT ![p][r] = TRUE]
                          BY <3>1, <2>2, <1>2, <4>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
                     <5>3 ASSUME NEW m \in broadcastNetwork'["History"], NEW o \in broadcastNetwork'["History"], m.sender = o.sender, m.inRound = o.inRound
                          PROVE m = o
                          <6>1 CASE m \in broadcastNetwork["History"] /\ o = [sender |-> p, inRound |-> r, vertex |-> v]
                               <7>1 broadcastRecord[m.sender][m.inRound] = TRUE
                                    BY <6>1, <1>2 DEF IndInv2
                               <7> QED BY <4>1, <7>1, <6>1, <5>3
                          <6>2 CASE o \in broadcastNetwork["History"] /\ m = [sender |-> p, inRound |-> r, vertex |-> v]
                               <7>1 broadcastRecord[o.sender][o.inRound] = TRUE
                                    BY <6>2, <1>2 DEF IndInv2
                               <7> QED BY <4>1, <7>1, <6>2, <5>3
                          <6>3 CASE m \in broadcastNetwork["History"] /\ o \in broadcastNetwork["History"]
                               BY <6>3, <5>3, <1>2 DEF IndInv5
                          <6> QED BY <6>1, <6>2, <6>3, <5>3, <5>1
                     <5> QED BY <1>2, <5>3 DEF IndInv5
                <4>2 CASE broadcastRecord[p][r] = TRUE
                     <5>1 UNCHANGED <<broadcastNetwork, broadcastRecord>>
                          BY <4>2, <2>2, <3>1 DEF Broadcast
                     <5> QED BY <5>1, <1>2 DEF IndInv5
                <4> QED BY <4>1, <4>2, <3>1, <2>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
           <3> QED BY VertexSetDefPlt, <2>2, <1>2, CreateVertexTypePlt, <3>1 DEF IndInv5, NextRoundTn, Broadcast
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p, q, r, v)
           PROVE IndInv5'
           <3>1 broadcastNetwork'["History"] =  broadcastNetwork["History"]
                <4>1 p # "History"
                     BY <2>3, ProcSetAsm DEF ProcessorSet
                <4> QED BY <4>1, <2>3, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
           <3> QED BY <3>1, VertexSetDefPlt, <2>3, <1>2 DEF IndInv5, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p, v)
           PROVE IndInv5'
           BY VertexSetDefPlt, <2>4, <1>2 DEF IndInv5, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDefPlt, <2>5, <1>2 DEF IndInv5, vars
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE IndInv5'
           <3>1 ASSUME Broadcast(p, r, v)
                PROVE IndInv5'
                <4>1 CASE broadcastRecord[p][r] = FALSE
                     <5>1 broadcastNetwork'["History"] = broadcastNetwork["History"] \cup {[sender |-> p, inRound |-> r, vertex |-> v]}
                          BY <3>1, <2>8, <2>2, <1>2, <4>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
                     <5>2 broadcastRecord' = [broadcastRecord EXCEPT ![p][r] = TRUE]
                          BY <3>1, <2>8, <2>2, <1>2, <4>1 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, Broadcast
                     <5>3 ASSUME NEW m \in broadcastNetwork'["History"], NEW o \in broadcastNetwork'["History"], m.sender = o.sender, m.inRound = o.inRound
                          PROVE m = o
                          <6>1 CASE m \in broadcastNetwork["History"] /\ o = [sender |-> p, inRound |-> r, vertex |-> v]
                               <7>1 broadcastRecord[m.sender][m.inRound] = TRUE
                                    BY <6>1, <1>2 DEF IndInv2
                               <7> QED BY <4>1, <7>1, <6>1, <5>3
                          <6>2 CASE o \in broadcastNetwork["History"] /\ m = [sender |-> p, inRound |-> r, vertex |-> v]
                               <7>1 broadcastRecord[o.sender][o.inRound] = TRUE
                                    BY <6>2, <1>2 DEF IndInv2
                               <7> QED BY <4>1, <7>1, <6>2, <5>3
                          <6>3 CASE m \in broadcastNetwork["History"] /\ o \in broadcastNetwork["History"]
                               BY <6>3, <5>3, <1>2 DEF IndInv5
                          <6> QED BY <6>1, <6>2, <6>3, <5>3, <5>1
                     <5> QED BY <1>2, <5>3 DEF IndInv5
                <4>2 CASE broadcastRecord[p][r] = TRUE
                     <5>1 UNCHANGED <<broadcastNetwork, broadcastRecord>>
                          BY <4>2, <2>2, <3>1, <2>8 DEF Broadcast
                     <5> QED BY <5>1, <1>2 DEF IndInv5
                <4> QED BY <4>1, <4>2, <3>1, <2>8, <2>2, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
           <3> QED BY <3>1, <2>8 DEF FaultyBcastTn
      <2> QED BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>8 DEF Next
 <1> QED BY <1>1, <1>2, TypeLem, IndInv2Lem, PTL DEF Spec

LEMMA IndInv6Lem == Spec => []IndInv6
 <1>1 StateType /\ Init => IndInv6
      <2>1 ASSUME NEW q \in ProcessorSet, NEW t \in ProcessorSet, NEW r \in RoundSet, Init, StateType
           PROVE dag[q][r][t].source = t /\ dag[q][r][t].round = r
           <3>1 CASE r = 0
                <4>1 dag[q][r][t] = [round |-> r, source |-> t, block |-> "Empty", strongedges |-> {}, weakedges |-> {}]
                      BY <3>1, <2>1 DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ZeroRoundVertex
                <4>2 [round |-> r, source |-> t, block |-> "Empty", strongedges |-> {}, weakedges |-> {}].source = t /\ [round |-> r, source |-> t, block |-> "Empty", strongedges |-> {}, weakedges |-> {}].round = r
                     OBVIOUS
                <4> QED BY <4>1, <4>2
           <3>2 CASE r # 0
                <4>1  dag[q][r][t] = [round |-> r, source |-> t, block |-> "Nil", strongedges |-> {}, weakedges |-> {}]
                      BY <3>2, <2>1 DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, NilVertex
                <4>2 [round |-> r, source |-> t, block |-> "Nil", strongedges |-> {}, weakedges |-> {}].source = t /\ [round |-> r, source |-> t, block |-> "Nil", strongedges |-> {}, weakedges |-> {}].round = r
                     OBVIOUS
                <4> QED BY <4>1, <4>2
           <3> QED BY <3>1, <3>2
      <2> QED BY <2>1 DEF IndInv6
 <1>2 ASSUME [Next]_vars, StateType, StateType', IndInv6
      PROVE IndInv6'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW b \in BlockSet, ProposeTn(p, b)
           PROVE IndInv6'
           BY VertexSetDefPlt, <2>1, <1>2 DEF IndInv6, ProposeTn
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE IndInv6'
           BY VertexSetDefPlt, <2>2, <1>2 DEF IndInv6, NextRoundTn
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p, q, r, v)
           PROVE IndInv6'
           BY VertexSetDefPlt, <2>3, <1>2 DEF IndInv6, ReceiveVertexTn
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p, v)
           PROVE IndInv6'
           <3>1 ASSUME NEW q \in ProcessorSet, NEW t \in ProcessorSet, NEW r \in RoundSet, q \notin faulty'
                PROVE dag'[q][r][t].source = t /\ dag'[q][r][t].round = r
                <4>1 CASE q = p /\ r = v.round /\ t = v.source
                     <5>1 dag'[q][r][t] = v
                          BY <4>1, <3>1, <2>4, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, AddVertexTn
                     <5> QED BY <5>1, <4>1
                <4>2 CASE p # q \/ v.source # t \/ v.round # r
                     <5>1 dag'[q][r][t] = dag[q][r][t]
                          BY <4>2, <3>1, <2>4, <1>2 DEF AddVertexTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                     <5>2 faulty = faulty'
                          BY <4>2, <3>1, <2>4 DEF AddVertexTn
                     <5> QED BY <5>1, <3>1, <1>2, <5>2, <2>4 DEF IndInv6
                <4> QED BY <4>1, <4>2
           <3> QED BY <3>1, VertexSetDefPlt, <2>4, <1>2 DEF IndInv6, AddVertexTn
      <2>5 CASE UNCHANGED vars
           BY VertexSetDefPlt, <2>5, <1>2 DEF IndInv6, vars
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE IndInv6'
           BY VertexSetDefPlt, <2>8, <1>2 DEF IndInv6, FaultyBcastTn, Broadcast
      <2>9 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, DecideFameTn(p, g, d)
           PROVE IndInv6'
           BY <1>2, <2>9 DEF vars1, DecideFameTn, IndInv6, BAPOrdering!DecideFameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>10 ASSUME NEW p \in ProcessorSet, NEW d \in VertexSet, NEW g \in VertexSet, VoteTn(p, g, d)
           PROVE IndInv6'
           BY <1>2, <2>10 DEF vars1, VoteTn, IndInv6, BAPOrdering!VoteTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2>11 ASSUME NEW p \in ProcessorSet, NEW u \in RoundSet, NEW g \in VertexSet, DecideFrameTn(p, u)
           PROVE IndInv6'
           BY <1>2, <2>11 DEF vars1, DecideFrameTn, IndInv6, BAPOrdering!DecideFrameTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
      <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2, <2>8, <2>9, <2>10, <2>11 DEF Next
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec

-----------------------------------------------------------------------------

THEOREM DagConsistencyThm == Spec => []DagConsistency
 <1>1 Init => DagConsistency
     BY DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound, DagConsistency
 <1>2 IndInv1' /\ IndInv4' /\ IndInv6' /\ IndInv5' /\ DagConsistency /\ [Next]_vars => DagConsistency'
    <2> SUFFICES ASSUME DagConsistency, [Next]_vars, IndInv1', IndInv4', IndInv6', IndInv5'
                  PROVE DagConsistency'
                  OBVIOUS
    <2>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, NEW  r \in RoundSet, NEW k \in ProcessorSet, r # 0, dag'[p][r][k] \in VertexSet, dag'[q][r][k] \in VertexSet, p \notin faulty', q \notin faulty'
              PROVE dag'[p][r][k] = dag'[q][r][k]
        <3>1 CASE r = 0
             BY <3>1, <2>1
        <3>2 CASE r # 0
             <4>1 \A a, b \in ProcessorSet, z \in RoundSet : a \notin faulty' => dag'[a][z][b].source = b /\ dag'[a][z][b].round = z
                  BY DEF IndInv6
             <4>2 dag'[p][r][k].source = k /\ dag'[p][r][k].round = r /\ dag'[q][r][k].source = k /\ dag'[q][r][k].round = r
                  BY <2>1, <4>1
             <4>3 \A p_1, q_1 \in ProcessorSet, r_1 \in RoundSet : r_1 # 0 /\ dag'[p_1][r_1][q_1] \in VertexSet => dag'[p_1][r_1][q_1] \in buffer'[p_1]
                  BY VertexSetDefPlt DEF IndInv1
             <4>4 dag'[p][r][k] \in buffer'[p] /\  dag'[q][r][k] \in buffer'[q]
                  BY <2>1, <4>3, <3>2
             <4>5 [ sender |-> k, inRound |-> r, vertex |-> dag'[p][r][k]] \in broadcastNetwork'["History"] /\ [ sender |-> k, inRound |-> r, vertex |-> dag'[q][r][k]] \in broadcastNetwork'["History"]
                  BY <2>1, <4>4, <4>2 DEF IndInv4
             <4> QED BY <4>5 DEF IndInv5
        <3> QED BY <3>1, <3>2
    <2>2 DagConsistency' = \A a, b \in ProcessorSet, z \in RoundSet, o \in ProcessorSet: a \notin faulty' /\ b \notin faulty' /\ z # 0 /\ dag'[a][z][o] \in VertexSet /\ dag'[b][z][o] \in VertexSet => dag'[a][z][o] = dag'[b][z][o]
         BY VertexSetDefPlt DEF DagConsistency
    <2>3 QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, PTL, IndInv1Lem, IndInv4Lem, IndInv5Lem, IndInv6Lem DEF Spec

-----------------------------------------------------------------------------

Inv7 == \A q \in ProcessorSet, s \in VertexSet: \A a \in s.strongedges: q \notin faulty /\ s = dag[q][s.round][s.source] => a = dag[q][a.round][a.source]

LEMMA Inv7proof == Spec => []Inv7  
 <1>1 ASSUME Init PROVE Inv7
      <2>1 ASSUME NEW q \in ProcessorSet, NEW s \in VertexSet PROVE  s # dag[q][s.round][s.source]
           <3>1 s.round # 0 /\ s.round \in RoundSet /\ s.source \in ProcessorSet
                BY <2>1, VertexTypePlt DEF RoundSet
           <3>2 dag[q][s.round][s.source] = NilVertex(s.source, s.round)
                BY <3>1, <1>1 DEF Init, InitDag
           <3> QED BY <3>2, NilVertexNotInVertexSetPlt, <3>1 
      <2> QED BY <2>1, <1>1 DEF Inv7
 <1>2 ASSUME [Next]_vars, Inv7 PROVE Inv7'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet,NEW v \in VertexSet, NEW b \in BlockSet, NEW  u \in VertexSet, NEW q \in ProcessorSet\{p}
          PROVE 
        (\/ ProposeTn(p, b)
         \/ NextRoundTn(p)
         \/ ReceiveVertexTn(p, q, r, v)
         \/ AddVertexTn(p, v)
         \/ FaultyBcastTn(p ,v, r)
         \/ DecideFameTn(p, u, v)
         \/ VoteTn(p, u, v)
         \/ DecideFrameTn(p, r)) => Inv7'
         <3>1 ProposeTn(p, b) => Inv7'
              BY <1>2, <2>1 DEF ProposeTn, vars, BAPOrdering!vars, Inv7
         <3>2 NextRoundTn(p) => Inv7'
              BY <1>2, <2>1 DEF NextRoundTn, vars, BAPOrdering!vars, Inv7
         <3>3 ReceiveVertexTn(p, q, r, v) => Inv7'
              BY <1>2, <2>1 DEF ReceiveVertexTn, vars, BAPOrdering!vars, Inv7
         <3>4 ASSUME AddVertexTn(p, v) PROVE Inv7'
              <4>1 ASSUME  NEW p_1 \in ProcessorSet, NEW s_1 \in VertexSet, NEW a_1 \in s_1.strongedges, p_1 \notin faulty, s_1 = dag'[p_1][s_1.round][s_1.source]
                   PROVE a_1 = dag'[p_1][a_1.round][a_1.source]
                   <5>1 CASE p_1 = p /\ v.source = s_1.source /\ v.round = s_1.round
                        BY <5>1, <4>1, <3>4 DEF AddVertexTn
                   <5>2 CASE ~(p_1 = p /\ v.source = s_1.source /\ v.round = s_1.round)
                        <6>1 dag'[p_1][s_1.round][s_1.source] = dag[p_1][s_1.round][s_1.source]
                             BY <5>2, <4>1, <3>4 DEF AddVertexTn
                        <6>2 a_1 = dag[p_1][a_1.round][a_1.source]
                             BY <6>1, <4>1, <1>2 DEF Inv7
                        <6>3 dag[p_1][a_1.round][a_1.source] # NilVertex(a_1.source, a_1.round)
                             BY <6>2, <4>1, NilVertexNotInVertexSetPlt, VertexTypePlt
                        <6>4 p_1 # p \/ v.source # a_1.source \/ v.round # a_1.round
                             BY <4>1, <6>3, <3>4 DEF AddVertexTn
                        <6>5 dag'[p_1][a_1.round][a_1.source] = dag[p_1][a_1.round][a_1.source]
                             BY <6>4, <3>4 DEF AddVertexTn
                        <6> QED BY <6>5, <6>2
                   <5> QED BY <5>1, <5>2
              <4> QED BY <4>1 DEF Inv7
         <3>5 FaultyBcastTn(p ,v, r) => Inv7'
              BY <1>2, <2>1 DEF FaultyBcastTn, vars, BAPOrdering!vars, Inv7
         <3>6 DecideFameTn(p, u, v) => Inv7'
              BY <1>2, <2>1 DEF DecideFameTn, vars1, BAPOrdering!DecideFameTn, Inv7
         <3>7 VoteTn(p, u, v) => Inv7'
              BY <1>2, <2>1 DEF VoteTn, vars1, BAPOrdering!VoteTn, Inv7
         <3>8 DecideFrameTn(p, r) => Inv7'
              BY <1>2, <2>1 DEF DecideFrameTn, vars1, BAPOrdering!DecideFrameTn, Inv7
         <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8
     <2>2 ASSUME UNCHANGED vars
           PROVE Inv7'
           BY <2>2, <1>2 DEF vars, BAPOrdering!vars, Inv7
      <2> QED BY  <2>1, <2>2, <1>2 DEF Next
 <1> QED BY <1>1, <1>2, PTL DEF Spec
      

ASSUME XAs == \A v \in VertexSet: v.frame = v.round /\ v.stronglysees = v.strongedges

LEMMA equalDef ==  ProcessorSet = BAPOrdering!ProcessSet /\ RoundSet = BAPOrdering!Frames
  BY DEF ProcessorSet, NumProcessors, BAPOrdering!ProcessSet, RoundSet,  BAPOrdering!Frames
  
equalVar == \A p \in ProcessorSet, r \in RoundSet, q \in ProcessorSet: p \notin faulty => IF dag[p][r][q] = NilVertex(q, r) THEN VVdag[p][r][q] = {} ELSE VVdag[p][r][q] = {dag[p][r][q]}

LEMMA equalVarProof == Spec => []equalVar
 <1>1 ASSUME Init PROVE equalVar
      <2>1 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet PROVE dag[p][r][q] = NilVertex(q, r) /\ VVdag[p][r][q] = {}
           <3>1 dag[p][r][q] = NilVertex(q, r)
                <4>1 r # 0
                    BY <2>1 DEF RoundSet
                <4> QED BY <4>1, <2>1, <1>1 DEF Init, InitDag
           <3>2 VVdag[p][r][q] = {}
                BY <1>1, <2>1, equalDef DEF Init, BAPOrdering!Init, BAPOrdering!InitWitnessDAG
           <3> QED BY <3>1, <3>2
      <2> QED BY <2>1 DEF equalVar
 <1>2 ASSUME [Next]_vars, equalVar PROVE equalVar'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet,NEW v \in VertexSet, NEW b \in BlockSet, NEW  u \in VertexSet, NEW q \in ProcessorSet\{p}
          PROVE 
        (\/ ProposeTn(p, b)
         \/ NextRoundTn(p)
         \/ ReceiveVertexTn(p, q, r, v)
         \/ AddVertexTn(p, v)
         \/ FaultyBcastTn(p ,v, r)
         \/ DecideFameTn(p, u, v)
         \/ VoteTn(p, u, v)
         \/ DecideFrameTn(p, r)) => equalVar'
         <3>1 ProposeTn(p, b) => equalVar'
              BY <1>2, <2>1 DEF ProposeTn, vars, BAPOrdering!vars, equalVar
         <3>2 NextRoundTn(p) => equalVar'
              BY <1>2, <2>1 DEF NextRoundTn, vars, BAPOrdering!vars, equalVar
         <3>3 ReceiveVertexTn(p, q, r, v) => equalVar'
              BY <1>2, <2>1 DEF ReceiveVertexTn, vars, BAPOrdering!vars, equalVar
         <3>4 ASSUME AddVertexTn(p, v) PROVE equalVar'
              <4>1 ASSUME  NEW p_1 \in ProcessorSet, NEW r_1 \in RoundSet, NEW q_1 \in ProcessorSet, p_1 \notin faulty
                   PROVE IF dag'[p_1][r_1][q_1] = NilVertex(q_1, r_1) THEN VVdag'[p_1][r_1][q_1] = {} ELSE VVdag'[p_1][r_1][q_1] = {dag'[p_1][r_1][q_1]}
                   <5>1  dag'= [dag EXCEPT ![p][v.round][v.source] = v] /\ VVdag' = [VVdag EXCEPT![p][v.round][v.source] = VVdag[p][v.round][v.source] \cup {v}]
                        BY <3>4, XAs DEF AddVertexTn, BAPOrdering!AddWitnessTn
                   <5>2 CASE p_1 = p /\ r_1 = v.round /\ q_1 = v.source
                        <6>1 dag'[p_1][r_1][q_1] = v  /\ VVdag'[p_1][r_1][q_1] = VVdag[p_1][r_1][q_1] \cup {v}
                             BY <3>4, XAs, <4>1, <5>2 DEF AddVertexTn, BAPOrdering!AddWitnessTn
                        <6>2 dag[p_1][r_1][q_1] = NilVertex(q_1, r_1)
                             BY <4>1, <5>2, <3>4 DEF AddVertexTn
                        <6>3 VVdag'[p_1][r_1][q_1] = {v}
                             BY <6>2, <6>1, <4>1, <1>2 DEF equalVar
                        <6> QED BY <6>1, <6>3, <1>2, NilVertexNotInVertexSetPlt
                   <5>3 CASE ~(p_1 = p /\ r_1 = v.round /\ q_1 = v.source)
                        <6>1 dag'[p_1][r_1][q_1] = dag[p_1][r_1][q_1] /\ VVdag'[p_1][r_1][q_1] = VVdag[p_1][r_1][q_1]
                             BY <5>1, <5>3, <4>1
                        <6> QED BY <6>1, <4>1, <1>2 DEF equalVar
                   <5> QED BY <5>2, <5>3
              <4> QED BY <4>1 DEF equalVar
         <3>5 FaultyBcastTn(p ,v, r) => equalVar'
              BY <1>2, <2>1 DEF FaultyBcastTn, vars, BAPOrdering!vars, equalVar
         <3>6 DecideFameTn(p, u, v) => equalVar'
              BY <1>2, <2>1 DEF DecideFameTn, vars1, BAPOrdering!DecideFameTn, equalVar
         <3>7 VoteTn(p, u, v) => equalVar'
              BY <1>2, <2>1 DEF VoteTn, vars1, BAPOrdering!VoteTn, equalVar
         <3>8 DecideFrameTn(p, r) => equalVar'
              BY <1>2, <2>1 DEF DecideFrameTn, vars1, BAPOrdering!DecideFrameTn, equalVar
         <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8
     <2>2 ASSUME UNCHANGED vars
           PROVE equalVar'
           BY <2>2, <1>2 DEF vars, BAPOrdering!vars, equalVar
      <2> QED BY  <2>1, <2>2, <1>2 DEF Next
 <1> QED BY <1>1, <1>2, PTL DEF Spec
 

LEMMA Safety2 == Spec => []UniqueStronglyseen
   <1>1 ASSUME Inv7, DagConsistency, equalVar PROVE UniqueStronglyseen
        <2>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, NEW e \in VertexSet, NEW a \in VertexSet, NEW s \in VertexSet, NEW l \in VertexSet,
             p \notin faulty /\ q \notin faulty, a.round = e.round, a.source = e.source , 
              s \in VVdag[q][s.round][s.source] /\ a \in s.strongedges,
              l \in VVdag[p][l.round][l.source] /\ e \in l.strongedges
             PROVE a = e
             <3>1 s = dag[q][s.round][s.source] /\ l = dag[p][l.round][l.source]
                  <4>1 s.round \in RoundSet /\ s.source \in ProcessorSet /\ l.round \in RoundSet /\ l.source \in ProcessorSet
                    BY <2>1, VertexTypePlt
                  <4>2 dag[q][s.round][s.source] # NilVertex(s.source, s.round)
                       <5>1 VVdag[q][s.round][s.source] # {}
                            BY <2>1
                       <5>2 dag[q][s.round][s.source] = NilVertex(s.source, s.round) => VVdag[q][s.round][s.source] = {}
                            BY <4>1, <2>1, <1>1 DEF equalVar
                       <5> QED BY <5>1, <5>2
                  <4>3 dag[p][l.round][l.source] # NilVertex(l.source, l.round)
                       <5>1 VVdag[p][l.round][l.source] # {}
                            BY <2>1
                       <5>2 dag[p][l.round][l.source] = NilVertex(l.source, l.round) => VVdag[p][l.round][l.source] = {}
                            BY <4>1, <2>1, <1>1 DEF equalVar
                       <5> QED BY <5>1, <5>2
                  <4> QED BY <4>2, <4>3, <4>1, <2>1, <1>1 DEF equalVar
             <3>2 a = dag[q][a.round][a.source] /\ e = dag[p][a.round][a.source]
                  BY <2>1, <1>1, <3>1 DEF Inv7
             <3>3 a.round \in RoundSet /\ a.source \in ProcessorSet /\ 0 \notin RoundSet
                  BY <2>1, VertexTypePlt DEF RoundSet
             <3>4 p \in ProcessorSet /\ q \in ProcessorSet /\ a.round # 0
                 BY <3>3, <2>1
             <3> QED BY <3>1, <2>1, <1>1, <3>2, <3>3 DEF DagConsistency
        <2> QED BY <2>1, <1>1 DEF UniqueStronglyseen, equalVar
   <1> QED BY <1>1, DagConsistencyThm, Inv7proof, PTL, equalVarProof 






  

LEMMA SpecPreservingLemma == Spec => BAPOrdering!Spec
 <1>1 Init => BAPOrdering!Init
    BY DEF Init
 <1>2 ASSUME [Next]_vars, UniqueStronglyseen, UniqueStronglyseen', equalVar, equalVar' \*witnessDAG = BAPWitnessDAG \*, witnessDAG' = BAPWitnessDAG'
      PROVE BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
      <2>1 BAPOrdering!UniqueStronglyseenAs /\ BAPOrdering!UniqueStronglyseenAs'
            <3>1  ProcessorSet = BAPOrdering!ProcessSet
               BY DEF ProcessorSet, NumProcessors, BAPOrdering!ProcessSet
            <3>2 UniqueStronglyseen = \A p \in ProcessorSet, q \in ProcessorSet, e \in VertexSet, a \in VertexSet: 
        (/\ p \notin faulty /\ q \notin faulty
         /\ a.frame = e.frame 
         /\ a.source = e.source 
         /\ \E s \in VertexSet: s \in VVdag[q][s.frame][s.source] /\ a \in s.stronglysees
         /\ \E l \in VertexSet: l \in VVdag[p][l.frame][l.source] /\ e \in l.stronglysees) => a = e
            BY XAs DEF UniqueStronglyseen
            <3>3 UniqueStronglyseen' = \A p \in ProcessorSet, q \in ProcessorSet, e \in VertexSet, a \in VertexSet: 
        (/\ p \notin faulty /\ q \notin faulty
         /\ a.frame = e.frame 
         /\ a.source = e.source 
         /\ \E s \in VertexSet: s \in VVdag'[q][s.frame][s.source] /\ a \in s.stronglysees
         /\ \E l \in VertexSet: l \in VVdag'[p][l.frame][l.source] /\ e \in l.stronglysees) => a = e
               BY XAs DEF UniqueStronglyseen
            <3> QED BY <3>1, <3>2, <1>2, <3>3 DEF BAPOrdering!UniqueStronglyseenAs
      <2>2 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet,NEW v \in VertexSet, NEW b \in BlockSet, NEW  u \in VertexSet, NEW q \in ProcessorSet\{p}
          PROVE 
        (\/ ProposeTn(p, b)
         \/ NextRoundTn(p)
         \/ ReceiveVertexTn(p, q, r, v)
         \/ AddVertexTn(p, v)
         \/ FaultyBcastTn(p ,v, r)
         \/ DecideFameTn(p, u, v)
         \/ VoteTn(p, u, v)
         \/ DecideFrameTn(p, r)) => BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
         <3>1 ASSUME ProposeTn(p, b) PROVE  BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
              BY <3>1 DEF ProposeTn, BAPOrdering!vars
         <3>2 ASSUME NextRoundTn(p) PROVE  BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
              BY <3>2 DEF NextRoundTn, BAPOrdering!vars
         <3>3 ASSUME ReceiveVertexTn(p, q, r, v) PROVE  BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
              BY <3>3 DEF ReceiveVertexTn, BAPOrdering!vars
         <3>4 ASSUME AddVertexTn(p, v) PROVE  BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
              BY <3>4, <2>2, equalDef, <2>1 DEF BAPOrdering!Next, AddVertexTn
         <3>5 ASSUME FaultyBcastTn(p ,v, r) PROVE  BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
              BY <3>5 DEF FaultyBcastTn, BAPOrdering!vars
         <3>6 ASSUME DecideFameTn(p, u, v) PROVE  BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
              BY <3>6, <2>2, equalDef, <2>1 DEF BAPOrdering!Next, DecideFameTn
         <3>7 ASSUME VoteTn(p, u, v) PROVE  BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
              BY <3>7, <2>2, equalDef, <2>1 DEF BAPOrdering!Next, VoteTn
         <3>8 ASSUME DecideFrameTn(p, r) PROVE  BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
              BY <3>8, <2>2, equalDef, <2>1 DEF BAPOrdering!Next, DecideFrameTn
         <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8
      <2>8 ASSUME UNCHANGED vars
           PROVE BAPOrdering!Next \/ UNCHANGED BAPOrdering!vars
           BY <2>8 DEF vars, BAPOrdering!vars
      <2> QED BY  <2>2, <2>8, <1>2 DEF Next
 <1> QED BY <1>1, <1>2, PTL, equalVarProof, Safety2 DEF Spec, BAPOrdering!Spec
-----------------------------------------------------------------------------

LEMMA AlephSafety == Spec => []Safety
   <1>1 Safety = BAPOrdering!Safety
         BY equalDef DEF Safety, BAPOrdering!Safety
   <1>2 Spec => []BAPOrdering!Safety
         BY BAPOrdering!safetyproof, rAsm, fAsm, cAsm, SpecPreservingLemma
   <1> QED BY <1>1, <1>2, BAPOrdering!safetyproof, rAsm, fAsm, cAsm, SpecPreservingLemma, equalDef, PTL DEF Safety, BAPOrdering!Safety
   
=============================================================================
\* Modification History
\* Last modified Thu Dec 19 18:11:10 AEDT 2024 by pgho0778
\* Created Tue Dec 10 18:51:00 AEDT 2024 by pgho0778
