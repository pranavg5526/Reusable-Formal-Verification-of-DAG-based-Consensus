--------------- MODULE ReliableBcastCommunicationProofs ---------------
EXTENDS ReliableBcastCommunicationSpecification,
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
      <2> QED BY <2>1, <2>2, <2>3 DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, FaultyType, InitFaulty
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
           <3> QED BY <3>2, <2>2, <1>2, VertexSetDefPlt DEF ProposeTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, TaggedVertexSet, FaultyType, InitFaulty
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
            <3> QED BY <3>1, <3>2, <2>3, <1>2, <2>1, VertexSetDefPlt, CreateVertexTypePlt DEF NextRoundTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, TaggedVertexSet, FaultyType, InitFaulty
      <2>4 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, NEW q \in ProcessorSet, p # q, ReceiveVertexTn(p, q, r, v)
           PROVE StateType'
           <3>1 buffer' \in [ProcessorSet -> SUBSET(VertexSet)]
                BY <2>4, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
           <3>2 broadcastNetwork' \in [ProcessorSet \cup {"History"} ->SUBSET(TaggedVertexSet)]
                BY <2>4, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, ReceiveVertexTn
           <3> QED BY <3>1, <3>2, <2>4, <1>2, <2>1, VertexSetDefPlt DEF ReceiveVertexTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, TaggedVertexSet, FaultyType, InitFaulty
      <2>5 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, AddVertexTn(p, v)
           PROVE StateType'
           <3>1 dag' \in [ProcessorSet -> [RoundSet -> [ProcessorSet -> VertexSet \cup NilVertexSet]]]
                <4>1 v.round \in RoundSet /\ v.source \in ProcessorSet \*/\ v.source \in ProcessorSet
                     BY VertexTypePlt, <2>5
                <4>2 dag' = [dag EXCEPT ![p][v.round][v.source] = v]
                     BY <2>5, <1>2  DEF AddVertexTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
                <4> QED BY <4>1, <4>2, <2>5, <1>2 DEF StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType
           <3> QED BY <3>1, <2>5, <1>2, VertexSetDefPlt DEF AddVertexTn, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, TaggedVertexSet, FaultyType, InitFaulty
      <2>6 CASE UNCHANGED vars
           BY <2>6, <2>1, <1>2, VertexSetDefPlt DEF vars, TaggedVertexSet, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, FaultyType, InitFaulty
      <2>7 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
           PROVE StateType'
           BY <2>7, <2>1, <1>2, VertexSetDefPlt DEF ProcessFailureTn, TaggedVertexSet, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, FaultyType, InitFaulty
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE StateType'
           BY <2>8, <2>1, <1>2, VertexSetDefPlt DEF FaultyBcastTn, TaggedVertexSet, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, FaultyType
      <2> QED  BY <2>2, <2>3, <2>4, <2>5, <2>6, <1>2, <2>7, <2>8 DEF Next
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
      <2>7 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
           PROVE IndInv1'
           BY <2>7, <2>1, <1>2, VertexSetDefPlt DEF IndInv1, ProcessFailureTn, TaggedVertexSet, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, FaultyType, InitFaulty
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE IndInv1'
           BY <2>8, <2>1, <1>2, VertexSetDefPlt DEF IndInv1, FaultyBcastTn, TaggedVertexSet, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, FaultyType
      <2> QED  BY <2>2, <2>3, <2>4, <2>5, <2>1, <1>2, <2>7, <2>8 DEF Next
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
      <2>7 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
           PROVE IndInv2'
           BY <2>7, <2>1, <1>2, VertexSetDefPlt DEF IndInv2, ProcessFailureTn, TaggedVertexSet, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, FaultyType, InitFaulty
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
      <2> QED BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>7, <2>8 DEF Next
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec

LEMMA IndInv3Lem == Spec => []IndInv3
 <1>1 Init => IndInv3
      BY DEF Init, InitBlocksToPropose, InitBroadcastNetwork, InitBroadcastRecord, InitBuffer, InitDag, InitRound, IndInv3, FaultyType, InitFaulty
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
      <2>7 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
           PROVE IndInv3'
           BY <2>7, <2>1, <1>2, VertexSetDefPlt DEF IndInv3, ProcessFailureTn
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE IndInv3'
           BY VertexSetDefPlt, <2>8, <1>2 DEF IndInv3, FaultyBcastTn, Broadcast
      <2> QED BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>7, <2>8 DEF Next
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
      <2>7 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
           PROVE IndInv4'
           BY <2>7, <2>1, <1>2, VertexSetDefPlt DEF IndInv4, ProcessFailureTn
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE IndInv4'
           BY VertexSetDefPlt, <2>8, <1>2 DEF IndInv4, FaultyBcastTn, Broadcast
      <2> QED BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>7, <2>8 DEF Next
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
      <2>7 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
           PROVE IndInv5'
           BY <2>7, <2>1, <1>2, VertexSetDefPlt DEF IndInv5, ProcessFailureTn, TaggedVertexSet, StateType, BlocksToProposeType, BroadcastNetworkType, BroadcastRecordType, BufferType, DagType, RoundType, FaultyType, InitFaulty
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
      <2> QED BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>7, <2>8 DEF Next
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
           BY VertexSetDefPlt, <2>1, <1>2 DEF IndInv6, ProposeTn, VertexSet
      <2>2 ASSUME NEW p \in ProcessorSet, NextRoundTn(p)
           PROVE IndInv6'
           BY VertexSetDefPlt, <2>2, <1>2 DEF IndInv6, NextRoundTn, VertexSet
      <2>3 ASSUME NEW p \in ProcessorSet, NEW r \in RoundSet, NEW q \in ProcessorSet, NEW v \in VertexSet, p# q, ReceiveVertexTn(p, q, r, v)
           PROVE IndInv6'
           BY VertexSetDefPlt, <2>3, <1>2 DEF IndInv6, ReceiveVertexTn, VertexSet
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
           <3> QED BY <3>1, VertexSetDefPlt, <2>4, <1>2 DEF IndInv6, AddVertexTn, VertexSet
      <2>5 CASE UNCHANGED vars
           BY VertexSetDefPlt, <2>5, <1>2 DEF IndInv6, vars, VertexSet
      <2>7 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
           PROVE IndInv6'
           BY <2>7, <2>1, <1>2, VertexSetDefPlt DEF IndInv6, ProcessFailureTn
      <2>8 ASSUME NEW p \in ProcessorSet, NEW v \in VertexSet, NEW r \in RoundSet, FaultyBcastTn(p, v, r)
           PROVE IndInv6'
           BY VertexSetDefPlt, <2>8, <1>2 DEF IndInv6, FaultyBcastTn, Broadcast
      <2> QED BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>7, <2>8 DEF Next
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
=============================================================================
