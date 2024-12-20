------------------- MODULE GPCOrderingProofs -------------------

EXTENDS FiniteSets, 
        Integers, 
        GPCOrderingSpecification, 
        SequenceOpTheorems,
        Sequences, 
        TLAPS, 
        TLC 

-----------------------------------------------------------------------------

Contains(w, S) == \E i \in 1..Len(S): S[i] = w

IndInv1 == 
   \A p \in ProcessorSet: 
      p \notin faulty /\ decidedWave[p] # 0 => leaderReachablity[p][decidedWave[p]].exists = TRUE

IndInv2 == 
   \A p \in ProcessorSet: p \notin faulty =>
      leaderSeq[p].current = 
         IF decidedWave[p] = 0 
         THEN <<>> 
         ELSE commitWithRef[p][decidedWave[p]]

IndInv3 == 
   \A p \in ProcessorSet, w \in WaveSet: p \notin faulty =>
      \A x \in leaderReachablity[p][w].edges: leaderReachablity[p][x].exists = TRUE

IndInv4 == 
   \A p \in ProcessorSet, w, x \in WaveSet: 
      p \notin faulty /\ Contains(w, commitWithRef[p][x]) => leaderReachablity[p][w].exists = TRUE

IndInv5 == 
   \A p \in ProcessorSet, w, x \in WaveSet: 
      p \notin faulty /\ Contains(w, commitWithRef[p][x]) => IsPrefix(commitWithRef[p][w], commitWithRef[p][x])

IndInv6 == 
   \A p \in ProcessorSet, w \in WaveSet: 
      p \notin faulty /\ leaderReachablity[p][w].exists = TRUE => 
         commitWithRef[p][w] = 
            IF leaderReachablity[p][w].edges = {} 
            THEN <<w>> 
            ELSE Append(commitWithRef[p][max(leaderReachablity[p][w].edges)], w) 

IndInv7 == 
   \A p, q \in ProcessorSet, w \in WaveSet: 
      p \notin faulty /\ q \notin faulty /\ leaderReachablity[p][w].exists = leaderReachablity[q][w].exists => commitWithRef[p][w] = commitWithRef[q][w]

IndInv8 == 
   \A p \in ProcessorSet, w \in WaveSet: 
      p \notin faulty /\ (\A y \in WaveSet : y > w /\ leaderReachablity[p][y].exists => w \in leaderReachablity[p][y].edges) => 
         (\A y \in WaveSet : y >= w /\ leaderReachablity[p][y].exists => Contains(w, commitWithRef[p][y])) 

IndInv9 == 
   \A p, q \in ProcessorSet, w \in WaveSet: 
     (/\ p \notin faulty 
      /\ q \notin faulty
      /\ decidedWave[p] # 0
      /\ w >= decidedWave[p]
      /\ leaderReachablity[q][w].exists = TRUE) => Contains(decidedWave[p], commitWithRef[q][w])

IndInv10 == 
   \A p, q \in ProcessorSet, w \in WaveSet:
     (/\ p \notin faulty 
      /\ q \notin faulty
      /\ leaderReachablity[p][w].exists = TRUE 
      /\ w >= decidedWave[q] 
      /\ decidedWave[q] # 0 ) => 
         IsPrefix(commitWithRef[q][decidedWave[q]], commitWithRef[p][w]) 

-----------------------------------------------------------------------------

LEMMA MaxInPlt == \A E \in SUBSET(WaveSet) : E # {} =>  max(E) \in E 
      
LEMMA MaxPropertyPlt == \A E \in SUBSET(WaveSet) : \A x \in E: E # {} => x<=max(E)

-----------------------------------------------------------------------------

LEMMA SelfIsPrefixLem == \A S \in Seq(WaveSet) : IsPrefix(S, S) = TRUE
      <1>1 \A S \in Seq(WaveSet) : S \o <<>> = S /\ <<>> \in Seq(WaveSet)
           OBVIOUS
      <1> QED BY IsPrefixConcat, <1>1
      
LEMMA TransitiveIsPrefixLem == ASSUME NEW S \in Seq(WaveSet), NEW L \in Seq(WaveSet), NEW M \in Seq(WaveSet), IsPrefix(S, L), IsPrefix(L, M)
                            PROVE IsPrefix(S, M)
      <1>1 \E u, w \in Seq(WaveSet) : L = S \o u /\ M = L \o w
           BY IsPrefixProperties
      <1>2 \A n, m, u \in Seq(WaveSet) : (n \o m) \o u = n \o (m \o u)
           OBVIOUS
      <1>3  \E u, w \in Seq(WaveSet) : M = S \o (u \o w)
           BY <1>1
      <1>4 \A u, w \in Seq(WaveSet) : u \o w \in Seq(WaveSet) 
           OBVIOUS
      <1>5 \A u, w \in Seq(WaveSet) : M = S \o (u \o w) /\ u \o w \in Seq(WaveSet) => IsPrefix(S, M)
           BY IsPrefixConcat
      <1> QED BY <1>5, <1>4, <1>3

LEMMA AppendIsPrefixLem == \A S \in Seq(WaveSet), w \in WaveSet : IsPrefix(S, Append(S, w))
      <1>1 \A S \in Seq(WaveSet), w \in WaveSet : <<w>> \in Seq(WaveSet) /\ Append(S, w) = S \o <<w>>
           OBVIOUS
      <1> QED BY <1>1, IsPrefixConcat
     
-----------------------------------------------------------------------------

LEMMA TypeLem == Spec => []StateType
 <1>1 Init => StateType
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, FaultyType, InitFaulty
 <1>2 ASSUME StateType, Next
      PROVE StateType'
      <2>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
           PROVE StateType'
           <3>1 leaderReachablity' \in [ProcessorSet -> [WaveSet -> [exists : BOOLEAN, edges : SUBSET(WaveSet)]]]
                BY  <2>1, <1>2 DEF ProcessorSet, WaveSet, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
           <3>2 commitWithRef' \in [ProcessorSet -> [WaveSet -> Seq(WaveSet)]]
                <4>1 <<w>> \in Seq(WaveSet)
                     BY <2>1 
                <4>2 E # {} =>max(E) \in WaveSet
                     BY MaxInPlt, <2>1
                <4>3 E # {} => Append(commitWithRef[p][max(E)], w) \in Seq(WaveSet)
                     <5>1 E # {} => commitWithRef[p][max(E)] \in Seq(WaveSet)
                          BY <2>1, <4>2, <1>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5> QED BY <5>1, <2>1 
                <4> QED BY  <4>1, <4>3, <2>1, <1>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
           <3> QED BY <3>1, <3>2, <2>1, <1>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, FaultyType, UpdateWaveTn
      <2>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
           PROVE StateType'
           <3>1 decidedWave' \in [ProcessorSet -> WaveSet \cup {0}]
                BY  <2>2, <1>2 DEF ProcessorSet, WaveSet, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
           <3>2 leaderSeq' \in [ProcessorSet -> [current : Seq(WaveSet), last : Seq(WaveSet)]]
                <4>1 commitWithRef[p][w] \in Seq(WaveSet) /\ leaderSeq[p].current \in Seq(WaveSet)
                     BY <2>2, <1>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                <4> QED BY <4>1, <2>2, <1>2 DEF ProcessorSet, WaveSet, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
           <3> QED BY <3>1, <3>2, <2>2, <1>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, FaultyType, UpdateDecidedWaveTn
      <2>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
           PROVE StateType'
           BY <2>3, <1>2 DEF StateType, ProcessFailureTn, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, FaultyType
      <2> QED BY <2>1, <2>2, <2>3, <1>2 DEF Next
 <1>3 StateType /\ UNCHANGED vars => StateType'
      BY DEF vars, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, FaultyType
 <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec
 
-----------------------------------------------------------------------------

LEMMA IndInv1Lem == Spec => []IndInv1
 <1>1 Init => IndInv1
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, IndInv1
 <1>2 StateType /\ StateType' /\ IndInv1 /\ [Next]_vars => IndInv1'
      <2>1 ASSUME StateType, StateType', Next, IndInv1
           PROVE IndInv1'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE IndInv1'
                <4>1 ASSUME NEW q \in ProcessorSet, decidedWave'[q] # 0, q \notin faulty'
                     PROVE leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                     <5>10 q \notin faulty
                           BY <4>1, <3>1 DEF UpdateWaveTn
                     <5>1 decidedWave'[q] \in WaveSet
                          BY <2>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5>2 CASE decidedWave'[q] = w /\ p = q 
                          BY <5>2, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>3 CASE decidedWave'[q] # w \/ p # q
                          <6>1 decidedWave[q] # 0
                               BY <3>1, <2>1, <4>1, <5>3 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>2 leaderReachablity'[q][decidedWave'[q]].exists = leaderReachablity[q][decidedWave[q]].exists
                               BY <5>3, <3>1, <2>1, <5>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <6>2, <2>1, <5>10 DEF IndInv1
                     <5> QED BY <5>3, <5>2
                <4> QED BY <4>1 DEF IndInv1
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE IndInv1'
                <4>1 ASSUME NEW q \in ProcessorSet, decidedWave'[q] # 0, q \notin faulty'
                     PROVE leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                     <5>1 decidedWave'[q] \in WaveSet
                          BY <2>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5>2 CASE  p = q 
                          BY <4>1, <5>2, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                     <5>3 CASE p # q
                          <6>1 decidedWave[q] # 0
                               BY <3>2, <2>1, <4>1, <5>3 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6>2 leaderReachablity'[q][decidedWave'[q]].exists = leaderReachablity[q][decidedWave[q]].exists
                               BY <5>3, <3>2, <2>1, <5>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6> QED BY <6>1, <6>2, <2>1, <4>1, <3>2 DEF IndInv1, UpdateDecidedWaveTn
                     <5> QED BY <5>3, <5>2
                <4> QED BY <4>1 DEF IndInv1
           <3>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
                PROVE IndInv1'
                BY <3>3, <2>1 DEF IndInv1, ProcessFailureTn
           <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, IndInv1
           PROVE IndInv1'
           BY <2>2 DEF vars, IndInv1
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec


LEMMA IndInv2Lem == Spec => []IndInv2
 <1>1 Init => IndInv2
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, IndInv2
 <1>2 StateType /\ StateType' /\ IndInv1 /\ IndInv1' /\ IndInv2 /\ [Next]_vars => IndInv2'
      <2>1 ASSUME StateType, StateType', Next, IndInv2, IndInv1, IndInv1'
           PROVE IndInv2'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE IndInv2'
                <4>1 ASSUME NEW q \in ProcessorSet, q \notin faulty' 
                     PROVE leaderSeq'[q].current = IF decidedWave'[q] = 0 THEN <<>> ELSE commitWithRef'[q][decidedWave'[q]]
                     <5>1 leaderSeq'[q].current = leaderSeq[q].current
                          BY <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>2 decidedWave'[q] = decidedWave[q]
                          BY <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>3 decidedWave'[q] # 0 => commitWithRef'[q][decidedWave'[q]] = commitWithRef[q][decidedWave[q]]
                          <6>1 CASE q = p
                               <7>1 decidedWave[q] # 0 => leaderReachablity[q][decidedWave[q]].exists = TRUE
                                    BY <4>1, <2>1, <3>1 DEF IndInv1, UpdateWaveTn
                               <7>2 decidedWave[q] # 0 => w # decidedWave[q]
                                    BY <7>1, <3>1, <6>1, <4>1  DEF UpdateWaveTn
                               <7> QED BY <7>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>2 CASE q # p
                               BY <6>2, <5>2, <3>1, <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <6>2
                     <5> QED BY <5>1, <5>2, <5>3, <2>1, <4>1, <3>1 DEF IndInv2, UpdateWaveTn
                <4> QED BY <4>1 DEF IndInv2  
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE IndInv2'
                <4>1 ASSUME NEW q \in ProcessorSet, q \notin faulty'
                     PROVE leaderSeq'[q].current = IF decidedWave'[q] = 0 THEN <<>> ELSE commitWithRef'[q][decidedWave'[q]]
                     <5>1 CASE p = q
                          <6>1 decidedWave'[q] = w
                               BY <5>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6>2 leaderSeq'[q].current = commitWithRef'[q][decidedWave'[q]]
                               BY <5>1, <3>2, <2>1, <6>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6> QED BY <6>1, <6>2, <3>1 DEF WaveSet
                     <5>2 CASE p # q
                          <6>1 leaderSeq'[q].current =leaderSeq[q].current
                               BY <4>1, <5>2, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6>2 decidedWave'[q] = decidedWave[q]
                               BY <4>1, <5>2, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6>3 decidedWave'[q] # 0 => commitWithRef'[q][decidedWave'[q]] = commitWithRef[q][decidedWave[q]]
                               BY <5>2, <6>2, <3>2, <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6> QED BY <6>1, <6>2, <6>3, <2>1, <4>1, <3>2 DEF IndInv2, UpdateDecidedWaveTn
                     <5> QED BY <5>1, <5>2
                <4> QED BY <4>1 DEF IndInv2
           <3>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
                PROVE IndInv2'
                BY <3>3, <2>1 DEF IndInv2, ProcessFailureTn
           <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, IndInv2
           PROVE IndInv2'
           BY <2>2 DEF vars, IndInv2
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, IndInv1Lem, PTL DEF Spec
 
  
LEMMA IndInv3Lem == Spec => []IndInv3
 <1>1 Init => IndInv3
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, IndInv3
 <1>2 StateType /\ StateType' /\ IndInv3 /\ [Next]_vars => IndInv3'
      <2>1 ASSUME StateType, StateType', Next, IndInv3
           PROVE IndInv3'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE IndInv3'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in leaderReachablity'[q][x].edges, q \notin faulty'
                     PROVE leaderReachablity'[q][y].exists = TRUE
                     <5>1 y \in WaveSet
                          BY <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5>2 CASE q = p /\ x = w
                          BY <5>2, <3>1, <2>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>3 CASE q # p \/ x # w
                          <6>1 leaderReachablity'[q][x].edges = leaderReachablity[q][x].edges
                               BY <5>3, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>2 leaderReachablity[q][y].exists = leaderReachablity'[q][y].exists
                               <7>1 w # y \/ q # p
                                    <8>1 leaderReachablity[q][y].exists = TRUE
                                         BY <6>1, <4>1, <2>1, <4>1, <3>1 DEF IndInv3, UpdateWaveTn
                                    <8> QED BY <8>1, <3>1, <4>1 DEF UpdateWaveTn
                               <7> QED BY <7>1, <5>1, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <6>2, <4>1, <2>1, <3>1 DEF IndInv3, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5> QED  BY <5>2, <5>3 
                <4> QED BY <4>1 DEF IndInv3
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE IndInv3'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in leaderReachablity'[q][x].edges, q \notin faulty'
                     PROVE leaderReachablity'[q][y].exists = TRUE 
                     <5>1 leaderReachablity'[q][x].edges = leaderReachablity[q][x].edges 
                          BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                     <5>2 leaderReachablity'[q][y].exists = leaderReachablity[q][y].exists
                          BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                     <5> QED BY <5>1, <5>2, <4>1, <2>1, <4>1, <3>2 DEF IndInv3, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF IndInv3
           <3>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
                PROVE IndInv3'
                BY <3>3, <2>1 DEF IndInv3, ProcessFailureTn
           <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, IndInv3
           PROVE IndInv3'
           BY <2>2 DEF vars, IndInv3
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec      


LEMMA IndInv4Lem == Spec => []IndInv4
 <1>1 Init => IndInv4
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, IndInv4, Contains
 <1>2 StateType /\ StateType' /\ IndInv4 /\ [Next]_vars => IndInv4'
      <2>1 ASSUME StateType, StateType', Next, IndInv4
           PROVE IndInv4'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE IndInv4'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y]), q \notin faulty'
                     PROVE leaderReachablity'[q][x].exists = TRUE
                     <5>1 CASE p = q
                          <6>1 CASE x = w
                               BY <6>1, <5>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>2 CASE x # w
                               <7>1 CASE y # w
                                    BY <7>1, <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv4, UpdateWaveTn
                               <7>2 CASE y = w
                                    <8>1 E # {}
                                         BY <6>2, <4>1, <3>1, <7>2, <5>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn, Contains
                                    <8>2 Contains(x, commitWithRef[q][max(E)])
                                         BY <6>2, <4>1, <3>1, <7>2, <5>1, <2>1, <8>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn, Contains
                                    <8>3 leaderReachablity'[q][x].exists = leaderReachablity[q][x].exists
                                         BY <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8> QED BY <8>2, <8>1, <8>3, MaxInPlt, <4>1, <2>1, <3>1 DEF IndInv4, UpdateWaveTn
                               <7> QED BY <7>1, <7>2
                          <6> QED BY <6>1, <6>2
                     <5>2 CASE p # q
                          BY <5>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv4, UpdateWaveTn
                     <5> QED BY <5>1, <5>2 
                <4> QED BY <4>1 DEF IndInv4
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE IndInv4'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y]), q \notin faulty'
                     PROVE leaderReachablity'[q][x].exists = TRUE
                     BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv4, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF IndInv4
           <3>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
                PROVE IndInv4'
                BY <3>3, <2>1 DEF IndInv4, ProcessFailureTn
           <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, IndInv4
           PROVE IndInv4'
           BY <2>2 DEF vars, IndInv4
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, PTL DEF Spec
 
 
LEMMA IndInv5Lem == Spec => []IndInv5
 <1>1 Init => IndInv5
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, IndInv5, Contains
 <1>2 StateType /\ StateType' /\ IndInv5 /\ [Next]_vars /\ IndInv4 /\ IndInv4' => IndInv5'
      <2>1 ASSUME StateType, StateType', Next, IndInv5, IndInv4, IndInv4'
           PROVE IndInv5'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE IndInv5'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y]), q \notin faulty'
                     PROVE IsPrefix(commitWithRef'[q][x], commitWithRef'[q][y])
                     <5>1 CASE p = q
                          <6>1 CASE x = w
                               <7>1 CASE y = w
                                    BY <7>1, <6>1, <4>1, <2>1, SelfIsPrefixLem DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                               <7>2 CASE y # w
                                    <8>1 leaderReachablity[q][x].exists = TRUE
                                         <9>1 Contains(x, commitWithRef[q][y])
                                              <10>1 commitWithRef'[q][y] = commitWithRef[q][y]
                                                    BY <7>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                              <10> QED BY <4>1, <10>1
                                         <9> QED BY <9>1, <4>1, <2>1, <3>1 DEF IndInv4, UpdateWaveTn
                                    <8>2 leaderReachablity[q][x].exists = FALSE
                                         BY <6>1, <5>1, <3>1, <4>1 DEF UpdateWaveTn
                                    <8> QED BY <8>1, <8>2
                               <7> QED BY <7>1, <7>2
                          <6>2 CASE x # w
                               <7>1 CASE y # w
                                    BY <7>1, <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv5, UpdateWaveTn
                               <7>2 CASE y = w
                                    <8>1 E # {} /\ Contains(x, commitWithRef[q][max(E)])
                                         BY <5>1, <7>2, <6>2, <4>1, <3>1, <2>1 DEF Contains, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>2 max(E) \in WaveSet
                                         BY <8>1, <3>1, MaxInPlt
                                    <8>3 commitWithRef'[q][x] = commitWithRef[q][x]
                                         BY <6>2, <3>1, <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>4 IsPrefix(commitWithRef'[q][x], commitWithRef[q][max(E)])
                                         BY <8>1, <8>2, <8>3, <4>1, <2>1, <3>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv5, UpdateWaveTn
                                    <8>5 IsPrefix(commitWithRef[q][max(E)], commitWithRef'[q][y])
                                         BY <8>1, <5>1, <7>2, <2>1, <3>1, AppendIsPrefixLem DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8> QED BY <8>2, <8>4, <8>5, TransitiveIsPrefixLem, <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                               <7> QED BY <7>1, <7>2
                          <6> QED BY <6>1, <6>2
                     <5>2 CASE p # q
                          BY <5>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv5, UpdateWaveTn
                     <5> QED BY <5>1, <5>2 
                <4> QED BY <4>1 DEF IndInv5
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE IndInv5'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW y \in WaveSet, Contains(x, commitWithRef'[q][y]), q \notin faulty'
                     PROVE IsPrefix(commitWithRef'[q][x], commitWithRef'[q][y])
                     BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv5, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF IndInv5
           <3>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
                PROVE IndInv5'
                BY <3>3, <2>1 DEF IndInv5, ProcessFailureTn
           <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, IndInv5
           PROVE IndInv5'
           BY <2>2 DEF vars, IndInv5
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, IndInv4Lem, PTL DEF Spec


LEMMA IndInv6Lem == Spec => []IndInv6
 <1>1 Init => IndInv6
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, IndInv6
 <1>2 StateType /\ StateType' /\ IndInv6 /\ [Next]_vars /\ IndInv3 /\ IndInv3' => IndInv6'
      <2>1 ASSUME StateType, StateType', Next, IndInv6, IndInv3, IndInv3'
           PROVE IndInv6'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE IndInv6'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = TRUE, q \notin faulty'
                     PROVE commitWithRef'[q][x] = IF leaderReachablity'[q][x].edges = {} THEN <<x>> ELSE Append(commitWithRef'[q][max(leaderReachablity'[q][x].edges)], x)
                     <5>1 CASE q = p /\ x = w
                          <6>1 leaderReachablity'[q][x].edges = E
                               BY <5>1, <3>1, <2>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                          <6>3 E # {} => commitWithRef'[q][max(E)] = commitWithRef[q][max(E)]
                               <7>1 E # {} => w # max(E)
                                    BY MaxInPlt, <3>1, <4>1,<5>1 DEF UpdateWaveTn
                               <7> QED BY <7>1, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <5>1, <4>1, <3>1, <2>1, <6>3 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>2 CASE q # p \/ x # w
                          <6>1 commitWithRef'[q][x] = commitWithRef[q][x] 
                               BY <5>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>2 leaderReachablity'[q][x].edges = leaderReachablity[q][x].edges /\ leaderReachablity'[q][x].exists = leaderReachablity[q][x].exists
                               BY <5>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6>3 leaderReachablity'[q][x].edges # {} => commitWithRef'[q][max(leaderReachablity'[q][x].edges)] = commitWithRef[q][max(leaderReachablity[q][x].edges)]
                               <7>1 leaderReachablity[q][x].edges # {} => max(leaderReachablity[q][x].edges) # w \/ q # p
                                    <8>1 leaderReachablity[q][x].edges # {} => leaderReachablity[q][max(leaderReachablity[q][x].edges)].exists = TRUE
                                         <9>1 leaderReachablity[q][x].edges \in SUBSET(WaveSet)
                                              BY <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                         <9>2 leaderReachablity[q][x].edges # {} => max(leaderReachablity[q][x].edges) \in leaderReachablity[q][x].edges
                                              BY <4>1, <2>1, <9>1, MaxInPlt DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                         <9> QED BY <2>1, <4>1, <3>1, <9>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv3, UpdateWaveTn
                                    <8> QED BY <8>1, <3>1, <4>1, <2>1, MaxInPlt DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                               <7> QED BY <7>1, <4>1, <3>1, <2>1, <6>2 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <6>2, <6>3, <4>1, <2>1, <3>1 DEF IndInv6, UpdateWaveTn
                     <5> QED BY <5>1, <5>2
                <4> QED BY <4>1 DEF IndInv6
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE IndInv6'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = TRUE, q \notin faulty'
                     PROVE commitWithRef'[q][x] = IF leaderReachablity'[q][x].edges = {} THEN <<x>> ELSE Append(commitWithRef'[q][max(leaderReachablity'[q][x].edges)], x)
                     BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv6, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF IndInv6
           <3>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
                PROVE IndInv6'
                BY <3>3, <2>1 DEF IndInv6, ProcessFailureTn
           <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, IndInv6
           PROVE IndInv6'
           BY <2>2 DEF vars, IndInv6
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, IndInv3Lem, PTL DEF Spec
 

LEMMA IndInv7Lem == Spec => []IndInv7
 <1>1 Init => IndInv7
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, IndInv7
 <1>2 StateType /\ StateType' /\ IndInv7 /\ [Next]_vars /\ IndInv6 /\ IndInv3 => IndInv7'
      <2>1 ASSUME StateType, StateType', Next, IndInv7, IndInv6, IndInv3
           PROVE IndInv7'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE IndInv7'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = leaderReachablity'[r][x].exists, q \notin faulty', r \notin faulty'
                     PROVE commitWithRef'[q][x] = commitWithRef'[r][x]
                     <5>1 CASE q = r
                          BY <5>1
                     <5>2 CASE q # r
                          <6>1 CASE x # w
                               BY <6>1, <4>1, <3>1, <2>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv7
                          <6>2 CASE x = w
                               <7>1 CASE q = p
                                    <8>1 leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists /\ commitWithRef[r][x] = commitWithRef'[r][x]
                                         BY <7>1, <5>2, <4>1, <3>1, <2>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                    <8>2 leaderReachablity'[q][x].exists /\ leaderReachablity'[r][x].exists
                                         BY <7>1, <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>3 commitWithRef[r][x] = IF leaderReachablity[r][x].edges = {} THEN <<x>> ELSE Append(commitWithRef[r][max(leaderReachablity[r][x].edges)], x)
                                         BY <8>1, <4>1, <2>1, <8>2, <3>1 DEF IndInv6, UpdateWaveTn
                                    <8>4 E  = leaderReachablity[r][x].edges
                                         BY <6>2, <4>1, <3>1, <8>1, <8>2, <7>1, <5>2 DEF UpdateWaveTn
                                    <8>5 commitWithRef'[q][x] = IF E = {} THEN <<x>> ELSE Append(commitWithRef[q][max(E)], x)
                                         BY <7>1, <6>2, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>7 E # {} => leaderReachablity[r][max(E)].exists /\ leaderReachablity[q][max(E)].exists
                                         BY <8>4, MaxInPlt, <3>1, <4>1, <2>1, <7>1 DEF IndInv3, UpdateWaveTn
                                    <8>6 E # {} => commitWithRef[q][max(E)] = commitWithRef[r][max(E)]
                                         BY <4>1, <3>1, MaxInPlt, <2>1, <8>7, <7>1, <5>2 DEF IndInv7, UpdateWaveTn
                                    <8> QED BY <8>3, <8>4, <8>5, <8>6, <8>1
                               <7>2 CASE r = p
                                    <8>1 leaderReachablity'[q][x].exists = leaderReachablity[q][x].exists /\ commitWithRef[q][x] = commitWithRef'[q][x]
                                         BY <7>2, <5>2, <4>1, <3>1, <2>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                    <8>2 leaderReachablity'[r][x].exists /\ leaderReachablity'[q][x].exists
                                         BY <7>2, <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>3 commitWithRef[q][x] = IF leaderReachablity[q][x].edges = {} THEN <<x>> ELSE Append(commitWithRef[q][max(leaderReachablity[q][x].edges)], x)
                                         BY <8>1, <4>1, <2>1, <8>2, <3>1 DEF IndInv6, UpdateWaveTn
                                    <8>4 E  = leaderReachablity[q][x].edges
                                         BY <6>2, <4>1, <3>1, <8>1, <8>2, <7>2, <5>2 DEF UpdateWaveTn
                                    <8>5 commitWithRef'[r][x] = IF E = {} THEN <<x>> ELSE Append(commitWithRef[r][max(E)], x)
                                         BY <7>2, <6>2, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8>7 E # {} => leaderReachablity[q][max(E)].exists /\ leaderReachablity[r][max(E)].exists
                                         BY <8>4, MaxInPlt, <3>1, <4>1, <2>1, <7>2 DEF IndInv3, UpdateWaveTn
                                    <8>6 E # {} => commitWithRef[r][max(E)] = commitWithRef[q][max(E)]
                                         BY <4>1, <3>1, MaxInPlt, <2>1, <8>7 DEF IndInv7, UpdateWaveTn
                                    <8> QED BY <8>3, <8>4, <8>5, <8>6, <8>1     
                               <7>3 CASE q # p /\ r # p
                                    BY <7>3, <4>1, <3>1, <2>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv7
                               <7> QED BY <7>1, <7>2, <7>3
                          <6> QED BY <6>1, <6>2
                     <5> QED BY <5>1, <5>2
                <4> QED BY <4>1 DEF IndInv7
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE IndInv7'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, leaderReachablity'[q][x].exists = leaderReachablity'[r][x].exists, q \notin faulty', r \notin faulty'
                     PROVE commitWithRef'[q][x] = commitWithRef'[r][x]
                     BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv7, UpdateDecidedWaveTn
                <4> QED BY <4>1 DEF IndInv7
           <3>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
                PROVE IndInv7'
                BY <3>3, <2>1 DEF IndInv7, ProcessFailureTn
           <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, IndInv7
           PROVE IndInv7'
           BY <2>2 DEF vars, IndInv7
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, IndInv3Lem, IndInv6Lem, PTL DEF Spec


LEMMA IndInv8Lem == Spec => []IndInv8
 <1>1 Init => IndInv8
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, IndInv8
 <1>2 StateType /\ StateType' /\ IndInv8 /\ [Next]_vars /\ IndInv6' => IndInv8'
      <2>1 ASSUME StateType, StateType', Next, IndInv8, IndInv6'
           PROVE IndInv8'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE IndInv8'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW x \in WaveSet, NEW z \in WaveSet, z >= x, leaderReachablity'[q][z].exists, \A y \in WaveSet : y > x /\ leaderReachablity'[q][y].exists => x \in leaderReachablity'[q][y].edges, q \notin faulty'
                     PROVE Contains(x, commitWithRef'[q][z]) 
                     <5>1 CASE x = z
                          <6>1 commitWithRef'[q][z] = IF leaderReachablity'[q][z].edges # {} THEN Append(commitWithRef'[q][max(leaderReachablity'[q][z].edges)], z) ELSE <<z>>
                               BY  <2>1, <4>1 DEF IndInv6
                          <6>2 leaderReachablity'[q][z].edges # {} => Contains(z, commitWithRef'[q][z]) 
                               BY <6>1 DEF Contains
                          <6> QED BY <5>1, <6>1, <6>2 DEF Contains
                     <5>2 CASE x # z
                          <6>1 z > x
                               BY <5>2, <4>1
                          <6>2 \A y \in WaveSet : y > x /\ leaderReachablity[q][y].exists => x \in leaderReachablity[q][y].edges
                               <7>1 \A y \in WaveSet : y > x /\ (y # w \/ q # p) /\ leaderReachablity[q][y].exists => x \in leaderReachablity[q][y].edges
                                    BY <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                               <7>2 \A y \in WaveSet : y > x /\ (y = w /\ q = p) => leaderReachablity[q][y].exists = FALSE
                                    BY <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                               <7> QED BY <7>1, <7>2
                          <6>3 CASE p = q /\ w = z
                               <7>1 leaderReachablity'[q][z].edges = E
                                    BY <2>1, <6>3, <3>1 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                               <7>2 x \in E
                                    BY <6>1, <4>1, <7>1
                               <7>3 commitWithRef'[q][z] = Append(commitWithRef'[q][max(E)], z)
                                    BY  <2>1, <4>1, <7>1, <7>2 DEF IndInv6
                               <7>4 max(E) # w /\ max(E) >= x
                                    BY <7>2, MaxInPlt, <3>1, MaxPropertyPlt, <4>1, <6>3 DEF UpdateWaveTn
                               <7>5 leaderReachablity[q][max(E)].exists
                                    BY <6>3, <3>1, <7>2, MaxInPlt, <4>1 DEF UpdateWaveTn
                               <7>6 commitWithRef'[q][max(E)] = commitWithRef[q][max(E)]
                                    BY <7>4, <3>1, <6>3, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                               <7>7 Contains(x, commitWithRef[q][max(E)])
                                    BY <7>6, <7>5, <6>2, <7>4, <7>2, <3>1, <2>1, <4>1, MaxInPlt DEF IndInv8, UpdateWaveTn
                               <7> QED BY <7>7, <7>6, <7>3 DEF Contains
                          <6>4 CASE p # q \/ w # z
                               BY <6>2, <4>1, <6>4, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn, IndInv8
                          <6> QED BY <6>3, <6>4
                     <5> QED BY <5>1, <5>2
                <4> QED BY <4>1 DEF IndInv8
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE IndInv8'
                BY <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, IndInv8, UpdateDecidedWaveTn
           <3>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
                PROVE IndInv8'
                BY <3>3, <2>1 DEF IndInv8, ProcessFailureTn
           <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, IndInv8
           PROVE IndInv8'
           BY <2>2 DEF vars, IndInv8
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, IndInv6Lem, PTL DEF Spec


LEMMA IndInv9Lem == Spec => []IndInv9
 <1>1 Init => IndInv9
      BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, IndInv9
 <1>2 StateType /\ StateType' /\ IndInv9 /\ [Next]_vars /\ IndInv8 /\ IndInv6 /\ IndInv3 => IndInv9'
      <2>1 ASSUME StateType, StateType', Next, IndInv8, IndInv6, IndInv3, IndInv9
           PROVE IndInv9'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE IndInv9'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, decidedWave'[q] # 0, x >= decidedWave'[q], leaderReachablity'[r][x].exists = TRUE, q \notin faulty', r \notin faulty'
                     PROVE Contains(decidedWave'[q], commitWithRef'[r][x])
                     <5>1 decidedWave'[q] = decidedWave[q]
                          BY <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                     <5>2 CASE x # w
                          <6>1 commitWithRef'[r][x] = commitWithRef[r][x] /\ leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists
                               BY <5>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                          <6> QED BY <6>1, <5>1, <4>1, <2>1, <3>1 DEF IndInv9, UpdateWaveTn
                     <5>3 CASE x = w
                          <6>1 CASE r = p
                               <7>1 E # {} => commitWithRef'[r][x] = Append(commitWithRef[r][max(E)], x)
                                    BY <3>1, <2>1, <6>1, <5>3 DEF UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                               <7>2 CASE decidedWave'[q] = x 
                                    <8>1 Contains(x, commitWithRef'[r][x])
                                         BY <7>1, <3>1, <2>1, <5>3, <6>1 DEF Contains, UpdateWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                    <8> QED BY <8>1, <7>2
                               <7>3 CASE decidedWave'[q] # x 
                                    <8>1 decidedWave'[q] \in E /\ E # {}
                                         <9>1 decidedWave'[q] < x
                                              BY <7>3, <4>1
                                         <9> QED BY <9>1, <5>3, <4>1, <3>1, <6>1 DEF UpdateWaveTn
                                    <8>2 Contains(decidedWave'[q], commitWithRef[r][max(E)])
                                         <9>1 max(E) \in E
                                              BY <8>1, <3>1, MaxInPlt
                                         <9>2 decidedWave'[q] =< max(E)
                                              BY <8>1, MaxPropertyPlt, <3>1 DEF max
                                         <9>3 leaderReachablity[r][max(E)].exists = TRUE
                                              BY <8>1, <6>1, <3>1, <9>1, <4>1, <6>1 DEF UpdateWaveTn
                                         <9> QED BY <9>1, <4>1, <9>2, <9>3, <2>1, <5>1, <3>1 DEF IndInv9, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                                    <8> QED BY <8>1, <7>1, <8>2 DEF Contains
                               <7> QED BY <7>2, <7>3
                          <6>2 CASE r # p
                               <7>1 commitWithRef'[r][x] = commitWithRef[r][x] /\ leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists
                                    BY <6>2, <4>1, <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateWaveTn
                               <7> QED BY <7>1, <5>1, <4>1, <2>1, <3>1 DEF IndInv9, UpdateWaveTn
                          <6> QED BY <6>1, <6>2
                     <5> QED BY <5>2, <5>3
                <4> QED BY <4>1 DEF IndInv9
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE IndInv9'
                <4>1 ASSUME NEW q \in ProcessorSet, NEW r \in ProcessorSet, NEW x \in WaveSet, decidedWave'[q] # 0, x >= decidedWave'[q], leaderReachablity'[r][x].exists = TRUE, q \notin faulty', r \notin faulty'
                     PROVE Contains(decidedWave'[q], commitWithRef'[r][x])
                     <5>1 commitWithRef'[r][x] = commitWithRef[r][x] /\ leaderReachablity'[r][x].exists = leaderReachablity[r][x].exists
                          BY <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                     <5>2 CASE q # p
                          <6>1 decidedWave'[q] = decidedWave[q]
                               BY <5>2, <4>1, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6> QED BY <6>1, <5>1, <2>1, <4>1, <3>2 DEF IndInv9, UpdateDecidedWaveTn
                     <5>3 CASE q = p
                          <6>1 decidedWave'[q] = w
                               BY <5>3, <3>2, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                          <6>2 commitWithRef[r][x] = IF leaderReachablity[r][x].edges # {} THEN Append(commitWithRef[r][max(leaderReachablity[r][x].edges)], x) ELSE <<x>>
                               BY <4>1, <2>1, <5>1, <3>2 DEF IndInv6, UpdateDecidedWaveTn
                          <6>3 CASE q = r
                               <7>1 CASE x = w
                                    <8>1 Contains(x, commitWithRef[r][x])
                                         <9>1 CASE leaderReachablity[r][x].edges # {}
                                             BY <9>1, <6>2 DEF Contains
                                         <9>2 CASE leaderReachablity[r][x].edges = {} 
                                             BY <9>2, <6>2 DEF Contains
                                         <9> QED BY <9>1, <9>2
                                    <8> QED BY <8>1, <7>1, <6>1, <5>1
                               <7>2 CASE x # w
                                    <8>1 x > w
                                         BY <7>2, <6>1, <4>1
                                    <8>2 leaderReachablity[r][x].exists = FALSE
                                         BY <8>1, <6>3, <5>3, <3>2, <2>1, <4>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                                    <8> QED BY <8>2, <5>1, <4>1
                              <7> QED BY <7>1, <7>2
                          <6>4 CASE q # r
                              <7>1 CASE x = w
                                   <8>1 Contains(x, commitWithRef[r][x])
                                         <9>1 CASE leaderReachablity[r][x].edges # {}
                                             BY <9>1, <6>2 DEF Contains
                                         <9>2 CASE leaderReachablity[r][x].edges = {} 
                                             BY <9>2, <6>2 DEF Contains
                                         <9> QED BY <9>1, <9>2
                                   <8> QED BY <8>1, <7>1, <6>1, <5>1
                              <7>2 CASE x # w
                                   <8>1 w \in leaderReachablity[r][x].edges /\ leaderReachablity[r][x].edges # {}
                                        <9>1 w < x
                                             BY <7>2, <4>1, <6>1
                                        <9> QED BY <9>1, <5>3, <4>1, <3>2, <6>2, <4>1 DEF UpdateDecidedWaveTn
                                   <8>2 leaderReachablity[r][x].edges \in SUBSET(WaveSet)
                                        BY <4>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                                   <8>3 Contains(w, commitWithRef[r][max(leaderReachablity[r][x].edges)])     
                                        <9>1 max(leaderReachablity[r][x].edges) \in leaderReachablity[r][x].edges
                                             BY <8>1, <4>1, MaxInPlt, <8>2
                                        <9>2 w =< max(leaderReachablity[r][x].edges)
                                             BY <8>1, MaxPropertyPlt, <3>1, <8>2 DEF max
                                        <9>3 leaderReachablity[r][max(leaderReachablity[r][x].edges)].exists = TRUE
                                             BY <4>1, <2>1, <9>1, <3>2 DEF IndInv3, UpdateDecidedWaveTn
                                        <9>4 \A z \in WaveSet : z >= w /\ leaderReachablity[r][z].exists = TRUE => Contains(w, commitWithRef[r][z])
                                             BY <4>1, <3>2, <2>1, <6>4, <5>3 DEF IndInv8, UpdateDecidedWaveTn
                                        <9> QED BY <9>1, <9>2, <9>3, <9>4, <8>2
                                   <8>4 Contains(w, commitWithRef[r][max(leaderReachablity[r][x].edges)])  => Contains(w, Append(commitWithRef[r][max(leaderReachablity[r][x].edges)], x))
                                        BY DEF Contains
                                   <8> QED BY <8>1, <8>4, <6>2, <8>3, <6>1, <5>1 DEF Contains 
                              <7> QED BY <7>1, <7>2
                          <6> QED BY <6>3, <6>4
                     <5> QED BY <5>2, <5>3
                <4> QED BY <4>1 DEF IndInv9
           <3>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
                PROVE IndInv9'
                BY <3>3, <2>1 DEF IndInv9, ProcessFailureTn
           <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, IndInv9
           PROVE IndInv9'
           BY <2>2 DEF vars, IndInv9
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, IndInv8Lem, IndInv6Lem, IndInv3Lem, PTL DEF Spec


LEMMA IndInv10Lem == Spec => []IndInv10
 <1>1 Init => IndInv10
    BY DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, IndInv10
 <1>2 IndInv1 /\ IndInv1' /\ IndInv4 /\ IndInv4' /\ IndInv7 /\ IndInv7' /\ IndInv5 /\ IndInv5'/\ IndInv9 /\ IndInv9' /\ StateType /\ StateType' /\ IndInv10 /\ [Next]_vars => IndInv10'
      <2>1 ASSUME IndInv9, IndInv9', StateType, StateType', IndInv10, [Next]_vars, IndInv1, IndInv1', IndInv4, IndInv4', IndInv7, IndInv7', IndInv5, IndInv5'
           PROVE IndInv10'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, NEW w \in WaveSet, leaderReachablity'[p][w].exists = TRUE, w >= decidedWave'[q], decidedWave'[q] # 0, p \notin faulty', q \notin faulty'
                PROVE IsPrefix(commitWithRef'[q][decidedWave'[q]], commitWithRef'[p][w])
                <4>1 Contains(decidedWave'[q], commitWithRef'[p][w]) 
                     BY <3>1, <2>1 DEF IndInv9
                <4>2 decidedWave'[q] \in WaveSet
                     BY <3>1, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                <4>3 commitWithRef'[p][decidedWave'[q]] = commitWithRef'[q][decidedWave'[q]]
                     <5>1 leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                          BY <3>1, <2>1 DEF IndInv1    
                     <5>2 leaderReachablity'[p][decidedWave'[q]].exists = TRUE
                          BY <3>1, <4>1, <4>2, <2>1 DEF IndInv4
                     <5> QED BY <5>1, <5>2, <4>2, <3>1, <2>1 DEF IndInv7
                <4>4 IsPrefix(commitWithRef'[p][decidedWave'[q]], commitWithRef'[p][w])
                     BY <4>1, <4>2, <3>1, <2>1 DEF IndInv5
                <4> QED BY <4>3, <4>4
           <3> QED BY <3>1 DEF IndInv10
      <2> QED BY <2>1     
 <1> QED BY <1>1, <1>2, PTL, TypeLem, IndInv1Lem, IndInv4Lem, IndInv7Lem, IndInv5Lem, IndInv9Lem DEF Spec             

-----------------------------------------------------------------------------

THEOREM ConsistencyThm == Spec => []Consistency
  <1>1 Init => Consistency
      BY SelfIsPrefixLem DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, Consistency
 <1>2 StateType /\ StateType' /\ IndInv10 /\ IndInv10' /\ IndInv1 /\ IndInv1'/\ IndInv2 /\ IndInv2' /\ [Next]_vars /\ Consistency => Consistency'
      <2>1 ASSUME StateType, StateType', IndInv10, IndInv10', [Next]_vars, Consistency, IndInv1, IndInv1', IndInv2, IndInv2'
           PROVE Consistency'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW q \in ProcessorSet, decidedWave'[p] <= decidedWave'[q], q \notin faulty', p \notin faulty'
                PROVE IsPrefix(leaderSeq'[p].current, leaderSeq'[q].current)
                <4>1 CASE decidedWave'[p] = 0 /\ decidedWave'[q] = 0
                     <5>1 leaderSeq'[p].current = <<>> /\ leaderSeq'[q].current = <<>>
                          BY <4>1, <2>1, <3>1 DEF IndInv2
                     <5> QED BY <5>1, SelfIsPrefixLem
                <4>2 CASE decidedWave'[p] = 0 /\ decidedWave'[q] # 0
                     <5>1 leaderSeq'[p].current = <<>>
                          BY <4>2, <2>1, <3>1 DEF IndInv2
                     <5> QED BY <5>1, <2>1, EmptyIsPrefix DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                <4>3 CASE decidedWave'[p] # 0 /\ decidedWave'[q] # 0
                     <5>1 leaderSeq'[p].current = commitWithRef'[p][decidedWave'[p]] /\ leaderSeq'[q].current = commitWithRef'[q][decidedWave'[q]]
                          BY <4>3, <2>1, <3>1 DEF IndInv2
                     <5>2 decidedWave'[q] \in WaveSet
                          BY <2>1, <4>3 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                     <5>3 leaderReachablity'[q][decidedWave'[q]].exists = TRUE
                          BY <2>1, <3>1, <4>3 DEF IndInv1
                     <5> QED BY <5>1, <5>2, <5>3, <2>1, <3>1, <4>3 DEF IndInv10
                <4> QED BY <3>1, <4>1, <4>2, <4>3, <2>1 DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, WaveSet
           <3> QED BY <3>1 DEF Consistency
      <2> QED BY <2>1
 <1> QED BY  <1>1, <1>2, TypeLem, IndInv10Lem, IndInv1Lem, IndInv2Lem, PTL DEF Spec


THEOREM  MonotonicityThm == Spec => []Monotonicity
 <1>1 Init => Monotonicity
      BY SelfIsPrefixLem DEF Init, InitCommitWithRef, InitDecidedWave, InitLeaderReachability, InitLeaderSeq, Monotonicity
 <1>2 StateType /\ StateType' /\ IndInv10 /\ IndInv10' /\ IndInv1 /\ IndInv1'/\ IndInv2 /\ IndInv2' /\ [Next]_vars /\ Monotonicity => Monotonicity'
      <2>1 ASSUME StateType, StateType', IndInv10, IndInv10', Next, Monotonicity,  IndInv1, IndInv1', IndInv2, IndInv2'
           PROVE Monotonicity'
           <3>1 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, NEW E \in SUBSET(WaveSet), UpdateWaveTn(p, w, E)
                PROVE Monotonicity'
                BY <3>1, <2>1 DEF Monotonicity, UpdateWaveTn
           <3>2 ASSUME NEW p \in ProcessorSet, NEW w \in WaveSet, UpdateDecidedWaveTn(p, w)
                PROVE Monotonicity'
                <4>1 ASSUME NEW q \in ProcessorSet, q \notin faulty'
                     PROVE IsPrefix(leaderSeq'[q].last, leaderSeq'[q].current)
                     <5>1 CASE p = q
                          <6>1 leaderSeq'[q].current = commitWithRef[q][w]
                               BY <5>1, <3>2, <2>1 DEF UpdateDecidedWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                          <6>2 leaderSeq'[q].last = leaderSeq[q].current
                               BY <5>1, <3>2, <2>1 DEF UpdateDecidedWaveTn, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                          <6>3 leaderReachablity[q][w].exists = TRUE
                               BY <5>1, <3>2, <4>1 DEF UpdateDecidedWaveTn
                          <6>4 w >= decidedWave[q]
                               BY <5>1, <3>2, <4>1 DEF UpdateDecidedWaveTn
                          <6>5 CASE decidedWave[q] = 0
                               <7>1 leaderSeq[q].current = <<>>
                                    BY <6>5, <2>1, <3>2, <4>1 DEF IndInv2, UpdateDecidedWaveTn
                               <7> QED BY <2>1, <5>1, <6>2, <7>1, EmptyIsPrefix DEF StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType
                          <6>6 CASE decidedWave[q] # 0
                               <7>1 leaderSeq'[q].last = commitWithRef[q][decidedWave[q]]
                                    BY <6>2, <2>1, <4>1, <6>6, <3>2 DEF IndInv2, UpdateDecidedWaveTn
                               <7> QED BY <7>1, <4>1, <3>2, <6>1, <6>3, <6>4, <6>6, <2>1 DEF IndInv10, UpdateDecidedWaveTn
                          <6> QED BY <6>5, <6>6
                     <5>2 CASE p # q
                          <6>1 leaderSeq'[q] = leaderSeq[q]
                               BY <3>2, <4>1, <5>2 DEF UpdateDecidedWaveTn
                          <6> QED BY <2>1, <6>1, <3>2, <4>1 DEF Monotonicity, StateType, CommitWithRefType, DecidedWaveType, LeaderReachabilityType, LeaderSeqType, UpdateDecidedWaveTn
                     <5> QED BY <5>1, <5>2    
                <4> QED BY <4>1 DEF Monotonicity
           <3>3 ASSUME NEW p \in ProcessorSet, ProcessFailureTn(p)
                PROVE Monotonicity'
                BY <3>3, <2>1 DEF Monotonicity, ProcessFailureTn
           <3> QED BY <3>1, <3>2, <3>3, <2>1 DEF Next
      <2>2 ASSUME UNCHANGED vars, Monotonicity
           PROVE Monotonicity'
           BY <2>2 DEF vars, Monotonicity
      <2> QED BY <2>1, <2>2
 <1> QED BY <1>1, <1>2, TypeLem, IndInv10Lem, IndInv1Lem, IndInv2Lem, PTL DEF Spec

THEOREM SafetyThm == Safety
  BY MonotonicityThm, ConsistencyThm DEF Safety

=============================================================================
\* Modification History
\* Last modified Thu Mar 21 19:35:14 AEDT 2024 by Pranav
\* Created Thu Mar 21 18:23:14 AEDT 2024 by Pranav
