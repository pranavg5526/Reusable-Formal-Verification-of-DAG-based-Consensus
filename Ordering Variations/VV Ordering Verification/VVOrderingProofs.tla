-------------------------- MODULE BinaryAgreementProtocolHashgraphProofs --------------------------

EXTENDS OPODISHashgraphSpecification,
        FiniteSets,
        Integers,
        Sequences,
        TLAPS,
        TLC

LEMMA Pslt1 == \A e \in WitnessSet: /\ e.frame \in Nat 
                                    /\ e.frame \in Frames 
                                    /\ e.source \in ProcessSet 
                                    /\ e.stronglysees \in SUBSET(WitnessSet) 
                                    /\ e \notin e.stronglysees 
                                    /\ (\A a \in e.stronglysees: a.frame = e.frame-1)
                                  
LEMMA Pslt5 == \A e \in WitnessSet: Cardinality({q \in ProcessSet: \E a \in e.stronglysees: a.source = q}) > 2*f

LEMMA Pslt6 == \A e \in WitnessSet: e.coinvote \in BOOLEAN

LEMMA Pslt7 == \A e \in WitnessSet: Cardinality(e.stronglysees) # {}

LEMMA Pslt2 == Cardinality(ProcessSet) = 3*f+1

LEMMA Pslt3 == \A A \in SUBSET(ProcessSet), B \in SUBSET(ProcessSet): Cardinality(A)> 2*f /\ Cardinality(B) > f => A \cap B # {}

LEMMA unequalTF == "undecided" # TRUE /\ "undecided" # FALSE

LEMMA subsetCard == \A A \in SUBSET(ProcessSet), B \in SUBSET(ProcessSet): A \in SUBSET(B) => Cardinality(A) <= Cardinality(B)

LEMMA intCard == \A A \in SUBSET(ProcessSet): Cardinality(A) \in Int

LEMMA CardLm == \A A \in SUBSET(ProcessSet), B \in SUBSET(ProcessSet): A \cap B = {} => Cardinality(A \cup B) = Cardinality(A)+Cardinality(B)

LEMMA intadd == \A a \in Int, b \in Int: a+b > 2*f /\ a> b => a > f          

LEMMA intInv14 == \A a \in Int, m \in Int: a >=m /\ m+a > 2*f => m > f

LEMMA nonemptySet == \A A \in SUBSET(ProcessSet): Cardinality(A) > f \/ Cardinality(A) > 2*f => A # {}  

LEMMA emptyCard == Cardinality({}) = 0

LEMMA UsAsproof == Spec => []UniqueStronglyseenAs
      <1>1 Init => UniqueStronglyseenAs
           BY Pslt1 DEF Init, UniqueStronglyseenAs, InitWitnessDAG, InitVotes, InitFame, InitDecidedFrames, InitFamousWitnesses
      <1>2 Next => UniqueStronglyseenAs /\ UniqueStronglyseenAs'
           BY DEF Next
      <1>3 UniqueStronglyseenAs /\ UNCHANGED vars => UniqueStronglyseenAs'
           BY DEF UniqueStronglyseenAs, vars
      <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec

THEOREM TypeOKcorrectness == Spec => []TypeOK
  <1>1 Init => TypeOK
       BY unequalTF DEF Init, TypeOK, InitWitnessDAG, InitVotes, InitFame, InitDecidedFrames, InitFamousWitnesses, WitnessDAGType, VotesType, FameType, DecidedFramesType, FamousWitnessesType
  <1>2 ASSUME [Next]_vars, TypeOK
       PROVE TypeOK' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE TypeOK'
            BY <2>1, <1>2, Pslt1 DEF AddWitnessTn, TypeOK, WitnessDAGType, VotesType, FameType, DecidedFramesType, FamousWitnessesType
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE TypeOK'
            BY <2>2, <1>2 DEF DecideFameTn, TypeOK, WitnessDAGType, VotesType, FameType, DecidedFramesType, FamousWitnessesType
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e)
            PROVE TypeOK'
            <3>1 VoteIn(p, s, e) \in BOOLEAN
                 <4>1 CASE s.frame = e.frame+1
                      BY <4>1 DEF VoteIn
                 <4>2 CASE ~(s.frame = e.frame+1) /\ (s.frame - e.frame)%c # 0
                      BY <4>2 DEF VoteIn
                 <4>3 CASE ~(s.frame = e.frame+1) /\ ~((s.frame - e.frame)%c # 0)
                      <5>1 CASE (Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]}) > 2*f)
                           BY <5>1, <4>3 DEF VoteIn
                      <5>2 CASE ~(Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]}) > 2*f) /\ (Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= FALSE}) > 2*f)
                           BY <5>2, <4>3 DEF VoteIn
                      <5>3 CASE ~(Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]}) > 2*f) /\ ~(Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= FALSE}) > 2*f)
                           BY <5>3, <4>3, Pslt6, <2>3 DEF VoteIn
                      <5> QED BY <5>1, <5>2, <5>3 
                 <4> QED BY <4>1, <4>2, <4>3
            <3> QED BY <3>1, <2>3, <1>2 DEF VoteTn, TypeOK, WitnessDAGType, VotesType, FameType, DecidedFramesType, FamousWitnessesType
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE TypeOK'
            BY <2>4, <1>2 DEF DecideFrameTn, TypeOK, WitnessDAGType, VotesType, FameType, DecidedFramesType, FamousWitnessesType
       <2>5 ASSUME UNCHANGED vars
            PROVE TypeOK'
            BY <2>5, <1>2 DEF vars, TypeOK, WitnessDAGType, VotesType, FameType, DecidedFramesType, FamousWitnessesType
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL DEF Spec 

Inv1 == \A p \in ProcessSet, s \in WitnessSet, e \in WitnessSet: Votes[p][s][e] # "undecided" /\ s.frame > e.frame+1 => \A a \in s.stronglysees: Votes[p][a][e] # "undecided"

LEMMA Inv1proof == Spec => []Inv1
  <1>1 TypeOK /\ Init => Inv1
       BY unequalTF DEF Init, Inv1, InitVotes, TypeOK, VotesType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv1
       PROVE Inv1' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv1'
            BY <2>1, <1>2 DEF AddWitnessTn, Inv1
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv1'
            BY <2>2, <1>2 DEF DecideFameTn, Inv1
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e)
            PROVE Inv1'
            BY <2>3, <1>2 DEF VoteTn, Inv1
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv1'
            BY <2>4, <1>2 DEF DecideFrameTn, Inv1
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv1'
            BY <2>5, <1>2 DEF vars, Inv1
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness DEF Spec 

Inv2 == \A p \in ProcessSet, e \in WitnessSet: Fame[p][e] = TRUE => \E s \in WitnessSet: s.frame >= e.frame+2 /\ Votes[p][s][e]= TRUE /\ s \in WitnessDAG[p][s.frame][s.source]

LEMMA Inv2proof == Spec => []Inv2
  <1>1 TypeOK /\ Init => Inv2
       BY unequalTF DEF Init, Inv2, InitFame, TypeOK, FameType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv2
       PROVE Inv2' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv2'
            BY <2>1, <1>2 DEF AddWitnessTn, Inv2
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv2'
            <3>1 ASSUME NEW q \in ProcessSet, NEW a \in WitnessSet, Fame'[q][a] = TRUE 
                 PROVE \E z \in WitnessSet: z.frame >= a.frame+2 /\ Votes[q][z][a]= TRUE /\ z \in WitnessDAG[q][z.frame][z.source]
                 <4>1 CASE p = q /\ e = a
                      <5>1 s.frame >= a.frame+2 /\ Votes[q][s][a]= FameIn(p, s, e) /\ s \in WitnessDAG[q][s.frame][s.source]
                           <6>1 s.frame > a.frame+1 => s.frame >= a.frame+2
                                BY <4>1, <2>2, Pslt1
                           <6> QED BY <6>1, <4>1, <2>2 DEF DecideFameTn
                      <5>2 Fame'[q][a] = FameIn(p, s, e)
                           BY <4>1, <2>2, <1>2 DEF DecideFameTn, TypeOK, FameType
                      <5> QED BY <5>1,<5>2, <3>1, <2>2
                 <4>2 CASE p # q \/ a # e
                      <5>1 Fame'[q][a] = Fame[q][a]
                           BY <4>2, <3>1, <2>2, <1>2 DEF TypeOK, FameType, DecideFameTn
                      <5> QED BY <5>1, <3>1, <1>2 DEF Inv2
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1, <2>2 DEF DecideFameTn, Inv2 \*BY <2>2, <1>2 DEF DecideFameTn, Inv2
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e)
            PROVE Inv2'
            <3>1 ASSUME NEW q \in ProcessSet, NEW a \in WitnessSet, Fame[q][a] = TRUE 
                 PROVE \E z \in WitnessSet: z.frame >= a.frame+2 /\ Votes'[q][z][a]= TRUE /\ z \in WitnessDAG[q][z.frame][z.source]
                 <4>1 ASSUME NEW z \in WitnessSet, Votes[q][z][a]= TRUE
                      PROVE Votes'[q][z][a]= TRUE
                      <5>1 CASE p = q /\ z = s /\ a = e
                           BY <5>1, <4>1, <2>3, unequalTF DEF VoteTn
                      <5>2 CASE p # q \/ z # s \/ a # e
                           BY <5>2, <4>1, <3>1, <2>3, <1>2 DEF TypeOK, VotesType, VoteTn
                      <5> QED BY <5>1, <5>2
                 <4> QED BY <4>1,<3>1, <1>2 DEF Inv2
            <3> QED BY <3>1, <2>3 DEF VoteTn, Inv2
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv2'
            BY <2>4, <1>2 DEF DecideFrameTn, Inv2
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv2'
            BY <2>5, <1>2 DEF vars, Inv2
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness DEF Spec 

Inv3 == \A p \in ProcessSet, s \in WitnessSet, e \in WitnessSet: 
    Votes[p][s][e] = TRUE /\ (s.frame-e.frame)%c # 0 /\ s.frame > e.frame+1 => 
           Cardinality({q \in ProcessSet: \E a \in s.stronglysees : a.source = q /\ Votes[p][a][e] = TRUE}) > f

LEMMA Inv3proof == Spec => []Inv3
  <1>1 TypeOK /\ Init => Inv3
       BY unequalTF DEF Init, Inv3, InitVotes, TypeOK, VotesType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv3
       PROVE Inv3' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv3'
            BY <2>1, <1>2 DEF AddWitnessTn, Inv3
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv3'
            BY <2>2, <1>2 DEF DecideFameTn, Inv3
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e), UniqueStronglyseenAs
            PROVE Inv3'
            <3>1 ASSUME NEW j \in ProcessSet, NEW z \in WitnessSet, NEW b \in WitnessSet, Votes'[j][z][b] = TRUE, ((z.frame-b.frame)%c # 0), z.frame > b.frame+1
                 PROVE Cardinality({q \in ProcessSet: \E a \in z.stronglysees : a.source = q /\ Votes'[j][a][b] = TRUE}) > f
                 <4>1 CASE j = p /\ b = e /\ s = z
                      <5>1 VoteIn(p, s, e) = TRUE /\ \A a \in s.stronglysees: Votes[p][a][e] = TRUE \/ Votes[p][a][e] = FALSE
                           BY <2>3, <1>2, <3>1, <4>1 DEF TypeOK, VotesType, VoteTn
                      <5>2 VoteIn(p, s, e) = (Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= TRUE}) >= Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= FALSE}))
                           BY <3>1, <4>1 DEF VoteIn
                      <5>3 (Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= FALSE}) <= Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= TRUE}))
                           BY <5>2, <5>1, intCard
                      <5>4 Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q}) = Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)} \cup {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)})
                           BY <2>3, Pslt1 , <5>1
                      <5>5 {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)} \cap {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)} = {}
                           <6>1 ASSUME {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)} \cap {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)} # {}
                                 PROVE FALSE
                                 <7>1 \E i \in ProcessSet: i \in {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)} /\ i \in {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)}
                                      BY <6>1
                                 <7>2 \E i \in ProcessSet, a \in s.stronglysees, u \in s.stronglysees : a.source = u.source /\ Votes[p][a][e] = TRUE  /\ Votes[p][u][e] = FALSE /\ a.frame = u.frame /\ s \in WitnessDAG[p][s.frame][s.source]
                                      BY <7>1, Pslt1, <2>3 DEF VoteTn
                                 <7>4 \E i \in ProcessSet, a \in s.stronglysees, u \in s.stronglysees : a = u /\ Votes[p][a][e] = TRUE  /\ Votes[p][u][e] = FALSE
                                      BY <7>2, <2>3, Pslt1 DEF UniqueStronglyseenAs
                                 <7> QED BY <7>4
                           <6> QED BY <6>1
                      <5>6 Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q}) = Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)}) + Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)})
                           BY <5>4, <5>5, CardLm
                      <5>7 Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)}) + Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)}) > 2*f
                           BY <2>3, Pslt5, natfAs, intCard, <5>6
                      <5>8 Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= TRUE}) > f
                           BY intInv14, <5>7, <5>3, intCard, intadd
                      <5>9 ASSUME NEW a \in s.stronglysees
                           PROVE Votes[p][a][e] = Votes'[p][a][e]
                           BY Pslt1, <2>3, <1>2 DEF TypeOK, VotesType, VoteTn
                      <5> QED BY <5>8, <4>1, <5>9
                 <4>2 CASE j # p \/ b # e \/ s # z
                      <5>1 Votes'[j][z][b] = Votes[j][z][b] 
                           BY <4>2, <2>3, <3>1, <1>2 DEF TypeOK, VotesType, VoteTn
                      <5>2 ASSUME NEW a \in z.stronglysees, Votes[j][a][b] = TRUE
                           PROVE Votes'[j][a][b] = TRUE
                           <6>1 CASE j = p /\ a = s /\ b = e
                                BY <5>2, <6>1, unequalTF, <2>3 DEF VoteTn
                           <6>2 CASE j # p \/ a # s \/ b # e
                                <7>1 a \in WitnessSet /\ b \in WitnessSet /\ j \in ProcessSet
                                     BY <5>2, Pslt1, <3>1
                                <7>2 Votes[j][a][b] = Votes'[j][a][b]
                                     BY <6>2, <2>3, <7>1, <1>2 DEF TypeOK, VotesType, VoteTn
                                <7> QED BY <7>2, <5>2 
                           <6> QED BY <6>1, <6>2
                      <5>3 Cardinality({q \in ProcessSet: \E a \in z.stronglysees : a.source = q /\ Votes'[j][a][b] = TRUE}) >= Cardinality({q \in ProcessSet: \E a \in z.stronglysees : a.source = q /\ Votes[j][a][b] = TRUE})
                           BY <5>2, subsetCard
                      <5> QED BY <5>1, <5>3, <3>1, <1>2, natfAs, intCard DEF Inv3 
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1 DEF Inv3 
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv3'
            BY <2>4, <1>2 DEF DecideFrameTn, Inv3
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv3'
            BY <2>5, <1>2 DEF vars, Inv3
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness DEF Spec 

Inv4 == \A p \in ProcessSet, s \in WitnessSet, e \in WitnessSet: 
    Votes[p][s][e] = FALSE /\ (s.frame-e.frame)%c # 0 /\ s.frame > e.frame+1 => 
           Cardinality({q \in ProcessSet: \E a \in s.stronglysees : a.source = q /\ Votes[p][a][e] = FALSE}) > f

LEMMA Inv4proof == Spec => []Inv4
  <1>1 TypeOK /\ Init => Inv4
       BY unequalTF DEF Init, Inv4, InitVotes, TypeOK, VotesType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv4 
       PROVE Inv4' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv4'
            BY <2>1, <1>2 DEF AddWitnessTn, Inv4
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv4'
            BY <2>2, <1>2 DEF DecideFameTn, Inv4
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e), UniqueStronglyseenAs
            PROVE Inv4'
            <3>1 ASSUME NEW j \in ProcessSet, NEW z \in WitnessSet, NEW b \in WitnessSet, Votes'[j][z][b] = FALSE, ((z.frame-b.frame)%c # 0), z.frame > b.frame+1
                 PROVE Cardinality({q \in ProcessSet: \E a \in z.stronglysees : a.source = q /\ Votes'[j][a][b] = FALSE}) > f
                 <4>1 CASE j = p /\ b = e /\ s = z
                      <5>1 VoteIn(p, s, e) = FALSE /\ \A a \in s.stronglysees: Votes[p][a][e] = TRUE \/ Votes[p][a][e] = FALSE
                           BY <2>3, <1>2, <3>1, <4>1 DEF TypeOK, VotesType, VoteTn
                      <5>2 VoteIn(p, s, e) = (Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= TRUE}) >= Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= FALSE}))
                           BY <3>1, <4>1 DEF VoteIn
                      <5>3 (Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= TRUE}) < Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= FALSE}))
                           <6>1 \A t \in Int, y \in Int: (t >= y) = FALSE => t < y
                                OBVIOUS
                           <6> QED BY <5>2, <5>1, intCard, <6>1 
                      <5>4 Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q}) = Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)} \cup {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)})
                           BY <2>3, Pslt1 , <5>1
                      <5>5 {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)} \cap {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)} = {}
                           <6>1 ASSUME {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)} \cap {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)} # {}
                                 PROVE FALSE
                                 <7>1 \E i \in ProcessSet: i \in {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)} /\ i \in {q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)}
                                      BY <6>1
                                 <7>2 \E i \in ProcessSet, a \in s.stronglysees, u \in s.stronglysees : a.source = u.source /\ Votes[p][a][e] = TRUE  /\ Votes[p][u][e] = FALSE /\ a.frame = u.frame /\ s \in WitnessDAG[p][s.frame][s.source]
                                      BY <7>1, Pslt1, <2>3 DEF VoteTn
                                 <7>4 \E i \in ProcessSet, a \in s.stronglysees, u \in s.stronglysees : a = u /\ Votes[p][a][e] = TRUE  /\ Votes[p][u][e] = FALSE
                                      BY <7>2, <2>3, Pslt1 DEF UniqueStronglyseenAs
                                 <7> QED BY <7>4
                           <6> QED BY <6>1
                      <5>6 Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q}) = Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)}) + Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)})
                           BY <5>4, <5>5, CardLm
                      <5>7 Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = TRUE)}) + Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ (Votes[p][a][e] = FALSE)}) > 2*f
                           BY <2>3, Pslt5, natfAs, intCard, <5>6
                      <5>8 Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= FALSE}) > f
                           BY <5>7, <5>3, intCard, intadd
                      <5>9 ASSUME NEW a \in s.stronglysees
                           PROVE Votes[p][a][e] = Votes'[p][a][e]
                           BY Pslt1, <2>3, <1>2 DEF TypeOK, VotesType, VoteTn
                      <5> QED BY <5>8, <4>1, <5>9
                 <4>2 CASE j # p \/ b # e \/ s # z
                      <5>1 Votes'[j][z][b] = Votes[j][z][b] 
                           BY <4>2, <2>3, <3>1, <1>2 DEF TypeOK, VotesType, VoteTn
                      <5>2 ASSUME NEW a \in z.stronglysees, Votes[j][a][b] = FALSE
                           PROVE Votes'[j][a][b] = FALSE
                           <6>1 CASE j = p /\ a = s /\ b = e
                                BY <5>2, <6>1, unequalTF, <2>3 DEF VoteTn
                           <6>2 CASE j # p \/ a # s \/ b # e
                                <7>1 a \in WitnessSet /\ b \in WitnessSet /\ j \in ProcessSet
                                     BY <5>2, Pslt1, <3>1
                                <7>2 Votes[j][a][b] = Votes'[j][a][b]
                                     BY <6>2, <2>3, <7>1, <1>2 DEF TypeOK, VotesType, VoteTn
                                <7> QED BY <7>2, <5>2 
                           <6> QED BY <6>1, <6>2
                      <5>3 Cardinality({q \in ProcessSet: \E a \in z.stronglysees : a.source = q /\ Votes'[j][a][b] = FALSE}) >= Cardinality({q \in ProcessSet: \E a \in z.stronglysees : a.source = q /\ Votes[j][a][b] = FALSE})
                           BY <5>2, subsetCard
                      <5> QED BY <5>1, <5>3, <3>1, <1>2, natfAs, intCard DEF Inv4 
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1 DEF Inv4 
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv4'
            BY <2>4, <1>2 DEF DecideFrameTn, Inv4
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv4'
            BY <2>5, <1>2 DEF vars, Inv4
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness DEF Spec 

Inv5 == \A p \in ProcessSet, s \in WitnessSet, e \in WitnessSet, x \in Frames: 
                (/\ s \in WitnessDAG[p][s.frame][s.source]
                 /\ Votes[p][s][e] # "undecided"
                 /\ e.frame < x /\ x < s.frame)
                  => (\E a \in WitnessSet: a \in WitnessDAG[p][a.frame][a.source] /\ a.frame = x /\ Votes[p][a][e] = Votes[p][s][e])

LEMMA Inv5proof == Spec => []Inv5
  <1>1 Init => Inv5
       BY DEF Init, Inv5, InitWitnessDAG, InitVotes, InitFame, InitDecidedFrames, InitFamousWitnesses
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv5, Inv3, Inv4, Inv4', Inv3'
       PROVE Inv5' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv5'
            BY <1>2, <2>1 DEF Inv5, AddWitnessTn
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv5'
            BY <1>2, <2>2 DEF Inv5, DecideFameTn
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e), UniqueStronglyseenAs
            PROVE Inv5'
            <3>1 ASSUME NEW q \in ProcessSet, NEW g \in WitnessSet, NEW h \in WitnessSet, NEW x \in Frames,  h \in WitnessDAG'[q][h.frame][h.source], Votes'[q][h][g] # "undecided", g.frame < x, x < h.frame
                 PROVE \E a \in WitnessSet: a \in WitnessDAG'[q][a.frame][a.source] /\ a.frame = x /\ Votes'[q][a][g] = Votes'[q][h][g]
                 <4>1 CASE p = q /\ g = e /\ h = s
                      <5>1 CASE h.frame-1 > g.frame
                           <6>3 \E a \in s.stronglysees : a \in WitnessDAG'[p][a.frame][a.source] /\ a.frame = s.frame-1 /\ Votes'[p][a][e] = Votes'[p][s][e]
                                <7>1 \A a \in s.stronglysees: WitnessDAG'[p][a.frame][a.source] = WitnessDAG[p][a.frame][a.source] /\ a.frame = s.frame-1
                                     BY Pslt1, <2>3 DEF VoteTn
                                <7>2 Votes'[p][s][e] = VoteIn(p, s, e)
                                     BY <2>3, <1>2 DEF TypeOK, VotesType, VoteTn
                                <7>3 \A a \in s.stronglysees: Votes'[p][a][e] = Votes[p][a][e]
                                     BY Pslt1, <2>3, <1>2 DEF TypeOK, VotesType, VoteTn
                                <7>4  \A a \in s.stronglysees: a \in WitnessDAG[p][a.frame][a.source] /\ a.frame = s.frame-1
                                     BY <7>1, <2>3 DEF VoteTn
                                <7>5  VoteIn(p, s, e) \in BOOLEAN
                                           <8>1 CASE s.frame = e.frame+1
                                                  BY <8>1 DEF VoteIn
                                           <8>2 CASE ~(s.frame = e.frame+1) /\ (s.frame - e.frame)%c # 0
                                                    BY <8>2 DEF VoteIn
                                           <8>3 CASE ~(s.frame = e.frame+1) /\ ~((s.frame - e.frame)%c # 0)
                                                <9>1 CASE (Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]}) > 2*f)
                                                          BY <9>1, <8>3 DEF VoteIn
                                                <9>2 CASE ~(Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]}) > 2*f) /\ (Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]= FALSE}) > 2*f)
                                                          BY <9>2, <8>3 DEF VoteIn
                                                <9>3 CASE ~(Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]}) > 2*f) /\ ~(Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]= FALSE}) > 2*f)
                                                          BY <9>3, <8>3, Pslt6, <2>3 DEF VoteIn
                                                <9> QED BY <9>1, <9>2, <9>3 
                                           <8> QED BY <8>1, <8>2, <8>3
                                <7>6 \E a \in s.stronglysees: Votes[p][a][e] = VoteIn(p, s, e)
                                     <8>1 CASE VoteIn(p, s, e) = TRUE
                                          <9>1 CASE s.frame = e.frame+1
                                               BY <5>1, <4>1, Pslt1, <2>3, <9>1
                                          <9>2 CASE ~(s.frame = e.frame+1) /\ ((s.frame - e.frame)%c # 0) 
                                               <10>1 s.frame > e.frame+1 /\ Votes'[p][s][e] = TRUE /\ (s.frame - e.frame)%c # 0
                                                    BY <5>1, <4>1, <2>3, Pslt1, <8>1, <7>2,<9>2
                                               <10>2 Cardinality({j \in ProcessSet: \E a \in s.stronglysees : a.source = j /\ Votes'[p][a][e] = TRUE}) > f
                                                    BY <10>1, <2>3, <1>2 DEF Inv3
                                               <10>3 {j \in ProcessSet: \E a \in s.stronglysees : a.source = j /\ Votes'[p][a][e] = TRUE} # {}
                                                     BY nonemptySet, <10>2
                                               <10>4 \E j \in ProcessSet: \E a \in s.stronglysees :  Votes'[p][a][e] = TRUE
                                                     BY <10>3
                                               <10> QED BY <10>4, <8>1, <7>3
                                          <9>3 CASE ~(s.frame = e.frame+1) /\ ~((s.frame - e.frame)%c # 0)
                                               <10>1 CASE Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]}) > 2*f
                                                     BY <10>1, <8>1, nonemptySet
                                               <10>2 CASE ~(Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]}) > 2*f)  /\ (Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]= FALSE}) > 2*f)
                                                     BY <9>3, <10>2, <8>1 DEF VoteIn
                                               <10>3 CASE ~(Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]}) > 2*f) /\ ~(Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]= FALSE}) > 2*f)
                                                     <11>1 \A a \in s.stronglysees: Votes[p][a][e] = TRUE \/ Votes[p][a][e] = FALSE
                                                           BY <2>3, <1>2, <3>1, <4>1 DEF TypeOK, VotesType, VoteTn
                                                     <11>2 Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j}) = Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)} \cup {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)})
                                                           BY <2>3, Pslt1 , <11>1
                                                     <11>3 {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)} \cap {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)} = {}
                                                           <12>1 ASSUME {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)} \cap {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)} # {}
                                                                 PROVE FALSE
                                                                  <13>1 \E i \in ProcessSet: i \in {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)} /\ i \in {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)}
                                                                     BY <12>1
                                                                  <13>2 \E i \in ProcessSet, a \in s.stronglysees, u \in s.stronglysees : a.source = u.source /\ Votes[p][a][e] = TRUE  /\ Votes[p][u][e] = FALSE /\ a.frame = u.frame /\ s \in WitnessDAG[p][s.frame][s.source]
                                                                      BY <13>1, Pslt1, <2>3 DEF VoteTn
                                                                  <13>4 \E i \in ProcessSet, a \in s.stronglysees, u \in s.stronglysees : a = u /\ Votes[p][a][e] = TRUE  /\ Votes[p][u][e] = FALSE
                                                                      BY <13>2, <2>3, Pslt1 DEF UniqueStronglyseenAs
                                                                  <13> QED BY <13>4
                                                           <12> QED BY <12>1
                                                    <11>4 Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j}) = Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)}) + Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)})
                                                         BY <11>2, <11>3, CardLm
                                                    <11>5  ASSUME {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)} = {} PROVE
                                                           FALSE
                                                           <12>1 Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)}) = 0
                                                                 <13>1 Cardinality({}) = 0
                                                                       BY emptyCard
                                                                 <13> QED BY <11>5, <13>1
                                                           <12>2  2*f < Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)})
                                                                 BY <12>1, <11>4, intCard, Pslt5, natfAs
                                                           <12> QED BY <12>2, <10>3
                                                    <11> QED BY <8>1, <11>5
                                               <10> QED BY <10>1, <10>2, <10>3
                                          <9> QED BY <9>1, <9>2, <9>3
                                     <8>2 CASE VoteIn(p, s, e) = FALSE
                                          <9>1 CASE s.frame = e.frame+1
                                               BY <5>1, <4>1, Pslt1, <2>3, <9>1
                                          <9>2 CASE ~(s.frame = e.frame+1) /\ ((s.frame - e.frame)%c # 0) 
                                               <10>1 s.frame > e.frame+1 /\ Votes'[p][s][e] = FALSE /\ (s.frame - e.frame)%c # 0
                                                    BY <5>1, <4>1, <2>3, Pslt1, <8>2, <7>2,<9>2
                                               <10>2 Cardinality({j \in ProcessSet: \E a \in s.stronglysees : a.source = j /\ Votes'[p][a][e] = FALSE}) > f
                                                    BY <10>1, <2>3, <1>2 DEF Inv4
                                               <10>3 {j \in ProcessSet: \E a \in s.stronglysees : a.source = j /\ Votes'[p][a][e] = FALSE} # {}
                                                     BY nonemptySet, <10>2
                                               <10>4 \E j \in ProcessSet: \E a \in s.stronglysees :  Votes'[p][a][e] = FALSE
                                                     BY <10>3
                                               <10> QED BY <10>4, <8>2, <7>3
                                          <9>3 CASE ~(s.frame = e.frame+1) /\ ~((s.frame - e.frame)%c # 0)
                                               <10>1 CASE Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]}) > 2*f
                                                     BY <9>3, <10>1, <8>2 DEF VoteIn
                                               <10>2 CASE ~(Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]}) > 2*f)  /\ (Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]= FALSE}) > 2*f)
                                                     BY <10>2, <8>2, nonemptySet
                                               <10>3 CASE ~(Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]}) > 2*f) /\ ~(Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ Votes[p][a][e]= FALSE}) > 2*f)
                                                     <11>1 \A a \in s.stronglysees: Votes[p][a][e] = TRUE \/ Votes[p][a][e] = FALSE
                                                           BY <2>3, <1>2, <3>1, <4>1 DEF TypeOK, VotesType, VoteTn
                                                     <11>2 Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j}) = Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)} \cup {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)})
                                                           BY <2>3, Pslt1 , <11>1
                                                     <11>3 {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)} \cap {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)} = {}
                                                           <12>1 ASSUME {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)} \cap {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)} # {}
                                                                 PROVE FALSE
                                                                  <13>1 \E i \in ProcessSet: i \in {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)} /\ i \in {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)}
                                                                     BY <12>1
                                                                  <13>2 \E i \in ProcessSet, a \in s.stronglysees, u \in s.stronglysees : a.source = u.source /\ Votes[p][a][e] = TRUE  /\ Votes[p][u][e] = FALSE /\ a.frame = u.frame /\ s \in WitnessDAG[p][s.frame][s.source]
                                                                      BY <13>1, Pslt1, <2>3 DEF VoteTn
                                                                  <13>4 \E i \in ProcessSet, a \in s.stronglysees, u \in s.stronglysees : a = u /\ Votes[p][a][e] = TRUE  /\ Votes[p][u][e] = FALSE
                                                                      BY <13>2, <2>3, Pslt1 DEF UniqueStronglyseenAs
                                                                  <13> QED BY <13>4
                                                           <12> QED BY <12>1
                                                    <11>4 Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j}) = Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)}) + Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)})
                                                         BY <11>2, <11>3, CardLm
                                                    <11>5  ASSUME {j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)} = {} PROVE
                                                           FALSE
                                                           <12>1 Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = FALSE)}) = 0
                                                                 <13>1 Cardinality({}) = 0
                                                                       BY emptyCard
                                                                 <13> QED BY <11>5, <13>1
                                                           <12>2  2*f < Cardinality({j \in ProcessSet: \E a \in s.stronglysees: a.source = j /\ (Votes[p][a][e] = TRUE)})
                                                                 BY <12>1, <11>4, intCard, Pslt5, natfAs
                                                           <12> QED BY <12>2, <10>3
                                                    <11> QED BY <8>2, <11>5
                                               <10> QED BY <10>1, <10>2, <10>3
                                          <9> QED BY <9>1, <9>2, <9>3
                                     <8> QED BY <8>1, <8>2, <7>5
                                <7> QED BY <7>2, <7>3, <7>4, <7>1, <7>6
                           <6>4 ASSUME NEW a \in WitnessSet, a.frame < h.frame 
                                PROVE Votes[q][a][e] = Votes'[q][a][e]
                                <7>1 a # s
                                     BY <6>4, <4>1
                                <7> QED BY <3>1, <4>1, <2>3, <7>1, <2>1 DEF VoteTn, TypeOK, VotesType
                           <6>1 CASE x = h.frame-1
                                BY <6>3, <6>1, Pslt1, <3>1, <4>1
                           <6>2 CASE x < h.frame-1
                                <7>1 ASSUME NEW a \in h.stronglysees, a \in WitnessDAG[q][a.frame][a.source], a.frame = h.frame-1, Votes[q][a][g] = Votes'[q][h][g]
                                     PROVE \E b \in WitnessSet: b \in WitnessDAG[q][b.frame][b.source] /\ b.frame = x /\ Votes[q][b][g] = Votes[q][a][g]
                                     BY <1>2, <3>1, <6>2, <7>1, Pslt1 DEF Inv5
                                <7>2 ASSUME NEW b \in WitnessSet, b.frame =x
                                     PROVE Votes'[q][b][g] = Votes[q][b][g]
                                     <8>1 b # s
                                          BY <6>2, Pslt1, <7>2, <4>1
                                     <8> QED BY <8>1, <3>1, <7>2, <2>3, <1>2 DEF VoteTn, TypeOK, VotesType
                                <7> QED BY <7>1, <6>3, <2>3, <6>4, Pslt1, <7>2, <4>1 DEF VoteTn
                           <6> QED BY <6>1, <6>2, <3>1, Pslt1 DEF Frames
                      <5>2 CASE h.frame-1 = g.frame
                           BY Pslt1, <3>1, <5>2 DEF Frames
                      <5> QED BY <5>1, <5>2, Pslt1, <3>1, <4>1, <2>3 DEF VoteTn
                 <4>2 CASE p # q \/ g # e \/ h # s
                      <5>1 WitnessDAG = WitnessDAG'
                           BY <2>3 DEF VoteTn
                      <5>2 Votes[q][h][g] = Votes'[q][h][g]
                           BY <4>2, <2>3, <1>2, <3>1 DEF VoteTn, TypeOK, VotesType
                      <5>3 ASSUME NEW a \in WitnessSet, Votes[q][a][g] # "undecided"
                           PROVE Votes[q][a][g] = Votes'[q][a][g]
                           BY <5>3, <2>3, <1>2, <3>1 DEF VoteTn, TypeOK, VotesType
                      <5> QED BY <5>1, <5>2, <5>3, <3>1, <1>2 DEF Inv5
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1 DEF Inv5
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv5'
            BY <1>2, <2>4 DEF Inv5, DecideFrameTn
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv5'
            BY <2>5, <1>2 DEF vars, Inv5
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness, Inv4proof, Inv3proof DEF Spec

Inv6 == \A p \in ProcessSet, e \in WitnessSet, a \in WitnessSet: a.frame = e.frame+1 /\ Votes[p][a][e] = TRUE => e \in a.stronglysees

LEMMA Inv6proof == Spec => []Inv6
  <1>1 TypeOK /\ Init => Inv6
       BY unequalTF DEF Init, Inv6, InitVotes, TypeOK, VotesType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv6
       PROVE Inv6' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv6'
            BY <2>1, <1>2 DEF AddWitnessTn, Inv6
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv6'
            BY <2>2, <1>2 DEF DecideFameTn, Inv6
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e)
            PROVE Inv6'
            <3>1 ASSUME NEW j \in ProcessSet, NEW b \in WitnessSet, NEW z \in WitnessSet, z.frame = b.frame+1, Votes'[j][z][b] = TRUE
                 PROVE b \in z.stronglysees
                 <4>1 CASE j = p /\ b = e /\ s = z
                      BY <4>1, <3>1, <2>3, <1>2 DEF Inv6, TypeOK, VotesType, VoteTn, VoteIn
                 <4>2 CASE j# p \/ b # e \/ s # z
                      BY <4>2, <3>1, <2>3, <1>2 DEF Inv6, TypeOK, VotesType, VoteTn
                 <4> QED BY <4>1, <4>2     
            <3> QED BY <3>1 DEF Inv6
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv6'
            BY <2>4, <1>2 DEF DecideFrameTn, Inv6
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv6'
            BY <2>5, <1>2 DEF vars, Inv6
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness DEF Spec 

Inv7 == \A i \in ProcessSet, b \in WitnessSet, z \in WitnessSet: z.frame >= b.frame+1 /\ Votes[i][z][b] \in BOOLEAN => Votes[i][z][b] = VoteIn(i, z, b)

LEMMA Inv7proof == Spec => []Inv7
  <1>1 TypeOK /\ Init => Inv7
       BY unequalTF DEF Init, Inv7, InitVotes, TypeOK, VotesType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv7, Inv1
       PROVE Inv7' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv7'
            BY <2>1, <1>2 DEF AddWitnessTn, Inv7, VoteIn
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv7'
            BY <2>2, <1>2 DEF DecideFameTn, Inv7, VoteIn
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e)
            PROVE Inv7'
            <3>1 ASSUME NEW i \in ProcessSet, NEW b \in WitnessSet, NEW z \in WitnessSet, Votes'[i][z][b] \in BOOLEAN, z.frame >= b.frame+1  PROVE Votes'[i][z][b] = VoteIn(i, z, b)'
                  <4>2 ASSUME NEW a \in z.stronglysees, z.frame> b.frame+1, Votes[i][z][b] # "undecided"
                       PROVE Votes[i][a][b] = Votes'[i][a][b]
                       <5>1 a \in WitnessSet
                            BY <4>2, <3>1, Pslt1
                       <5>3 Votes[i][a][b] # "undecided"
                            BY <5>1, <3>1, <4>2, <1>2 DEF Inv1
                       <5>4 Votes[i][a][b] = Votes'[i][a][b]
                            <6>1 CASE p = i /\ a = s /\ b = e
                                 BY <5>3, <6>1, <2>3 DEF VoteTn
                            <6>2 CASE p # i \/ a # s \/ b # e
                                 BY <6>2, <5>1, <3>1, <2>3, <1>2 DEF VoteTn, TypeOK, VotesType
                            <6> QED BY <6>1, <6>2
                       <5> QED BY <5>4
                  <4>3 CASE p = i /\ e = b /\ s = z
                       <5>2 ASSUME NEW a \in s.stronglysees
                            PROVE Votes[p][a][e] = Votes'[p][a][e]
                            <6>1 a # s /\ a \in WitnessSet
                                 BY Pslt1, <2>3, <5>2
                            <6> QED BY <6>1, <4>3, <2>3, <1>2 DEF VoteTn, TypeOK, VotesType
                       <5>1 VoteIn(p, s, e)' = VoteIn(p, s, e)
                            BY <5>2 DEF VoteIn
                       <5> QED BY <5>1, <4>3, <2>3 , <1>2 DEF VoteTn, TypeOK, VotesType
                  <4>4 CASE p # i \/ e # b \/ s # z
                       <5>1 Votes'[i][z][b] = Votes[i][z][b] /\ Votes'[i][z][b] # "undecided"
                            BY <4>4, <3>1, <2>3, <1>2, unequalTF DEF TypeOK, VotesType, VoteTn
                       <5>2 VoteIn(i, z, b)' =VoteIn(i, z, b)
                            <6>1 CASE z.frame = b.frame+1
                                 BY <6>1 DEF VoteIn
                            <6>2 CASE z.frame > b.frame+1
                                 BY <6>2, <4>2, <5>1 DEF VoteIn
                            <6>3 z.frame # b.frame+1 => z.frame > b.frame+1
                                 BY <3>1, <2>3, Pslt1
                            <6> QED BY<6>1, <6>2, <6>3
                       <5> QED BY <5>1, <5>2, <3>1, <1>2 DEF Inv7
                  <4> QED BY <4>3, <4>4
            <3> QED BY <3>1 DEF Inv7 \* BY <2>3, <1>2 DEF VoteTn, Inv7, VoteIn
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv7'
            BY <2>4, <1>2 DEF DecideFrameTn, Inv7, VoteIn
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv7'
            BY <2>5, <1>2 DEF vars, Inv7, VoteIn
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness, Inv1proof DEF Spec 

Inv8 == \A p \in ProcessSet, q \in ProcessSet, s \in WitnessSet, e \in WitnessSet: s.frame >= e.frame+1 /\ Votes[p][s][e] \in BOOLEAN /\ Votes[q][s][e] \in BOOLEAN => Votes[p][s][e] = Votes[q][s][e]

LEMMA Inv8proof == Spec => []Inv8
  <1>1 TypeOK /\ Init => Inv8
       BY unequalTF DEF Init, Inv8, InitVotes, TypeOK, VotesType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv8, Inv1, Inv7
       PROVE Inv8' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv8'
            BY <2>1, <1>2 DEF AddWitnessTn, Inv8
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv8'
            BY <2>2, <1>2 DEF DecideFameTn, Inv8
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e)
            PROVE Inv8'
            <3>1 ASSUME NEW i \in ProcessSet, NEW j \in ProcessSet, NEW b \in WitnessSet, NEW z \in WitnessSet,  Votes'[i][z][b] \in BOOLEAN, Votes'[j][z][b] \in BOOLEAN, z.frame >= b.frame+1
                 PROVE Votes'[i][z][b] = Votes'[j][z][b]
                 <4>1 CASE i = p /\ j # p /\ b = e /\ z = s
                       <5>1 Votes'[p][s][e] = VoteIn(p, s, e) /\ Votes[j][s][e] = Votes'[j][s][e]
                           BY <2>3, <1>2, <4>1 DEF VoteTn, TypeOK, VotesType
                       <5>4 ASSUME NEW a \in s.stronglysees, s.frame > e.frame+1 PROVE Votes[j][a][e] = Votes[p][a][e]
                            <6>1 a \in WitnessSet  /\ a.frame = s.frame-1
                                BY <2>3, Pslt1, <5>4
                            <6>4 a.frame >= e.frame+1
                                 <7>1 a.frame \in Nat /\ e.frame \in Nat /\ s.frame \in Nat
                                      BY Pslt1, <2>3, <5>4
                                 <7>2 s.frame > e.frame+1 /\ a.frame = s.frame-1 
                                      BY <5>4, <6>1
                                 <7>3 a.frame >= e.frame+1
                                      BY <7>1, <7>2 
                                 <7> QED BY <7>3 \*Pslt1, <6>1, <5>4, <2>3, intInv12
                            <6>2 Votes[j][a][e] \in BOOLEAN
                                 <7>1 Votes[j][a][e] # "undecided"
                                      <8>1 Votes[j][s][e] # "undecided"
                                           BY <5>1, <4>1, <3>1, unequalTF
                                      <8> QED BY <8>1, <3>1, <2>3, <5>4, <1>2 DEF Inv1
                                 <7>2 Votes[j][a][e] \in BOOLEAN \cup {"undecided"}
                                      BY <6>1, <2>3, <1>2, <3>1 DEF TypeOK, VotesType
                                 <7> QED BY <7>1, <7>2
                            <6>3 Votes[p][a][e] \in BOOLEAN
                                 <7>1 Votes[p][a][e] # "undecided"
                                      BY <5>4, <2>3,<1>2 DEF TypeOK, VotesType, VoteTn
                                 <7>2 Votes[p][a][e] \in BOOLEAN \cup {"undecided"}
                                      BY <6>1, <2>3, <1>2 DEF TypeOK, VotesType
                                 <7> QED BY <7>1, <7>2
                            <6> QED BY <6>1, <6>2, <6>3, <1>2, <3>1, <4>1, <6>4 DEF Inv8
                       <5>5 Votes[j][s][e] = VoteIn(j, s, e)
                            <6>1 Votes[j][s][e] \in BOOLEAN => VoteIn(j, s, e) = Votes[j][s][e]
                                 BY <2>3, <3>1, <1>2, <4>1 DEF Inv7
                            <6> QED BY <5>1, <3>1, <4>1, <6>1
                       <5>6 VoteIn(j, s, e) = VoteIn(p, s, e)
                            <6>1 CASE s.frame # e.frame+1 
                                 <7>1 s.frame > e.frame+1 
                                      BY <3>1, <4>1, <6>1
                                 <7> QED BY <7>1, <5>4 DEF VoteIn
                            <6>2 CASE s.frame = e.frame+1
                                 BY <6>2 DEF VoteIn
                            <6> QED BY <6>1, <6>2
                       <5> QED BY <5>5, <5>6, <5>1, <4>1
                 <4>2 CASE i # p /\ j = p /\ b = e /\ z = s
                      <5>1 Votes'[p][s][e] = VoteIn(p, s, e) /\ Votes[i][s][e] = Votes'[i][s][e]
                           BY <2>3, <1>2, <4>2 DEF VoteTn, TypeOK, VotesType
                       <5>4 ASSUME NEW a \in s.stronglysees, s.frame > e.frame+1 PROVE Votes[i][a][e] = Votes[p][a][e]
                            <6>1 a \in WitnessSet  /\ a.frame = s.frame-1
                                BY <2>3, Pslt1, <5>4
                            <6>4 a.frame >= e.frame+1
                                 <7>1 a.frame \in Nat /\ e.frame \in Nat /\ s.frame \in Nat
                                      BY Pslt1, <2>3, <5>4
                                 <7>2 s.frame > e.frame+1 /\ a.frame = s.frame-1 
                                      BY <5>4, <6>1
                                 <7>3 a.frame >= e.frame+1
                                      BY <7>1, <7>2 
                                 <7> QED BY <7>3 \*Pslt1, <6>1, <5>4, <2>3, intInv12
                            <6>2 Votes[i][a][e] \in BOOLEAN
                                 <7>1 Votes[i][a][e] # "undecided"
                                      <8>1 Votes[i][s][e] # "undecided"
                                           BY <5>1, <4>2, <3>1, unequalTF
                                      <8> QED BY <8>1, <3>1, <2>3, <5>4, <1>2 DEF Inv1
                                 <7>2 Votes[i][a][e] \in BOOLEAN \cup {"undecided"}
                                      BY <6>1, <2>3, <1>2, <3>1 DEF TypeOK, VotesType
                                 <7> QED BY <7>1, <7>2
                            <6>3 Votes[p][a][e] \in BOOLEAN
                                 <7>1 Votes[p][a][e] # "undecided"
                                      BY <5>4, <2>3,<1>2 DEF TypeOK, VotesType, VoteTn
                                 <7>2 Votes[p][a][e] \in BOOLEAN \cup {"undecided"}
                                      BY <6>1, <2>3, <1>2 DEF TypeOK, VotesType
                                 <7> QED BY <7>1, <7>2
                            <6> QED BY <6>1, <6>2, <6>3, <1>2, <3>1, <4>2, <6>4 DEF Inv8
                       <5>5 Votes[i][s][e] = VoteIn(i, s, e)
                            <6>1 Votes[i][s][e] \in BOOLEAN => VoteIn(i, s, e) = Votes[i][s][e]
                                 BY <2>3, <3>1, <1>2, <4>2 DEF Inv7
                            <6> QED BY <5>1, <3>1, <4>2, <6>1
                       <5>6 VoteIn(i, s, e) = VoteIn(p, s, e)
                            <6>1 CASE s.frame # e.frame+1 
                                 <7>1 s.frame > e.frame+1 
                                      BY <3>1, <4>2, <6>1
                                 <7> QED BY <7>1, <5>4 DEF VoteIn
                            <6>2 CASE s.frame = e.frame+1
                                 BY <6>2 DEF VoteIn
                            <6> QED BY <6>1, <6>2
                       <5> QED BY <5>5, <5>6, <5>1, <4>2
                 <4>3 CASE i = j
                      BY <4>3
                 <4>4 CASE (i # p /\ j # p) \/ b # e \/ z # s
                      <5>1 Votes'[i][z][b] = Votes[i][z][b] /\ Votes'[j][z][b] = Votes[j][z][b]
                           BY <4>4, <3>1, <2>3, <1>2 DEF VoteTn, TypeOK, VotesType
                      <5> QED BY <5>1, <3>1, <1>2 DEF Inv8
                 <4> QED BY <4>1, <4>2, <4>3, <4>4
            <3> QED BY <3>1 DEF Inv8
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv8'
            BY <2>4, <1>2 DEF DecideFrameTn, Inv8
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv8'
            BY <2>5, <1>2 DEF vars, Inv8
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness, Inv7proof, Inv1proof DEF Spec 
  
Inv9 == \A p \in ProcessSet, e \in WitnessSet: e \in WitnessDAG[p][e.frame][e.source] => 
           /\ \A s \in e.stronglysees: s \in WitnessDAG[p][s.frame][s.source]
           /\ Cardinality({q \in ProcessSet: \E a \in e.stronglysees: a.source = q /\ a.frame = e.frame-1 /\ a \in WitnessDAG[p][a.frame][a.source]})> 2*f

LEMMA Inv9proof == Spec => []Inv9
  <1>1 TypeOK /\ Init => Inv9
       BY Pslt1 DEF Init, Inv9, InitWitnessDAG, TypeOK, WitnessDAGType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv9
       PROVE Inv9' 
       <2>1 ASSUME NEW j \in ProcessSet, NEW b \in WitnessSet, AddWitnessTn(j, b)
            PROVE Inv9'
            <3>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, e \in WitnessDAG'[p][e.frame][e.source]
                 PROVE /\ \A s \in e.stronglysees: s \in WitnessDAG'[p][s.frame][s.source]
                       /\ Cardinality({q \in ProcessSet: \E a \in e.stronglysees: a.source = q /\ a.frame = e.frame-1 /\ a \in WitnessDAG'[p][a.frame][a.source]})> 2*f
                 <4>3 ASSUME NEW a \in e.stronglysees, a \in WitnessDAG[p][a.frame][a.source]
                      PROVE a \in WitnessDAG'[p][a.frame][a.source]
                      <5>1 CASE p = j /\ a = b
                           BY <4>3, <5>1, <2>1 DEF AddWitnessTn
                      <5>2 CASE p # j \/ a # b
                           <6>1 CASE a.frame = b.frame /\ a.source = b.source
                                BY <6>1, <5>2, <2>1, <1>2, Pslt1, <3>1, <4>3 DEF TypeOK, AddWitnessTn, WitnessDAGType
                           <6>2 CASE a.frame # b.frame \/ a.source # b.source
                                BY <6>2, <5>2, <2>1, <1>2, Pslt1, <3>1, <4>3 DEF TypeOK, AddWitnessTn, WitnessDAGType
                           <6> QED BY <6>1, <6>2
                      <5> QED BY <5>1, <5>2
                 <4>1 CASE p = j /\ e = b
                      <5>1 \A s \in e.stronglysees: WitnessDAG'[p][s.frame][s.source] = WitnessDAG[p][s.frame][s.source]
                           BY Pslt1, <4>1, <2>1, <1>2 DEF TypeOK, AddWitnessTn, WitnessDAGType
                      <5>2 \A s \in e.stronglysees: s \in WitnessDAG'[p][s.frame][s.source]
                           BY <5>1, <4>1, <2>1 DEF AddWitnessTn
                      <5>3 Cardinality({q \in ProcessSet: \E a \in e.stronglysees: a.source = q /\ a.frame = e.frame-1 /\ a \in WitnessDAG'[p][a.frame][a.source]})> 2*f
                           BY <5>1, <4>1, <2>1 DEF AddWitnessTn
                      <5> QED BY <5>3, <5>2
                 <4>2 CASE p # j \/ e # b
                      <5>1 e \in WitnessDAG[p][e.frame][e.source]
                           <6>1 CASE e.frame = b.frame /\ e.source = b.source
                                BY <6>1, <4>2, <2>1, <1>2, Pslt1, <3>1 DEF TypeOK, AddWitnessTn, WitnessDAGType
                           <6>2 CASE e.frame # b.frame \/ e.source # b.source
                                BY <6>2, <4>2, <2>1, <1>2, Pslt1, <3>1 DEF TypeOK, AddWitnessTn, WitnessDAGType
                           <6> QED BY <6>1, <6>2
                      <5>4 /\ \A s \in e.stronglysees: s \in WitnessDAG[p][s.frame][s.source]
                           /\ Cardinality({q \in ProcessSet: \E a \in e.stronglysees: a.source = q /\ a.frame = e.frame-1 /\ a \in WitnessDAG[p][a.frame][a.source]})> 2*f
                           BY <5>1, <3>1, <1>2 DEF Inv9
                      <5>2 \A s \in e.stronglysees: s \in WitnessDAG'[p][s.frame][s.source]
                           BY <5>4, <4>3
                      <5>3 Cardinality({q \in ProcessSet: \E a \in e.stronglysees: a.source = q /\ a.frame = e.frame-1 /\ a \in WitnessDAG'[p][a.frame][a.source]})> 2*f
                           <6>1 Cardinality({q \in ProcessSet: \E a \in e.stronglysees: a.source = q /\ a.frame = e.frame-1 /\ a \in WitnessDAG'[p][a.frame][a.source]}) >= Cardinality({q \in ProcessSet: \E a \in e.stronglysees: a.source = q /\ a.frame = e.frame-1 /\ a \in WitnessDAG[p][a.frame][a.source]})
                                BY subsetCard, <4>3
                           <6> QED BY <5>4, <6>1, natfAs, intCard
                      <5> QED BY <5>3, <5>2  
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1, <2>1 DEF  Inv9
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv9'
            BY <2>2, <1>2 DEF DecideFameTn, Inv9
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e)
            PROVE Inv9'
            BY <2>3, <1>2 DEF VoteTn, Inv9
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv9'
            BY <2>4, <1>2 DEF DecideFrameTn, Inv9
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv9'
            BY <2>5, <1>2 DEF vars, Inv9
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness DEF Spec 

Inv10 == \A p \in ProcessSet, e \in WitnessSet: Fame[p][e] = TRUE => 
       \E s \in WitnessSet:
             /\ s.frame > e.frame+1
             /\ (s.frame-e.frame)%c # 0
             /\ Cardinality({d \in ProcessSet: \E a \in s.stronglysees: a.source = d /\ Votes[p][a][e]=TRUE}) > 2*f
             /\ s \in WitnessDAG[p][s.frame][s.source]
             /\ Votes[p][s][e] = TRUE
             
THEOREM Inv10proof == Spec => []Inv10
  <1>1 ASSUME TypeOK, Init PROVE Inv10
       BY <1>1, unequalTF DEF Init, Inv10, InitFame, TypeOK, FameType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv10
       PROVE Inv10' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv10'
            <3>1 ASSUME NEW q \in ProcessSet, NEW a \in WitnessSet, Fame[q][a] = TRUE
                 PROVE \E s \in WitnessSet: /\ s.frame > a.frame+1
                                            /\ (s.frame-a.frame)%c # 0
                                            /\ Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=TRUE}) > 2*f
                                            /\ s \in WitnessDAG'[q][s.frame][s.source]
                                            /\ Votes[q][s][a] = TRUE
                <4>1 ASSUME NEW z \in WitnessSet
                     PROVE z \in WitnessDAG[q][z.frame][z.source] => z \in WitnessDAG'[q][z.frame][z.source]
                     BY <4>1, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType, FameType, DecidedFramesType, FamousWitnessesType
                <4> QED BY <4>1, <3>1, <2>1,<1>2 DEF Inv10
            <3> QED BY <2>1, <1>2, <3>1 DEF AddWitnessTn, Inv10
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW b \in WitnessSet, DecideFameTn(p, b, e)
            PROVE Inv10'
            <3>1 ASSUME NEW q \in ProcessSet, NEW a \in WitnessSet, Fame'[q][a] = TRUE
                 PROVE \E s \in WitnessSet: /\ s.frame > a.frame+1
                                            /\ (s.frame-a.frame)%c # 0
                                            /\ Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=TRUE}) > 2*f
                                            /\ s \in WitnessDAG[q][s.frame][s.source]
                                            /\ Votes[q][s][a] = TRUE
                 <4>1 CASE p = q /\ a = e
                      <5>1 FameIn(p, b, e) = TRUE
                           <6>1 Fame'[p][e] = FameIn(p, b, e)
                              BY <2>2, <1>2, <3>1 DEF TypeOK, FameType, DecideFameTn
                           <6> QED BY <6>1, <3>1, <4>1
                      <5>2 /\ b.frame > e.frame+1
                           /\ (b.frame-e.frame)%c # 0
                           /\ Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes[p][z][e]=TRUE}) > 2*f
                           /\ b \in WitnessDAG[p][b.frame][b.source]
                           /\ Votes[p][b][e] = TRUE
                           BY <2>2, <5>1, <3>1 DEF DecideFameTn, FameIn
                      <5> QED BY <5>2, <2>2, <4>1
                 <4>2 CASE p # q \/ a # e
                      BY <4>2, <3>1, <1>2, <2>2 DEF DecideFameTn, TypeOK, FameType, Inv10
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1, <2>2, <1>2 DEF DecideFameTn, Inv10 
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW b \in WitnessSet, VoteTn(p, b, e)
            PROVE Inv10'
            <3>1 ASSUME NEW q \in ProcessSet, NEW a \in WitnessSet, Fame[q][a] = TRUE
                 PROVE \E s \in WitnessSet: /\ s.frame > a.frame+1
                                            /\ (s.frame-a.frame)%c # 0
                                            /\ Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes'[q][z][a]=TRUE}) > 2*f
                                            /\ s \in WitnessDAG[q][s.frame][s.source]
                                            /\ Votes'[q][s][a] = TRUE
                 <4>1 ASSUME NEW s \in WitnessSet, NEW z \in WitnessSet
                      PROVE Votes[q][s][z] = TRUE => Votes'[q][s][z] = TRUE
                      <5>1 CASE q = p /\ s = b /\ z = e
                           <6>1 Votes[q][s][z] = "undecided"
                                BY <5>1, <2>3 DEF VoteTn
                           <6> QED BY <6>1, unequalTF
                      <5>2 CASE q # p \/ s # b \/ z # e
                           BY <5>2, <2>3, <1>2, <3>1 DEF TypeOK, VotesType, VoteTn
                      <5> QED BY <5>1, <5>2
                 <4>2 ASSUME NEW s \in WitnessSet PROVE Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=TRUE}) <= Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes'[q][z][a]=TRUE})
                      <5>1 \A z \in s.stronglysees: Votes[q][z][a]=TRUE => Votes'[q][z][a]=TRUE
                           BY Pslt1, <4>1, <3>1
                      <5> QED BY <5>1, subsetCard
                 <4>3 \E s \in WitnessSet: /\ s.frame > a.frame+1
                                           /\ (s.frame-a.frame)%c # 0
                                           /\ Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=TRUE}) > 2*f
                                           /\ s \in WitnessDAG[q][s.frame][s.source]
                                           /\ Votes[q][s][a] = TRUE
                      BY <3>1, <1>2 DEF Inv10
                 <4>4 ASSUME NEW s \in WitnessSet, Votes[q][s][a] = TRUE, Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=TRUE}) > 2*f
                      PROVE /\ Votes'[q][s][a] = TRUE 
                            /\ (Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes'[q][z][a]=TRUE}) > 2*f)
                      <5>1 Votes'[q][s][a] = TRUE
                           BY <4>1, <3>1, <4>4
                      <5>2 Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes'[q][z][a]=TRUE}) > 2*f
                           <6>1 Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes'[q][z][a]=TRUE}) >= Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=TRUE})
                                BY <4>4, <4>2
                           <6> QED BY <6>1, <4>4, natfAs, intCard
                      <5> QED BY <5>1, <5>2
                 <4> QED BY <4>3, <4>4
            <3> QED BY <2>3, <1>2, <3>1 DEF VoteTn, Inv10
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv10'
            BY <2>4, <1>2, <1>1 DEF DecideFrameTn, Inv10
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv10'
            BY <2>5, <1>2 DEF vars, Inv10
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness DEF Spec

Inv11 == \A p \in ProcessSet, e \in WitnessSet: Fame[p][e] = FALSE => \E s \in WitnessSet:
             /\ s.frame > e.frame+1
             /\ (s.frame-e.frame)%c # 0
             /\ Cardinality({d \in ProcessSet: \E a \in s.stronglysees: a.source = d /\ Votes[p][a][e]=FALSE}) > 2*f
             /\ s \in WitnessDAG[p][s.frame][s.source]
             /\ Votes[p][s][e] = FALSE
               
THEOREM Inv11proof == Spec => []Inv11
  <1>1 ASSUME TypeOK, Init PROVE Inv11
       BY <1>1, unequalTF DEF Init, Inv11, InitFame, TypeOK, FameType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv11
       PROVE Inv11' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv11'
            <3>1 ASSUME NEW q \in ProcessSet, NEW a \in WitnessSet, Fame[q][a] = FALSE
                 PROVE \E s \in WitnessSet: /\ s.frame > a.frame+1
                                            /\ (s.frame-a.frame)%c # 0
                                            /\ Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=FALSE}) > 2*f
                                            /\ s \in WitnessDAG'[q][s.frame][s.source]
                                            /\ Votes[q][s][a] = FALSE
                <4>1 ASSUME NEW z \in WitnessSet
                     PROVE z \in WitnessDAG[q][z.frame][z.source] => z \in WitnessDAG'[q][z.frame][z.source]
                     BY <4>1, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType, FameType, DecidedFramesType, FamousWitnessesType
                <4> QED BY <4>1, <3>1, <2>1,<1>2 DEF Inv11
            <3> QED BY <2>1, <1>2, <3>1 DEF AddWitnessTn, Inv11
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW b \in WitnessSet, DecideFameTn(p, b, e)
            PROVE Inv11'
            <3>1 ASSUME NEW q \in ProcessSet, NEW a \in WitnessSet, Fame'[q][a] = FALSE
                 PROVE \E s \in WitnessSet: /\ s.frame > a.frame+1
                                            /\ (s.frame-a.frame)%c # 0
                                            /\ Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=FALSE}) > 2*f
                                            /\ s \in WitnessDAG[q][s.frame][s.source]
                                            /\ Votes[q][s][a] = FALSE
                 <4>1 CASE p = q /\ a = e
                      <5>1 FameIn(p, b, e) = FALSE
                           <6>1 Fame'[p][e] = FameIn(p, b, e)
                              BY <2>2, <1>2, <3>1 DEF TypeOK, FameType, DecideFameTn
                           <6> QED BY <6>1, <3>1, <4>1
                      <5>2 /\ b.frame > e.frame+1
                           /\ (b.frame-e.frame)%c # 0
                           /\ Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes[p][z][e]=FALSE}) > 2*f
                           /\ b \in WitnessDAG[p][b.frame][b.source]
                           /\ Votes[p][b][e] = FALSE
                           BY <2>2, <5>1, <3>1 DEF DecideFameTn, FameIn
                      <5> QED BY <5>2, <2>2, <4>1
                 <4>2 CASE p # q \/ a # e
                      <5>1 Fame[q][a] = Fame'[q][a]
                          BY <4>2, <3>1, <1>2, <2>2 DEF DecideFameTn, TypeOK, FameType
                      <5> QED BY <5>1, <1>2 , <3>1 DEF Inv11
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1, <2>2, <1>2 DEF DecideFameTn, Inv11 
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW b \in WitnessSet, VoteTn(p, b, e)
            PROVE Inv11'
            <3>1 ASSUME NEW q \in ProcessSet, NEW a \in WitnessSet, Fame[q][a] = FALSE
                 PROVE \E s \in WitnessSet: /\ s.frame > a.frame+1
                                            /\ (s.frame-a.frame)%c # 0
                                            /\ Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes'[q][z][a]=FALSE}) > 2*f
                                            /\ s \in WitnessDAG[q][s.frame][s.source]
                                            /\ Votes'[q][s][a] = FALSE
                 <4>1 ASSUME NEW s \in WitnessSet, NEW z \in WitnessSet
                      PROVE Votes[q][s][z] = FALSE => Votes'[q][s][z] = FALSE
                      <5>1 CASE q = p /\ s = b /\ z = e
                           <6>1 Votes[q][s][z] = "undecided"
                                BY <5>1, <2>3 DEF VoteTn
                           <6> QED BY <6>1, unequalTF
                      <5>2 CASE q # p \/ s # b \/ z # e
                           BY <5>2, <2>3, <1>2, <3>1 DEF TypeOK, VotesType, VoteTn
                      <5> QED BY <5>1, <5>2
                 <4>2 ASSUME NEW s \in WitnessSet PROVE Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=FALSE}) <= Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes'[q][z][a]=FALSE})
                      <5>1 \A z \in s.stronglysees: Votes[q][z][a]=FALSE => Votes'[q][z][a]=FALSE
                           BY Pslt1, <4>1, <3>1
                      <5> QED BY <5>1, subsetCard
                 <4>3 \E s \in WitnessSet: /\ s.frame > a.frame+1
                                           /\ (s.frame-a.frame)%c # 0
                                           /\ Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=FALSE}) > 2*f
                                           /\ s \in WitnessDAG[q][s.frame][s.source]
                                           /\ Votes[q][s][a] = FALSE
                      BY <3>1, <1>2 DEF Inv11
                 <4>4 ASSUME NEW s \in WitnessSet, Votes[q][s][a] = FALSE, Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=FALSE}) > 2*f
                      PROVE /\ Votes'[q][s][a] = FALSE 
                            /\ (Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes'[q][z][a]=FALSE}) > 2*f)
                      <5>1 Votes'[q][s][a] = FALSE
                           BY <4>1, <3>1, <4>4
                      <5>2 Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes'[q][z][a]=FALSE}) > 2*f
                           <6>1 Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes'[q][z][a]=FALSE}) >= Cardinality({d \in ProcessSet: \E z \in s.stronglysees: z.source = d /\ Votes[q][z][a]=FALSE})
                                BY <4>4, <4>2
                           <6> QED BY <6>1, <4>4, natfAs, intCard
                      <5> QED BY <5>1, <5>2
                 <4> QED BY <4>3, <4>4
            <3> QED BY <2>3, <1>2, <3>1 DEF VoteTn, Inv11
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv11'
            BY <2>4, <1>2, <1>1 DEF DecideFrameTn, Inv11
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv11'
            BY <2>5, <1>2 DEF vars, Inv11
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness DEF Spec

Inv12 == \A p \in ProcessSet, e \in WitnessSet:
        /\ Fame[p][e] = TRUE => \E a \in WitnessSet: a.frame = e.frame+2 /\ a \in WitnessDAG[p][a.frame][a.source] /\ Cardinality({j \in ProcessSet: \E s \in a.stronglysees: s.source = j /\ s.frame = e.frame+1 /\ e \in s.stronglysees /\ s \in WitnessDAG[p][s.frame][s.source]}) > f

LEMMA Inv12proof == Spec => []Inv12
  <1>1 ASSUME Inv3, TypeOK, Inv5, Inv9, Inv6, Inv2
       PROVE Inv12
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, Fame[p][e] = TRUE
            PROVE \E a \in WitnessSet: /\ a.frame = e.frame+2 /\ a \in WitnessDAG[p][a.frame][a.source] 
                                       /\ Cardinality({j \in ProcessSet: \E s \in a.stronglysees: s.source = j /\ s.frame = e.frame+1 /\ e \in s.stronglysees /\ s \in WitnessDAG[p][s.frame][s.source]}) > f
            <3>1 \E b \in WitnessSet: b \in WitnessDAG[p][b.frame][b.source] /\ b.frame = e.frame+2 /\ Votes[p][b][e] = TRUE
                 <4>1 \E s \in WitnessSet: /\ e.frame+2 <= s.frame 
                                           /\ Votes[p][s][e]= TRUE 
                                           /\ s \in WitnessDAG[p][s.frame][s.source]
                      BY <2>1, <1>1 DEF Inv2
                 <4>2 ASSUME NEW s \in WitnessSet, e.frame+2 <= s.frame /\ Votes[p][s][e]= TRUE /\ s \in WitnessDAG[p][s.frame][s.source]
                      PROVE \E b \in WitnessSet: b \in WitnessDAG[p][b.frame][b.source] /\ b.frame = e.frame+2 /\ Votes[p][b][e] = TRUE
                      <5>1 CASE s.frame = e.frame+2
                           BY <5>1, <4>2
                      <5>2 CASE s.frame # e.frame+2 
                           <6>1 s.frame > e.frame+2 /\ e.frame+2 > e.frame
                               BY <5>2, <4>2, Pslt1
                           <6>2 e.frame+2 \in Frames
                                <7>1 s.frame \in Frames /\ e.frame \in Frames
                                     BY Pslt1, <4>2, <2>1
                                <7> QED BY <6>1, <7>1, natrAs DEF Frames
                           <6>3 p \in ProcessSet /\ Votes[p][s][e] # "undecided" /\ e \in WitnessSet
                                BY <2>1, <4>2, unequalTF
                           <6>4 \E b \in WitnessSet: b \in WitnessDAG[p][b.frame][b.source] /\ b.frame = e.frame+2 /\ Votes[p][b][e] = Votes[p][s][e]
                                 BY <6>2, <6>1, <4>2, <6>3, <1>1 DEF Inv5
                           <6> QED BY <6>4, <4>2
                      <5> QED BY <5>1, <5>2
                 <4> QED BY <4>1, <4>2
            <3>2 ASSUME NEW b \in WitnessSet, b \in WitnessDAG[p][b.frame][b.source], b.frame = e.frame+2, Votes[p][b][e] = TRUE
                 PROVE Cardinality({q \in ProcessSet: \E z \in b.stronglysees : z.frame = e.frame+1 /\ z.source = q /\ e \in z.stronglysees /\ z \in WitnessDAG[p][z.frame][z.source]}) > f
                 <4>1 Votes[p][b][e] = TRUE /\ (b.frame - e.frame) % c # 0 /\ b.frame > e.frame+1
                      <5>1 b.frame \in Nat /\ e.frame \in Nat
                           BY <3>2, <2>1, Pslt1
                      <5> QED BY <5>1, <3>2, Pslt1, natcAs
                 <4>2 Cardinality({q \in ProcessSet: \E z \in b.stronglysees : z.frame = e.frame+1 /\ z.source = q /\ Votes[p][z][e] = TRUE}) > f
                      <5>1 b \in WitnessSet /\ e \in WitnessSet /\ p \in ProcessSet
                           BY <3>2, <2>1
                      <5>2 ASSUME NEW z \in b.stronglysees PROVE z.frame = e.frame+1
                           <6>1 z.frame = b.frame-1
                                BY <5>1, Pslt1
                           <6>2 z.frame \in Nat /\ b.frame \in Nat /\ e.frame \in Nat
                                BY <5>2, <5>1, Pslt1
                           <6> QED BY <6>1, <6>2, <3>2
                      <5> QED BY <4>1, <5>1, <1>1, <5>2 DEF Inv3
                 <4>3 \A z \in b.stronglysees: z \in WitnessDAG[p][z.frame][z.source]
                      BY <3>2, <1>1 DEF Inv9
                 <4>4 \A z \in b.stronglysees: z.frame = e.frame+1 /\ Votes[p][z][e] = TRUE => e \in z.stronglysees
                      BY <1>1, <3>2, <2>1, Pslt1 DEF Inv6
                 <4>5 Cardinality({q \in ProcessSet: \E z \in b.stronglysees : z.frame = e.frame+1 /\ z.source = q /\ Votes[p][z][e] = TRUE /\ e \in z.stronglysees /\ z \in WitnessDAG[p][z.frame][z.source]}) > f
                      BY <4>2, <4>3, <4>4
                 <4>6 Cardinality({q \in ProcessSet: \E z \in b.stronglysees : z.frame = e.frame+1 /\ z.source = q /\ Votes[p][z][e] = TRUE /\ e \in z.stronglysees /\ z \in WitnessDAG[p][z.frame][z.source]}) <= Cardinality({q \in ProcessSet: \E z \in b.stronglysees : z.frame = e.frame+1 /\ z.source = q /\ e \in z.stronglysees /\ z \in WitnessDAG[p][z.frame][z.source]})
                      BY subsetCard,  intCard
                 <4>7 f < Cardinality({q \in ProcessSet: \E z \in b.stronglysees : z.frame = e.frame+1 /\ z.source = q /\ e \in z.stronglysees /\ z \in WitnessDAG[p][z.frame][z.source]})
                      BY <4>5, <4>6, intCard, natfAs
                 <4> QED BY <4>7
            <3> QED BY <3>2, <3>1
       <2> QED BY <2>1 DEF Inv12
  <1> QED BY <1>1, Inv3proof, TypeOKcorrectness, PTL, Inv5proof, Inv6proof, Inv9proof, Inv2proof

Inv13 == \A x \in Frames, p \in ProcessSet: DecidedFrames[p][x] => 
         /\ \E a \in WitnessSet: a \in WitnessDAG[p][x+2][a.source] /\ a.frame= x+2
         /\ \A e \in WitnessSet: e \in FamousWitnesses[p][x] => e.frame = x /\ e \in WitnessDAG[p][x][e.source] /\ Fame[p][e] = TRUE


LEMMA Inv13proof == Spec => []Inv13
  <1>1 Init => Inv13
       BY DEF Init, Inv13, InitWitnessDAG, InitVotes, InitFame, InitDecidedFrames, InitFamousWitnesses
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv13
       PROVE Inv13' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv13'
            BY <2>1, <1>2, <1>1 DEF AddWitnessTn, Inv13
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv13'
            <3>1 ASSUME NEW y \in Frames, NEW q \in ProcessSet, NEW b \in WitnessSet, DecidedFrames[q][y]
                 PROVE /\ \E a \in WitnessSet: a \in WitnessDAG[q][y+2][a.source] /\ a.frame= y+2
                       /\ b \in FamousWitnesses[q][y] => b.frame = y /\ b \in WitnessDAG[q][y][b.source] /\ Fame'[q][b] = TRUE
                 <4>1 b \in FamousWitnesses[q][y] => b.frame = y /\ b \in WitnessDAG[q][y][b.source] /\ Fame[q][b] = TRUE
                      BY <3>1, <1>2 DEF Inv13
                 <4>2 CASE q = p /\ b = e
                      <5>2 Fame[q][b] # TRUE
                           BY <4>2, <2>2, unequalTF DEF DecideFameTn
                      <5>1 b \in FamousWitnesses[q][y] => Fame'[q][b] = TRUE
                           BY <5>2, <4>1
                      <5> QED BY <5>1, <2>2, <3>1, <1>2 DEF Inv13
                 <4>3 CASE q # p \/ b # e
                      BY <4>3, <3>1, <1>2, <2>2 DEF DecideFameTn, TypeOK, FameType, Inv13
                 <4> QED BY <4>3, <4>2
            <3> QED BY <3>1, <2>2 DEF DecideFameTn, Inv13 
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e)
            PROVE Inv13'
            BY <2>3, <1>2, <1>1 DEF VoteTn, Inv13
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv13'
            <3>1 ASSUME NEW y \in Frames, NEW q \in ProcessSet, DecidedFrames'[q][y]
                 PROVE /\ \E a \in WitnessSet: a \in WitnessDAG[q][y+2][a.source] /\ a.frame= y+2
                       /\ \A e \in WitnessSet: e \in FamousWitnesses'[q][y] => e.frame = y /\ e \in WitnessDAG[q][y][e.source] /\ Fame[q][e] = TRUE
                 <4>1 CASE x =y /\ p = q
                      <5>1 \E a \in WitnessSet: a \in WitnessDAG[q][y+2][a.source] /\ a.frame= y+2
                           BY <4>1, <2>4 DEF DecideFrameTn
                      <5>2 \A e \in WitnessSet: e \in FamousWitnesses'[q][y] => e.frame = y /\ e \in WitnessDAG[q][y][e.source] /\ Fame[q][e] = TRUE
                           BY <1>2, <4>1, <2>4 DEF DecideFrameTn, TypeOK, FamousWitnessesType, DecidedFramesType
                      <5> QED BY <5>1, <5>2
                 <4>2 CASE x # y \/ p # q
                      BY <3>1, <4>2, <2>4, <1>2 DEF DecideFrameTn, TypeOK, FamousWitnessesType, DecidedFramesType, Inv13
                 <4> QED BY <4>1, <4>2, <2>4 DEF DecideFrameTn
            <3> QED BY <3>1, <2>4 DEF Inv13, DecideFrameTn 
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv13'
            BY <2>5, <1>2 DEF vars, Inv13 
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness DEF Spec 



Inv14 == \A x \in Frames, p \in ProcessSet, s \in WitnessSet: DecidedFrames[p][x] /\ s \notin FamousWitnesses[p][x] /\ s.frame = x
       => Fame[p][s] = FALSE \/ (\E z \in WitnessSet: z.frame = s.frame+2 /\ z \in WitnessDAG[p][z.frame][z.source] /\ Cardinality({q \in ProcessSet: \E a \in z.stronglysees: a.source = q /\ a.frame = s.frame+1 /\ a \in WitnessDAG[p][a.frame][a.source] /\ s \notin a.stronglysees}) > 2*f)


LEMMA Inv14proof == Spec => []Inv14
  <1>1 ASSUME TypeOK, Init PROVE Inv14
       BY <1>1 DEF Init, Inv14, InitVotes, InitFame, InitDecidedFrames, InitFamousWitnesses, TypeOK, FamousWitnessesType
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv14, Inv9
       PROVE Inv14' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv14'
            <3>1 ASSUME NEW y \in Frames, NEW q \in ProcessSet, NEW a \in WitnessSet, DecidedFrames[q][y], a \notin FamousWitnesses[q][y], a.frame = y
                 PROVE Fame[q][a] = FALSE \/ (\E z \in WitnessSet: z.frame = a.frame+2 /\ z \in WitnessDAG'[q][z.frame][z.source] /\ Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG'[q][b.frame][b.source] /\ a \notin b.stronglysees}) > 2*f)
                 <5>1 ASSUME NEW z \in WitnessSet
                      PROVE z \in WitnessDAG[q][z.frame][z.source] => z \in WitnessDAG'[q][z.frame][z.source]
                      BY <5>1, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType, FameType, DecidedFramesType, FamousWitnessesType
                 <5>2 ASSUME NEW z \in WitnessSet, z.frame = a.frame+2, z \in WitnessDAG[q][z.frame][z.source], Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG[q][b.frame][b.source] /\ a \notin b.stronglysees}) > 2*f
                      PROVE z.frame = a.frame+2 /\ z \in WitnessDAG'[q][z.frame][z.source] /\ Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG'[q][b.frame][b.source] /\ a \notin b.stronglysees}) > 2*f
                      <6>1 Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG[q][b.frame][b.source] /\ a \notin b.stronglysees}) <= Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG'[q][b.frame][b.source] /\ a \notin b.stronglysees})
                           <7>1 \A b \in z.stronglysees: b \in WitnessDAG[q][b.frame][b.source] => b \in WitnessDAG'[q][b.frame][b.source]
                                BY <5>1, <5>2, Pslt1
                           <7> QED BY <7>1, subsetCard 
                      <6> QED BY <6>1, <5>1, <5>2, intCard, natfAs
                 <5>3 Fame[q][a] = FALSE \/ (\E z \in WitnessSet: z.frame = a.frame+2 /\ z \in WitnessDAG[q][z.frame][z.source] /\ Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG[q][b.frame][b.source] /\ a \notin b.stronglysees}) > 2*f)
                      BY <3>1, <1>2 DEF Inv14
                 <5> QED BY <5>2, <5>3
            <3> QED BY <3>1, <2>1 DEF AddWitnessTn, Inv14 \*<2>1, <1>2, <1>1 DEF AddWitnessTn, Inv14, TypeOK, WitnessDAGType, FameType, DecidedFramesType, FamousWitnessesType
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv14'
            <3>1 ASSUME NEW y \in Frames, NEW q \in ProcessSet, NEW a \in WitnessSet, DecidedFrames[q][y], a \notin FamousWitnesses[q][y], a.frame = y
                 PROVE Fame'[q][a] = FALSE \/ (\E z \in WitnessSet: z.frame = a.frame+2 /\ z \in WitnessDAG[q][z.frame][z.source] /\ Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG[q][b.frame][b.source] /\ a \notin b.stronglysees}) > 2*f)
                 <4>1 CASE q = p /\ a = e
                      <5>1 Fame[q][a] # FALSE
                           BY unequalTF, <4>1, <2>2 DEF DecideFameTn
                      <5>3 DecidedFrames[q][y] /\ a \notin FamousWitnesses[q][y] /\ a.frame = y
                            BY <3>1
                      <5>2 Fame[q][a] = FALSE \/ (\E z \in WitnessSet: z.frame = a.frame+2 /\ z \in WitnessDAG[q][z.frame][z.source] /\ Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG[q][b.frame][b.source] /\ a \notin b.stronglysees}) > 2*f)
                          BY <5>3, <3>1, <1>2 DEF Inv14  
                      <5> QED BY <5>1, <5>2
                 <4>2 CASE q # p \/ a # e
                      <5>1 Fame[q][a] = Fame'[q][a]
                           BY <4>2, <3>1, <1>2, <2>2 DEF DecideFameTn, TypeOK, FameType, Inv14
                      <5>3 DecidedFrames[q][y] /\ a \notin FamousWitnesses[q][y] /\ a.frame = y
                            BY <3>1
                      <5>2 Fame[q][a] = FALSE \/ (\E z \in WitnessSet: z.frame = a.frame+2 /\ z \in WitnessDAG[q][z.frame][z.source] /\ Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG[q][b.frame][b.source] /\ a \notin b.stronglysees}) > 2*f)
                          BY <5>3, <3>1, <1>2 DEF Inv14  
                      <5> QED BY <5>1, <5>2
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1, <1>2, <2>2 DEF DecideFameTn, Inv14
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e)
            PROVE Inv14'
            BY <2>3, <1>2, <1>1 DEF VoteTn, Inv14
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv14'
            <3>1 ASSUME NEW y \in Frames, NEW q \in ProcessSet, NEW a \in WitnessSet, DecidedFrames'[q][y], a \notin FamousWitnesses'[q][y], a.frame = y
                 PROVE Fame[q][a] = FALSE \/ (\E z \in WitnessSet: z.frame = a.frame+2 /\ z \in WitnessDAG[q][z.frame][z.source] /\ Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG[q][b.frame][b.source] /\ a \notin b.stronglysees}) > 2*f)
                 <4>1 CASE q = p /\ x = y
                      <5>1 a \notin WitnessDAG[p][x][a.source] \/ Fame[p][a] # TRUE
                           <6>1 FamousWitnesses'[q][y] = {g \in WitnessSet: g.frame = x /\ g \in WitnessDAG[q][x][g.source] /\ Fame[q][g] = TRUE}
                                BY <4>1, <2>4, <1>2 DEF DecideFrameTn, TypeOK, DecidedFramesType, FamousWitnessesType
                           <6> QED BY <6>1, <3>1, <4>1
                      <5>2 Fame[p][a] # TRUE => a \notin WitnessDAG[p][x][a.source] \/ Fame[p][a] = FALSE
                           <6>1 a \in WitnessDAG[p][x][a.source] /\ Fame[p][a] # TRUE => Fame[p][a] # "undecided"
                                BY <3>1, <2>4, unequalTF, <1>2, <2>4 DEF DecideFrameTn, TypeOK, FameType
                           <6>2 Fame[p][a] = "undecided" \/ Fame[p][a] = TRUE \/ Fame[p][a] = FALSE \*# "undecided"
                                BY <1>2, <2>4, <3>1 DEF TypeOK, FameType
                           <6>3 Fame[p][a] # "undecided" /\ Fame[p][a] # TRUE => Fame[p][a] = FALSE
                                BY <6>2
                           <6> QED BY <6>3, <6>1
                      <5>3 a \notin WitnessDAG[p][x][a.source] \/ Fame[p][a] = FALSE
                           BY <5>1, <5>2
                      <5>4 a \notin WitnessDAG[p][x][a.source] => \E z \in WitnessSet: z.frame = a.frame+2 /\ z \in WitnessDAG[q][z.frame][z.source] /\ Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG[q][b.frame][b.source] /\ a \notin b.stronglysees}) > 2*f
                           <6>1 \E z \in WitnessSet: z \in WitnessDAG[p][z.frame][z.source] /\ z.frame = a.frame+2
                                BY <4>1, <3>1, <2>4 DEF DecideFrameTn
                           <6>2 ASSUME NEW z \in WitnessSet, z \in WitnessDAG[p][z.frame][z.source], z.frame = a.frame+2, a \notin WitnessDAG[p][x][a.source]
                                PROVE Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = a.frame+1 /\ b \in WitnessDAG[q][b.frame][b.source] /\ a \notin b.stronglysees}) > 2*f
                                <7>1 Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = z.frame-1 /\ b \in WitnessDAG[p][b.frame][b.source]})> 2*f
                                     BY <2>4, <6>2, <1>2 DEF Inv9
                                <7>2 ASSUME NEW b \in z.stronglysees, b \in WitnessDAG[q][b.frame][b.source], b.frame = z.frame-1, a \notin WitnessDAG[p][x][a.source]
                                     PROVE a \notin b.stronglysees
                                     <8>1 a \in b.stronglysees => a \in WitnessDAG[p][a.frame][a.source]
                                          BY <2>4, <7>2, <1>2, <4>1, Pslt1 DEF Inv9
                                     <8> QED BY <8>1, <7>2, <4>1, <3>1
                                <7>3 2*f < Cardinality({j \in ProcessSet: \E b \in z.stronglysees: b.source = j /\ b.frame = z.frame-1 /\ b \in WitnessDAG[p][b.frame][b.source] /\ a \notin b.stronglysees})
                                     BY <7>2, <4>1, subsetCard, intCard, natfAs, <7>1, <6>2
                                <7>4 z.frame-1 = a.frame+1
                                     BY Pslt1, <6>2
                                <7> QED BY <7>3, <4>1, <7>4
                           <6> QED BY <6>1, <6>2, <4>1
                      <5> QED BY <5>4, <5>3, <4>1
                 <4>2 CASE q # p \/ x # y
                      <5>1 DecidedFrames'[q][y] = DecidedFrames[q][y] /\ FamousWitnesses[q][y] = FamousWitnesses'[q][y]
                           BY <3>1, <2>4, <1>2, <4>2 DEF DecideFrameTn, Inv14, TypeOK, DecidedFramesType, FamousWitnessesType
                      <5> QED BY <5>1, <3>1, <1>2 DEF Inv14
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1, <2>4, <1>2 DEF Inv14, DecideFrameTn 
            \*BY <2>4, <1>2, <1>1 DEF DecideFrameTn, Inv14, TypeOK, WitnessDAGType, FameType, DecidedFramesType, FamousWitnessesType
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv14'
            BY <2>5, <1>2 DEF vars, Inv14\*, TypeOK, WitnessDAGType, FameType, DecidedFramesType, FamousWitnessesType
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness, Inv9proof DEF Spec 

Inv15 == \A p \in ProcessSet, q \in ProcessSet, e \in WitnessSet, s \in WitnessSet, g \in WitnessSet: 
       (/\ e \in WitnessDAG[p][e.frame][e.source] 
        /\ s \in WitnessDAG[p][s.frame][s.source]
        /\ s.frame > e.frame+1
        /\ (s.frame-e.frame)%c # 0
        /\ Cardinality({d \in ProcessSet: \E a \in s.stronglysees: a.source = d /\ Votes[p][a][e]=TRUE}) > 2*f
        /\ g \in WitnessDAG[q][g.frame][g.source]
        /\ g.frame >= s.frame) => (Votes[p][s][e] = TRUE => Votes[q][g][e] = "undecided" \/ Votes[q][g][e] = TRUE)
  
THEOREM Inv15proof == Spec => []Inv15
  <1>1 Init => Inv15
       BY DEF Init, Inv15, InitWitnessDAG, InitVotes, InitFame, InitDecidedFrames, InitFamousWitnesses
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv15, Inv9, Inv9', Inv4, Inv4', Inv8, Inv8', Inv5, Inv5', Inv1, Inv1'
       PROVE Inv15' 
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv15'
            <3>1 ASSUME NEW i \in ProcessSet, NEW j \in ProcessSet, NEW a \in WitnessSet, NEW b \in WitnessSet, NEW g \in WitnessSet, b.frame > a.frame+1, (b.frame-a.frame)%c # 0,
                       a \in WitnessDAG'[i][a.frame][a.source], b \in WitnessDAG'[i][b.frame][b.source], g \in WitnessDAG'[j][g.frame][g.source], g.frame >= b.frame,
                       Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a]= TRUE}) > 2*f
                 PROVE Votes'[i][b][a] = TRUE => Votes'[j][g][a] = "undecided" \/ Votes'[j][g][a] = TRUE
                 <4>1 CASE i = p
                      <5>1 CASE e = b
                           BY <5>1, <4>1, <3>1, <2>1, unequalTF DEF AddWitnessTn
                      <5>2 CASE e = a
                           BY <5>2, <4>1, <3>1, <2>1, unequalTF DEF AddWitnessTn
                      <5>3 CASE e # b /\ e # a
                           <6>1 CASE j = p /\ e = g
                                BY <6>1, <3>1, <2>1 DEF AddWitnessTn
                           <6>2 CASE j # p \/ e # g
                                <7>1 a \in WitnessDAG[i][a.frame][a.source]
                                     <8>1 CASE a.frame = e.frame /\ a.source = e.source
                                          BY <8>1, <5>3, <1>2, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType
                                     <8>2 CASE a.frame # e.frame \/ a.source # e.source
                                          BY <8>2, <3>1, <2>1 DEF AddWitnessTn
                                     <8> QED BY <8>1, <8>2
                                <7>2 b \in WitnessDAG[i][b.frame][b.source]
                                     <8>1 CASE b.frame = e.frame /\ b.source = e.source
                                          BY <8>1, <5>3, <1>2, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType
                                     <8>2 CASE b.frame # e.frame \/ b.source # e.source
                                          BY <8>2, <3>1, <2>1 DEF AddWitnessTn
                                     <8> QED BY <8>1, <8>2
                                <7>3 g \in WitnessDAG[j][g.frame][g.source]
                                     <8>1 CASE g.frame = e.frame /\ g.source = e.source
                                          BY <8>1, <6>2, <1>2, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType
                                     <8>2 CASE g.frame # e.frame \/ g.source # e.source
                                          BY <8>2, <3>1, <2>1 DEF AddWitnessTn
                                     <8> QED BY <8>1, <8>2
                                <7>4 \A z \in b.stronglysees : z \in WitnessDAG[i][z.frame][z.source]
                                     BY <1>2, <7>2, <3>1 DEF Inv9
                                <7>5 2*f < Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes[i][z][a]= TRUE})
                                     BY <3>1, <7>4, subsetCard, natfAs, intCard, <2>1 DEF AddWitnessTn
                                <7> QED BY <7>1, <7>2, <7>3, <7>5, <3>1, <2>1, <1>2 DEF Inv15, AddWitnessTn
                           <6> QED BY <6>1, <6>2
                      <5> QED BY <5>1, <5>2, <5>3
                 <4>2 CASE i # p
                      <5>1 CASE j = p /\ e = g
                           BY <5>1, <3>1, <2>1 DEF AddWitnessTn
                      <5>2 CASE j # p \/ e # g
                           <6>1 a \in WitnessDAG[i][a.frame][a.source]
                                BY <4>2, <2>1 , <3>1 DEF AddWitnessTn
                           <6>2 b \in WitnessDAG[i][b.frame][b.source]
                                BY <4>2, <2>1 , <3>1 DEF AddWitnessTn
                           <6>3 g \in WitnessDAG[j][g.frame][g.source]
                                <7>1 CASE g.frame = e.frame /\ g.source = e.source
                                          BY <7>1, <5>2, <1>2, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType
                                <7>2 CASE g.frame # e.frame \/ g.source # e.source
                                          BY <7>2, <3>1, <2>1 DEF AddWitnessTn
                                <7> QED BY <7>1, <7>2
                           <6>4 \A z \in b.stronglysees : z \in WitnessDAG[i][z.frame][z.source]
                                 BY <1>2, <6>2, <3>1 DEF Inv9
                           <6>5 2*f < Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes[i][z][a]=TRUE})
                                BY <3>1, <6>4, subsetCard, natfAs, intCard, <2>1 DEF AddWitnessTn
                           <6> QED BY <6>1, <6>2, <6>3, <6>5, <3>1, <2>1, <1>2 DEF Inv15, AddWitnessTn     
                      <5> QED BY <5>1, <5>2
                 <4> QED BY <4>1, <4>2, <3>1, <2>1 DEF AddWitnessTn
            <3> QED BY <3>1 DEF Inv15
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv15'
            BY <1>2, <2>2 DEF Inv15, DecideFameTn
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e), UniqueStronglyseenAs, UniqueStronglyseenAs'
            PROVE Inv15'
            <3>1 ASSUME NEW i \in ProcessSet, NEW j \in ProcessSet, NEW a \in WitnessSet, NEW b \in WitnessSet, NEW g \in WitnessSet, b.frame > a.frame+1, (b.frame-a.frame)%c # 0,
                       a \in WitnessDAG[i][a.frame][a.source], b \in WitnessDAG[i][b.frame][b.source], g \in WitnessDAG[j][g.frame][g.source], g.frame >= b.frame,
                       Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = TRUE}) > 2*f
                 PROVE Votes'[i][b][a] = TRUE => Votes'[j][g][a] = "undecided" \/ Votes'[j][g][a] = TRUE
                 <4>1 CASE e = a
                      <5>1 CASE i = p /\ b = s
                           <6>1 CASE j = p /\ g = s
                                BY <6>1, <5>1, <3>1
                           <6>2 CASE j # p \/ g # s 
                                <7>1 ASSUME NEW z \in b.stronglysees
                                     PROVE Votes'[i][z][a] = Votes[i][z][a]
                                     BY <7>1, <5>1, Pslt1, <1>2, <3>1, <2>3 DEF VoteTn, TypeOK, VotesType
                                <7>2 Votes'[j][g][a] = Votes[j][g][a]
                                     BY <6>2, <1>2, <3>1, <2>3 DEF VoteTn, TypeOK, VotesType
                                <7>3 Votes[j][g][a] # FALSE
                                     <8>1 CASE g.frame = b.frame
                                          <9>1 Votes[j][g][a] = FALSE => Cardinality({q \in ProcessSet: \E z \in g.stronglysees : z.source = q /\ Votes[j][z][a] = FALSE}) > f
                                               <10>1 g.frame > a.frame+1 /\ (g.frame-a.frame)%c # 0
                                                     BY <8>1, <3>1
                                               <10> QED BY <10>1, <3>1, <1>2 DEF Inv4
                                          <9>2 Votes[j][g][a] = FALSE => {q \in ProcessSet: \E z \in g.stronglysees : z.source = q /\ Votes[j][z][a] = FALSE} \cap {d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = TRUE} # {}
                                               BY <9>1, <3>1, Pslt3
                                          <9>3 Votes[j][g][a] = FALSE => \E q \in ProcessSet, z \in g.stronglysees, o \in b.stronglysees: o.source = q /\ z.source = q /\ Votes[i][o][a] = TRUE /\ Votes[j][z][a] = FALSE /\ z.frame = o.frame
                                               BY <9>2, <7>1, <8>1, Pslt1
                                          <9>4 Votes[j][g][a] = FALSE => \E q \in ProcessSet, z \in g.stronglysees, o \in b.stronglysees: o = z /\ Votes[i][o][a] = TRUE /\ Votes[j][z][a] = FALSE
                                               BY <2>3, <3>1, <9>3, Pslt1 DEF UniqueStronglyseenAs
                                          <9>5 Votes[j][g][a] = FALSE => \E z \in g.stronglysees: Votes[i][z][a] = TRUE /\ Votes[j][z][a] = FALSE
                                               BY <9>4, <3>1, <1>2 DEF Inv8
                                          <9>7 ASSUME NEW z \in g.stronglysees, Votes[i][z][a] = TRUE, Votes[j][z][a] = FALSE
                                               PROVE Votes[i][z][a] = Votes[j][z][a]
                                               <10>1 z \in WitnessSet /\ a \in WitnessSet /\ i \in ProcessSet /\ j \in ProcessSet
                                                     BY <3>1, Pslt1
                                               <10>2 Votes[i][z][a] \in BOOLEAN /\ Votes[j][z][a] \in BOOLEAN
                                                     BY <9>7
                                               <10>3 z.frame >= a.frame+1
                                                     <11>1 z.frame = g.frame-1
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11>2 g.frame > a.frame+1
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11>3 g.frame \in Nat /\ z.frame \in Nat /\ a.frame \in Nat
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11> QED BY <11>1, <11>2, <11>3
                                               <10> QED BY <10>1, <10>2, <1>2, <10>3 DEF Inv8
                                          <9>6 Votes[j][g][a] = FALSE => FALSE \* \E z \in g.stronglysees: Votes[i][z][a] = TRUE /\ Votes[j][z][a] = FALSE /\ Votes[j][z][a] = Votes[i][z][a]
                                               BY <9>5, <9>7 \*<3>1, <1>2, Pslt1 DEF Inv8
                                          <9> QED BY <9>6
                                     <8>2 CASE g.frame # b.frame
                                          <9>1 g.frame > b.frame
                                               BY <8>2, <3>1
                                          <9>2 ASSUME Votes[j][g][a] = FALSE PROVE \E m \in WitnessSet: m \in WitnessDAG[j][m.frame][m.source] /\ m.frame = b.frame /\  Votes[j][m][a] = Votes[j][g][a]\*\E m \in WitnessSet: m \in WitnessDAG[j][m.frame][m.source] /\ m.frame = b.frame /\ Votes[j][m][a] = FALSE
                                               <10>1 j \in ProcessSet /\ g \in WitnessSet /\ a \in WitnessSet /\ b.frame \in Frames
                                                     BY <3>1, Pslt1
                                               <10>2 g \in WitnessDAG[j][g.frame][g.source] 
                                                     BY <3>1, <2>1 DEF VoteTn
                                               <10>3 Votes[j][g][a] # "undecided"
                                                     BY <9>2, unequalTF
                                               <10>4 a.frame < b.frame /\ b.frame < g.frame
                                                     BY <3>1, <9>1, Pslt1
                                               <10>5 b.frame \in Frames
                                                     BY <3>1, Pslt1
                                               <10> QED BY <9>2, <10>1, <10>2, <10>3, <10>4, <10>5, <1>2 DEF Inv5
                                          <9>3 ASSUME NEW m \in WitnessSet, m \in WitnessDAG[j][m.frame][m.source], m.frame = b.frame, Votes[j][m][a] = FALSE
                                               PROVE FALSE
                                               <10>1  Cardinality({q \in ProcessSet: \E z \in m.stronglysees : z.source = q /\ Votes[j][z][a] = FALSE}) > f
                                                    <11>1 (m.frame-a.frame)%c # 0
                                                          BY <3>1, <9>3
                                                    <11>2 Votes[j][m][a] = FALSE
                                                          BY <9>3
                                                    <11> QED BY <11>1, <11>2, <3>1, <1>2, <9>3 DEF Inv4
                                               <10>2 {q \in ProcessSet: \E z \in m.stronglysees : z.source = q /\ Votes[j][z][a] = FALSE} \cap {d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = TRUE} # {}
                                                    BY <10>1, <3>1, Pslt3
                                               <10>3 \E q \in ProcessSet, z \in m.stronglysees, o \in b.stronglysees: o.source = q /\ z.source = q /\ Votes[i][o][a] = TRUE /\ Votes[j][z][a] = FALSE /\ z.frame = o.frame
                                                    BY <10>2, <7>1, <9>3, Pslt1
                                               <10>4  \E q \in ProcessSet, z \in m.stronglysees, o \in b.stronglysees: o = z /\ Votes[i][o][a] = TRUE /\ Votes[j][z][a] = FALSE
                                                    BY <2>3, <3>1, <10>3, Pslt1, <9>3 DEF UniqueStronglyseenAs
                                               <10>5 \E z \in m.stronglysees: Votes[i][z][a] = TRUE /\ Votes[j][z][a] = FALSE
                                                    BY <10>4, <3>1, <1>2 DEF Inv8
                                               <10>7 ASSUME NEW z \in m.stronglysees, Votes[i][z][a] = TRUE, Votes[j][z][a] = FALSE
                                                    PROVE Votes[i][z][a] = Votes[j][z][a]
                                                    <11>1 z \in WitnessSet /\ a \in WitnessSet /\ i \in ProcessSet /\ j \in ProcessSet
                                                          BY <3>1, Pslt1
                                                    <11>2 Votes[i][z][a] \in BOOLEAN /\ Votes[j][z][a] \in BOOLEAN
                                                          BY <10>7
                                                    <11>3 z.frame >= a.frame+1
                                                         <12>1 z.frame = m.frame-1
                                                            BY <10>7, <3>1, <2>3, <9>3, Pslt1
                                                         <12>2 m.frame > a.frame+1
                                                            BY <10>7, <3>1, <2>3, Pslt1, <9>3
                                                         <12>3 m.frame \in Nat /\ z.frame \in Nat /\ a.frame \in Nat
                                                            BY <10>7, <3>1, <2>3, Pslt1, <9>3
                                                         <12> QED BY <12>1, <12>2, <12>3
                                                    <11> QED BY <11>1, <11>2, <1>2, <11>3 DEF Inv8
                                               <10>6 FALSE \* \E z \in g.stronglysees: Votes[i][z][a] = TRUE /\ Votes[j][z][a] = FALSE /\ Votes[j][z][a] = Votes[i][z][a]
                                                    BY <10>5, <10>7 \*<3>1, <1>2, Pslt1 DEF Inv8
                                               <10> QED BY <10>6
                                          <9> QED BY <9>2, <9>3
                                     <8> QED BY <8>1, <8>2 \*Votes[j][g][a] = FALSE =>  
                                <7>4 Votes[j][g][a] \in BOOLEAN \cup {"undecided"}
                                     BY <3>1, <1>2 DEF TypeOK, VotesType
                                <7>5 Votes[j][g][a] ="undecided" \/ Votes[j][g][a] = TRUE \/ Votes[j][g][a] = FALSE
                                     BY <7>4
                                <7> QED BY <7>5, <7>3, <7>2
                           <6> QED BY <6>1, <6>2
                      <5>2 CASE i # p \/ b # s
                           <6>1 CASE j = p /\ g = s
                                <7>1 ASSUME NEW l \in b.stronglysees, Votes[i][b][a] = TRUE
                                     PROVE Votes'[i][l][a] = Votes[i][l][a]
                                     <8>1 Votes'[i][b][a] = Votes[i][b][a]
                                          BY <5>2, <3>1, <2>3, <1>2, <4>1 DEF TypeOK, VotesType, VoteTn
                                     <8>2 Votes[i][b][a] = TRUE => \A z \in b.stronglysees: Votes[i][z][a] # "undecided"
                                          BY <3>1, unequalTF, <1>2 DEF Inv1
                                     <8>3 Votes[p][s][a] = "undecided"
                                          BY <2>3, <4>1 DEF VoteTn
                                     <8>4 ASSUME NEW z \in b.stronglysees, Votes[i][b][a] = TRUE
                                          PROVE z # s \/ p # i
                                          <9>1 z = s /\ p = i => FALSE
                                               <10>1 z = s /\ p = i => Votes[i][z][a] = "undecided"
                                                   BY <8>3
                                               <10>2 Votes[i][z][a] # "undecided"
                                                   BY <8>4, <8>2
                                               <10> QED BY <10>1, <10>2
                                          <9> QED BY <9>1
                                     <8>5 ASSUME NEW z \in b.stronglysees, Votes[i][b][a] = TRUE
                                          PROVE Votes'[i][z][a] = Votes[i][z][a]
                                          BY <8>4, <2>3, <3>1, <1>2, <8>5, <4>1, Pslt1 DEF VoteTn, TypeOK, VotesType
                                     <8> QED BY <8>5, <7>1
                                <7>3 Votes'[j][g][a] # FALSE
                                     <8>1 CASE g.frame = b.frame
                                          <9>1 Votes'[j][g][a] = FALSE => Cardinality({q \in ProcessSet: \E z \in g.stronglysees : z.source = q /\ Votes'[j][z][a] = FALSE}) > f
                                               <10>1 g.frame > a.frame+1 /\ (g.frame-a.frame)%c # 0
                                                     BY <8>1, <3>1
                                               <10> QED BY <10>1, <3>1, <1>2 DEF Inv4
                                          <9>2 Votes'[j][g][a] = FALSE => {q \in ProcessSet: \E z \in g.stronglysees : z.source = q /\ Votes'[j][z][a] = FALSE} \cap {d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = TRUE} # {}
                                               BY <9>1, <3>1, Pslt3
                                          <9>3 Votes'[j][g][a] = FALSE => \E q \in ProcessSet, z \in g.stronglysees, o \in b.stronglysees: o.source = q /\ z.source = q /\ Votes'[i][o][a] = TRUE /\ Votes'[j][z][a] = FALSE /\ z.frame = o.frame
                                               <10>1 Votes'[i][b][a] = Votes[i][b][a]
                                                     BY <5>2, <3>1, <2>3, <1>2 DEF VoteTn, TypeOK, VotesType 
                                               <10> QED BY <9>2, <7>1, <8>1, Pslt1
                                          <9>4 Votes'[j][g][a] = FALSE => \E q \in ProcessSet, z \in g.stronglysees, o \in b.stronglysees: o = z /\ Votes'[i][o][a] = TRUE /\ Votes'[j][z][a] = FALSE
                                               BY <2>3, <3>1, <9>3, Pslt1 DEF UniqueStronglyseenAs
                                          <9>5 Votes'[j][g][a] = FALSE => \E z \in g.stronglysees: Votes'[i][z][a] = TRUE /\ Votes'[j][z][a] = FALSE
                                               BY <9>4, <3>1, <1>2 DEF Inv8
                                          <9>7 ASSUME NEW z \in g.stronglysees, Votes'[i][z][a] = TRUE, Votes'[j][z][a] = FALSE
                                               PROVE Votes'[i][z][a] = Votes'[j][z][a]
                                               <10>1 z \in WitnessSet /\ a \in WitnessSet /\ i \in ProcessSet /\ j \in ProcessSet
                                                     BY <3>1, Pslt1
                                               <10>2 Votes'[i][z][a] \in BOOLEAN /\ Votes'[j][z][a] \in BOOLEAN
                                                     BY <9>7
                                               <10>3 z.frame >= a.frame+1
                                                     <11>1 z.frame = g.frame-1
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11>2 g.frame > a.frame+1
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11>3 g.frame \in Nat /\ z.frame \in Nat /\ a.frame \in Nat
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11> QED BY <11>1, <11>2, <11>3
                                               <10> QED BY <10>1, <10>2, <1>2, <10>3 DEF Inv8
                                          <9>6 Votes'[j][g][a] = FALSE => FALSE \* \E z \in g.stronglysees: Votes[i][z][a] = TRUE /\ Votes[j][z][a] = FALSE /\ Votes[j][z][a] = Votes[i][z][a]
                                               BY <9>5, <9>7 \*<3>1, <1>2, Pslt1 DEF Inv8
                                          <9> QED BY <9>6
                                     <8>2 CASE g.frame # b.frame
                                          <9>1 g.frame > b.frame
                                               BY <8>2, <3>1
                                          <9>2 ASSUME Votes'[j][g][a] = FALSE PROVE \E m \in WitnessSet: m \in WitnessDAG'[j][m.frame][m.source] /\ m.frame = b.frame /\  Votes'[j][m][a] = Votes'[j][g][a]\*\E m \in WitnessSet: m \in WitnessDAG[j][m.frame][m.source] /\ m.frame = b.frame /\ Votes[j][m][a] = FALSE
                                               <10>1 j \in ProcessSet /\ g \in WitnessSet /\ a \in WitnessSet /\ b.frame \in Frames
                                                     BY <3>1, Pslt1
                                               <10>2 g \in WitnessDAG'[j][g.frame][g.source] 
                                                     BY <3>1, <2>3 DEF VoteTn
                                               <10>3 Votes'[j][g][a] = FALSE => Votes'[j][g][a] # "undecided"
                                                     BY unequalTF
                                               <10>4 a.frame < b.frame /\ b.frame < g.frame
                                                     BY <3>1, <9>1, Pslt1
                                               <10>5 b.frame \in Frames
                                                     BY <3>1, Pslt1
                                               <10> QED BY <9>2, <10>1, <10>2, <10>3, <10>4, <10>5, <1>2 DEF Inv5
                                          <9>3 ASSUME NEW m \in WitnessSet, m \in WitnessDAG'[j][m.frame][m.source], m.frame = b.frame, Votes'[j][m][a] = FALSE
                                               PROVE FALSE
                                               <10>1  Cardinality({q \in ProcessSet: \E z \in m.stronglysees : z.source = q /\ Votes'[j][z][a] = FALSE}) > f
                                                    <11>1 (m.frame-a.frame)%c # 0
                                                          BY <3>1, <9>3
                                                    <11>2 Votes'[j][m][a] = FALSE
                                                          BY <9>3
                                                    <11> QED BY <11>1, <11>2, <3>1, <1>2, <9>3 DEF Inv4
                                               <10>2 {q \in ProcessSet: \E z \in m.stronglysees : z.source = q /\ Votes'[j][z][a] = FALSE} \cap {d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = TRUE} # {}
                                                    BY <10>1, <3>1, Pslt3
                                               <10>3 \E q \in ProcessSet, z \in m.stronglysees, o \in b.stronglysees: o.source = q /\ z.source = q /\ Votes'[i][o][a] = TRUE /\ Votes'[j][z][a] = FALSE /\ z.frame = o.frame
                                                    BY <10>2, <7>1, <9>3, Pslt1
                                               <10>4  \E q \in ProcessSet, z \in m.stronglysees, o \in b.stronglysees: o = z /\ Votes'[i][o][a] = TRUE /\ Votes'[j][z][a] = FALSE
                                                    BY <2>3, <3>1, <10>3, Pslt1, <9>3 DEF UniqueStronglyseenAs, VoteTn
                                               <10>5 \E z \in m.stronglysees: Votes'[i][z][a] = TRUE /\ Votes'[j][z][a] = FALSE
                                                    BY <10>4, <3>1, <1>2 DEF Inv8
                                               <10>7 ASSUME NEW z \in m.stronglysees, Votes'[i][z][a] = TRUE, Votes'[j][z][a] = FALSE
                                                    PROVE Votes'[i][z][a] = Votes'[j][z][a]
                                                    <11>1 z \in WitnessSet /\ a \in WitnessSet /\ i \in ProcessSet /\ j \in ProcessSet
                                                          BY <3>1, Pslt1
                                                    <11>2 Votes'[i][z][a] \in BOOLEAN /\ Votes'[j][z][a] \in BOOLEAN
                                                          BY <10>7
                                                    <11>3 z.frame >= a.frame+1
                                                         <12>1 z.frame = m.frame-1
                                                            BY <10>7, <3>1, <2>3, <9>3, Pslt1
                                                         <12>2 m.frame > a.frame+1
                                                            BY <10>7, <3>1, <2>3, Pslt1, <9>3
                                                         <12>3 m.frame \in Nat /\ z.frame \in Nat /\ a.frame \in Nat
                                                            BY <10>7, <3>1, <2>3, Pslt1, <9>3
                                                         <12> QED BY <12>1, <12>2, <12>3
                                                    <11> QED BY <11>1, <11>2, <1>2, <11>3 DEF Inv8
                                               <10>6 FALSE \* \E z \in g.stronglysees: Votes[i][z][a] = TRUE /\ Votes[j][z][a] = FALSE /\ Votes[j][z][a] = Votes[i][z][a]
                                                    BY <10>5, <10>7 \*<3>1, <1>2, Pslt1 DEF Inv8
                                               <10> QED BY <10>6
                                          <9> QED BY <9>2, <9>3
                                     <8> QED BY <8>1, <8>2 \*Votes[j][g][a] = FALSE =>  
                                <7>4 Votes'[j][g][a] \in BOOLEAN \cup {"undecided"}
                                     BY <3>1, <1>2 DEF TypeOK, VotesType
                                <7>5 Votes'[j][g][a] ="undecided" \/ Votes'[j][g][a] = TRUE \/ Votes'[j][g][a] = FALSE
                                     BY <7>4
                                <7> QED BY <7>5, <7>3
                           <6>2 CASE j # p \/ g # s
                                <7>1 Votes'[i][b][a] = Votes[i][b][a] /\ Votes'[j][g][a] = Votes[j][g][a]
                                     BY <6>2, <5>2, <3>1, <2>3, <1>2, <4>1 DEF TypeOK, VotesType, VoteTn
                                <7>2 Votes[i][b][a] = TRUE => \A z \in b.stronglysees: Votes[i][z][a] # "undecided"
                                     BY <3>1, unequalTF, <1>2 DEF Inv1
                                <7>3 Votes[p][s][a] = "undecided"
                                     BY <2>3, <4>1 DEF VoteTn
                                <7>4 ASSUME NEW z \in b.stronglysees, Votes[i][b][a] = TRUE
                                     PROVE z # s \/ p # i
                                     <8>1 z = s /\ p = i => FALSE
                                         <9>1 z = s /\ p = i => Votes[i][z][a] = "undecided"
                                              BY <7>3
                                         <9>2 Votes[i][z][a] # "undecided"
                                              BY <7>4, <7>2
                                         <9> QED BY <9>1, <9>2
                                     <8> QED BY <8>1
                                <7>5 ASSUME NEW z \in b.stronglysees, Votes[i][b][a] = TRUE
                                     PROVE Votes[i][z][a] = Votes'[i][z][a]
                                     BY <7>4, <2>3, <3>1, <1>2, <7>5, <4>1, Pslt1 DEF VoteTn, TypeOK, VotesType
                                <7>6 Votes[i][b][a] = TRUE => Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = TRUE}) = Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes[i][z][a] = TRUE})
                                     BY <7>5
                                <7> QED BY <7>6, <7>1, <3>1, <1>2 DEF Inv15
                           <6> QED BY <6>1, <6>2
                      <5> QED BY <5>1, <5>2
                 <4>2 CASE e # a
                      <5>1 ASSUME NEW z \in WitnessSet
                           PROVE Votes'[i][z][a] = Votes[i][z][a] /\ Votes'[j][z][a] = Votes[j][z][a]
                           BY <4>2, <3>1, <2>3, <1>2 DEF VoteTn, TypeOK, VotesType
                      <5>2 2*f < Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes[i][z][a] = TRUE})
                           BY <5>1, <3>1, subsetCard, intCard, natfAs, Pslt1
                      <5> QED BY <5>1, <3>1, <1>2, <5>2 DEF Inv15
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1, <2>3 DEF Inv15,  VoteTn
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv15'
            BY <1>2, <2>4 DEF Inv15, DecideFrameTn
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv15'
            BY <2>5, <1>2 DEF vars, Inv15
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness, Inv9proof, Inv4proof, Inv8proof, Inv5proof, Inv1proof DEF Spec

Inv16 == \A p \in ProcessSet, q \in ProcessSet, e \in WitnessSet, s \in WitnessSet, g \in WitnessSet: 
       (/\ e \in WitnessDAG[p][e.frame][e.source] 
        /\ s \in WitnessDAG[p][s.frame][s.source]
        /\ s.frame > e.frame+1
        /\ (s.frame-e.frame)%c # 0
        /\ Cardinality({d \in ProcessSet: \E a \in s.stronglysees: a.source = d /\ Votes[p][a][e]=FALSE}) > 2*f
        /\ g \in WitnessDAG[q][g.frame][g.source]
        /\ g.frame >= s.frame) => (Votes[p][s][e] = FALSE => Votes[q][g][e] = "undecided" \/ Votes[q][g][e] = FALSE)


THEOREM Inv16proof == Spec => []Inv16
  <1>1 Init => Inv16
       BY DEF Init, Inv16, InitWitnessDAG, InitVotes, InitFame, InitDecidedFrames, InitFamousWitnesses
  <1>2 ASSUME [Next]_vars, TypeOK, TypeOK', Inv16, Inv9, Inv9', Inv3, Inv3', Inv8, Inv8', Inv5, Inv5', Inv1, Inv1'
       PROVE Inv16'  
       <2>1 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, AddWitnessTn(p, e)
            PROVE Inv16'
            <3>1 ASSUME NEW i \in ProcessSet, NEW j \in ProcessSet, NEW a \in WitnessSet, NEW b \in WitnessSet, NEW g \in WitnessSet, 
       (/\ a \in WitnessDAG'[i][a.frame][a.source] 
        /\ b \in WitnessDAG'[i][b.frame][b.source]
        /\ b.frame > a.frame+1
        /\ (b.frame-a.frame)%c # 0
        /\ Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a]=FALSE}) > 2*f
        /\ g \in WitnessDAG'[j][g.frame][g.source]
        /\ g.frame >= b.frame)
                 PROVE Votes'[i][b][a] = FALSE => Votes'[j][g][a] = "undecided" \/ Votes'[j][g][a] = FALSE
                 <4>1 CASE i = p
                      <5>1 CASE e = b
                           BY <5>1, <4>1, <3>1, <2>1, unequalTF DEF AddWitnessTn
                      <5>2 CASE e = a
                           BY <5>2, <4>1, <3>1, <2>1, unequalTF DEF AddWitnessTn
                      <5>3 CASE e # b /\ e # a
                           <6>1 CASE j = p /\ e = g
                                BY <6>1, <3>1, <2>1 DEF AddWitnessTn
                           <6>2 CASE j # p \/ e # g
                                <7>1 a \in WitnessDAG[i][a.frame][a.source]
                                     <8>1 CASE a.frame = e.frame /\ a.source = e.source
                                          BY <8>1, <5>3, <1>2, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType
                                     <8>2 CASE a.frame # e.frame \/ a.source # e.source
                                          BY <8>2, <3>1, <2>1 DEF AddWitnessTn
                                     <8> QED BY <8>1, <8>2
                                <7>2 b \in WitnessDAG[i][b.frame][b.source]
                                     <8>1 CASE b.frame = e.frame /\ b.source = e.source
                                          BY <8>1, <5>3, <1>2, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType
                                     <8>2 CASE b.frame # e.frame \/ b.source # e.source
                                          BY <8>2, <3>1, <2>1 DEF AddWitnessTn
                                     <8> QED BY <8>1, <8>2
                                <7>3 g \in WitnessDAG[j][g.frame][g.source]
                                     <8>1 CASE g.frame = e.frame /\ g.source = e.source
                                          BY <8>1, <6>2, <1>2, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType
                                     <8>2 CASE g.frame # e.frame \/ g.source # e.source
                                          BY <8>2, <3>1, <2>1 DEF AddWitnessTn
                                     <8> QED BY <8>1, <8>2
                                <7>4 \A z \in b.stronglysees : z \in WitnessDAG[i][z.frame][z.source]
                                     BY <1>2, <7>2, <3>1 DEF Inv9
                                <7>5 2*f < Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes[i][z][a]= FALSE})
                                     BY <3>1, <7>4, subsetCard, natfAs, intCard, <2>1 DEF AddWitnessTn
                                <7>7 b.frame > a.frame+1 /\ (b.frame-a.frame)%c # 0 /\ g.frame >= b.frame
                                     BY <3>1
                                <7>6 Votes[i][b][a] = FALSE => Votes[j][g][a] = "undecided" \/ Votes[j][g][a] = FALSE
                                     BY <7>1, <7>2, <7>3, <7>5, <7>7, <1>2 DEF Inv16
                                <7> QED BY <7>6, <7>1, <7>2, <7>3, <7>5, <3>1, <2>1, <1>2 DEF Inv15, AddWitnessTn
                           <6> QED BY <6>1, <6>2
                      <5> QED BY <5>1, <5>2, <5>3
                 <4>2 CASE i # p
                      <5>1 CASE j = p /\ e = g
                           BY <5>1, <3>1, <2>1 DEF AddWitnessTn
                      <5>2 CASE j # p \/ e # g
                           <6>1 a \in WitnessDAG[i][a.frame][a.source]
                                BY <4>2, <2>1 , <3>1 DEF AddWitnessTn
                           <6>2 b \in WitnessDAG[i][b.frame][b.source]
                                BY <4>2, <2>1 , <3>1 DEF AddWitnessTn
                           <6>3 g \in WitnessDAG[j][g.frame][g.source]
                                <7>1 CASE g.frame = e.frame /\ g.source = e.source
                                          BY <7>1, <5>2, <1>2, <3>1, <2>1 DEF AddWitnessTn, TypeOK, WitnessDAGType
                                <7>2 CASE g.frame # e.frame \/ g.source # e.source
                                          BY <7>2, <3>1, <2>1 DEF AddWitnessTn
                                <7> QED BY <7>1, <7>2
                           <6>4 \A z \in b.stronglysees : z \in WitnessDAG[i][z.frame][z.source]
                                 BY <1>2, <6>2, <3>1 DEF Inv9
                           <6>5 2*f < Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes[i][z][a]=FALSE})
                                BY <3>1, <6>4, subsetCard, natfAs, intCard, <2>1 DEF AddWitnessTn
                           <6>6 b.frame > a.frame+1 /\ (b.frame-a.frame)%c # 0 /\ g.frame >= b.frame
                                BY <3>1
                           <6> QED BY <6>1, <6>2, <6>3, <6>5, <2>1, <1>2, <6>6 DEF Inv16, AddWitnessTn     
                      <5> QED BY <5>1, <5>2
                 <4> QED BY <4>1, <4>2, <3>1, <2>1 DEF AddWitnessTn
            <3> QED BY <3>1 DEF Inv16
       <2>2 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, DecideFameTn(p, s, e)
            PROVE Inv16'
            BY <1>2, <2>2 DEF Inv16, DecideFameTn
       <2>3 ASSUME NEW p \in ProcessSet, NEW e \in WitnessSet, NEW s \in WitnessSet, VoteTn(p, s, e), UniqueStronglyseenAs, UniqueStronglyseenAs'
            PROVE Inv16' 
            <3>1 ASSUME NEW i \in ProcessSet, NEW j \in ProcessSet, NEW a \in WitnessSet, NEW b \in WitnessSet, NEW g \in WitnessSet, b.frame > a.frame+1, (b.frame-a.frame)%c # 0,
                       a \in WitnessDAG[i][a.frame][a.source], b \in WitnessDAG[i][b.frame][b.source], g \in WitnessDAG[j][g.frame][g.source], g.frame >= b.frame,
                       Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = FALSE}) > 2*f 
                 PROVE Votes'[i][b][a] = FALSE => Votes'[j][g][a] = "undecided" \/ Votes'[j][g][a] = FALSE
                 <4>1 CASE e = a 
                      <5>1 CASE i = p /\ b = s 
                           <6>1 CASE j = p /\ g = s
                                BY <6>1, <5>1, <3>1
                           <6>2 CASE j # p \/ g # s  
                                <7>1 ASSUME NEW z \in b.stronglysees
                                     PROVE Votes'[i][z][a] = Votes[i][z][a]
                                     BY <7>1, <5>1, Pslt1, <1>2, <3>1, <2>3 DEF VoteTn, TypeOK, VotesType
                                <7>2 Votes'[j][g][a] = Votes[j][g][a]
                                     BY <6>2, <1>2, <3>1, <2>3 DEF VoteTn, TypeOK, VotesType
                                <7>3 Votes[j][g][a] # TRUE 
                                     <8>1 CASE g.frame = b.frame 
                                          <9>1 Votes[j][g][a] = TRUE => Cardinality({q \in ProcessSet: \E z \in g.stronglysees : z.source = q /\ Votes[j][z][a] = TRUE}) > f 
                                              <10>1 g.frame > a.frame+1 /\ (g.frame-a.frame)%c # 0
                                                     BY <8>1, <3>1
                                              <10>3 g \in WitnessSet /\ a \in WitnessSet /\ j \in ProcessSet
                                                    BY <3>1
                                              <10>2 ASSUME  Votes[j][g][a] = TRUE PROVE Cardinality({q \in ProcessSet: \E z \in g.stronglysees : z.source = q /\ Votes[j][z][a] = TRUE}) > f 
                                                    BY <10>1, <10>2, 10>3, <1>2 DEF Inv3
                                              <10> QED BY <10>2
                                          <9>2 Votes[j][g][a] = TRUE => {q \in ProcessSet: \E z \in g.stronglysees : z.source = q /\ Votes[j][z][a] = TRUE} \cap {d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = FALSE} # {}
                                               BY <9>1, <3>1, Pslt3
                                          <9>3 Votes[j][g][a] = TRUE => \E q \in ProcessSet, z \in g.stronglysees, o \in b.stronglysees: o.source = q /\ z.source = q /\ Votes[i][o][a] = FALSE /\ Votes[j][z][a] = TRUE /\ z.frame = o.frame
                                               BY <9>2, <7>1, <8>1, Pslt1
                                          <9>4 Votes[j][g][a] = TRUE => \E q \in ProcessSet, z \in g.stronglysees, o \in b.stronglysees: o = z /\ Votes[i][o][a] = FALSE /\ Votes[j][z][a] = TRUE
                                               BY <2>3, <3>1, <9>3, Pslt1 DEF UniqueStronglyseenAs
                                          <9>5 Votes[j][g][a] = TRUE => \E z \in g.stronglysees: Votes[i][z][a] = FALSE /\ Votes[j][z][a] = TRUE
                                               BY <9>4, <3>1, <1>2 DEF Inv8
                                          <9>7 ASSUME NEW z \in g.stronglysees, Votes[i][z][a] = FALSE, Votes[j][z][a] = TRUE
                                               PROVE Votes[i][z][a] = Votes[j][z][a]
                                               <10>1 z \in WitnessSet /\ a \in WitnessSet /\ i \in ProcessSet /\ j \in ProcessSet
                                                     BY <3>1, Pslt1
                                               <10>2 Votes[i][z][a] \in BOOLEAN /\ Votes[j][z][a] \in BOOLEAN
                                                     BY <9>7
                                               <10>3 z.frame >= a.frame+1
                                                     <11>1 z.frame = g.frame-1
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11>2 g.frame > a.frame+1
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11>3 g.frame \in Nat /\ z.frame \in Nat /\ a.frame \in Nat
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11> QED BY <11>1, <11>2, <11>3
                                               <10> QED BY <10>1, <10>2, <1>2, <10>3 DEF Inv8
                                          <9>6 Votes[j][g][a] = TRUE => FALSE \* \E z \in g.stronglysees: Votes[i][z][a] = TRUE /\ Votes[j][z][a] = FALSE /\ Votes[j][z][a] = Votes[i][z][a]
                                               BY <9>5, <9>7 \*<3>1, <1>2, Pslt1 DEF Inv8
                                          <9> QED BY <9>6
                                     <8>2 CASE g.frame # b.frame
                                          <9>1 g.frame > b.frame
                                               BY <8>2, <3>1
                                          <9>2 ASSUME Votes[j][g][a] = TRUE PROVE \E m \in WitnessSet: m \in WitnessDAG[j][m.frame][m.source] /\ m.frame = b.frame /\  Votes[j][m][a] = Votes[j][g][a]\*\E m \in WitnessSet: m \in WitnessDAG[j][m.frame][m.source] /\ m.frame = b.frame /\ Votes[j][m][a] = FALSE
                                               <10>1 j \in ProcessSet /\ g \in WitnessSet /\ a \in WitnessSet /\ b.frame \in Frames
                                                     BY <3>1, Pslt1
                                               <10>2 g \in WitnessDAG[j][g.frame][g.source] 
                                                     BY <3>1, <2>1 DEF VoteTn
                                               <10>3 Votes[j][g][a] # "undecided"
                                                     BY <9>2, unequalTF
                                               <10>4 a.frame < b.frame /\ b.frame < g.frame
                                                     BY <3>1, <9>1, Pslt1
                                               <10>5 b.frame \in Frames
                                                     BY <3>1, Pslt1
                                               <10> QED BY <9>2, <10>1, <10>2, <10>3, <10>4, <10>5, <1>2 DEF Inv5
                                          <9>3 ASSUME NEW m \in WitnessSet, m \in WitnessDAG[j][m.frame][m.source], m.frame = b.frame, Votes[j][m][a] = TRUE
                                               PROVE FALSE
                                               <10>1  Cardinality({q \in ProcessSet: \E z \in m.stronglysees : z.source = q /\ Votes[j][z][a] = TRUE}) > f
                                                    <11>1 (m.frame-a.frame)%c # 0
                                                          BY <3>1, <9>3
                                                    <11>2 Votes[j][m][a] = TRUE
                                                          BY <9>3
                                                    <11> QED BY <11>1, <11>2, <3>1, <1>2, <9>3 DEF Inv3
                                               <10>2 {q \in ProcessSet: \E z \in m.stronglysees : z.source = q /\ Votes[j][z][a] = TRUE} \cap {d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = FALSE} # {}
                                                    BY <10>1, <3>1, Pslt3
                                               <10>3 \E q \in ProcessSet, z \in m.stronglysees, o \in b.stronglysees: o.source = q /\ z.source = q /\ Votes[i][o][a] = FALSE /\ Votes[j][z][a] = TRUE /\ z.frame = o.frame
                                                    BY <10>2, <7>1, <9>3, Pslt1
                                               <10>4  \E q \in ProcessSet, z \in m.stronglysees, o \in b.stronglysees: o = z /\ Votes[i][o][a] = FALSE /\ Votes[j][z][a] = TRUE
                                                    BY <2>3, <3>1, <10>3, Pslt1, <9>3 DEF UniqueStronglyseenAs
                                               <10>5 \E z \in m.stronglysees: Votes[i][z][a] = FALSE /\ Votes[j][z][a] = TRUE
                                                    BY <10>4, <3>1, <1>2 DEF Inv8
                                               <10>7 ASSUME NEW z \in m.stronglysees, Votes[i][z][a] = FALSE, Votes[j][z][a] = TRUE
                                                    PROVE Votes[i][z][a] = Votes[j][z][a]
                                                    <11>1 z \in WitnessSet /\ a \in WitnessSet /\ i \in ProcessSet /\ j \in ProcessSet
                                                          BY <3>1, Pslt1
                                                    <11>2 Votes[i][z][a] \in BOOLEAN /\ Votes[j][z][a] \in BOOLEAN
                                                          BY <10>7
                                                    <11>3 z.frame >= a.frame+1
                                                         <12>1 z.frame = m.frame-1
                                                            BY <10>7, <3>1, <2>3, <9>3, Pslt1
                                                         <12>2 m.frame > a.frame+1
                                                            BY <10>7, <3>1, <2>3, Pslt1, <9>3
                                                         <12>3 m.frame \in Nat /\ z.frame \in Nat /\ a.frame \in Nat
                                                            BY <10>7, <3>1, <2>3, Pslt1, <9>3
                                                         <12> QED BY <12>1, <12>2, <12>3
                                                    <11> QED BY <11>1, <11>2, <1>2, <11>3 DEF Inv8
                                               <10>6 FALSE \* \E z \in g.stronglysees: Votes[i][z][a] = TRUE /\ Votes[j][z][a] = FALSE /\ Votes[j][z][a] = Votes[i][z][a]
                                                    BY <10>5, <10>7 \*<3>1, <1>2, Pslt1 DEF Inv8
                                               <10> QED BY <10>6
                                          <9> QED BY <9>2, <9>3
                                     <8> QED BY <8>1, <8>2 \*Votes[j][g][a] = FALSE =>  
                                <7>4 Votes[j][g][a] \in BOOLEAN \cup {"undecided"}
                                     BY <3>1, <1>2 DEF TypeOK, VotesType
                                <7>5 Votes[j][g][a] ="undecided" \/ Votes[j][g][a] = TRUE \/ Votes[j][g][a] = FALSE
                                     BY <7>4
                                <7> QED BY <7>5, <7>3, <7>2
                           <6> QED BY <6>1, <6>2
                      <5>2 CASE i # p \/ b # s
                           <6>1 CASE j = p /\ g = s
                                <7>1 ASSUME NEW l \in b.stronglysees, Votes[i][b][a] = FALSE 
                                     PROVE Votes'[i][l][a] = Votes[i][l][a]
                                     <8>1 Votes'[i][b][a] = Votes[i][b][a]
                                          BY <5>2, <3>1, <2>3, <1>2, <4>1 DEF TypeOK, VotesType, VoteTn
                                     <8>2 Votes[i][b][a] = FALSE => \A z \in b.stronglysees: Votes[i][z][a] # "undecided"
                                          BY <3>1, unequalTF, <1>2 DEF Inv1
                                     <8>3 Votes[p][s][a] = "undecided"
                                          BY <2>3, <4>1 DEF VoteTn
                                     <8>4 ASSUME NEW z \in b.stronglysees, Votes[i][b][a] = FALSE
                                          PROVE z # s \/ p # i
                                          <9>1 z = s /\ p = i => FALSE
                                               <10>1 z = s /\ p = i => Votes[i][z][a] = "undecided"
                                                   BY <8>3
                                               <10>2 Votes[i][z][a] # "undecided"
                                                   BY <8>4, <8>2
                                               <10> QED BY <10>1, <10>2
                                          <9> QED BY <9>1
                                     <8>5 ASSUME NEW z \in b.stronglysees, Votes[i][b][a] = FALSE
                                          PROVE Votes'[i][z][a] = Votes[i][z][a]
                                          BY <8>4, <2>3, <3>1, <1>2, <8>5, <4>1, Pslt1 DEF VoteTn, TypeOK, VotesType
                                     <8> QED BY <8>5, <7>1
                                <7>3 Votes'[j][g][a] # TRUE
                                     <8>1 CASE g.frame = b.frame
                                          <9>1 Votes'[j][g][a] = TRUE => Cardinality({q \in ProcessSet: \E z \in g.stronglysees : z.source = q /\ Votes'[j][z][a] = TRUE}) > f
                                               <10>1 g.frame > a.frame+1 /\ (g.frame-a.frame)%c # 0
                                                     BY <8>1, <3>1
                                               <10> QED BY <10>1, <3>1, <1>2 DEF Inv3
                                          <9>2 Votes'[j][g][a] = TRUE => {q \in ProcessSet: \E z \in g.stronglysees : z.source = q /\ Votes'[j][z][a] = TRUE} \cap {d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = FALSE} # {}
                                               BY <9>1, <3>1, Pslt3
                                          <9>3 Votes'[j][g][a] = TRUE => \E q \in ProcessSet, z \in g.stronglysees, o \in b.stronglysees: o.source = q /\ z.source = q /\ Votes'[i][o][a] = FALSE /\ Votes'[j][z][a] = TRUE /\ z.frame = o.frame
                                               <10>1 Votes'[i][b][a] = Votes[i][b][a]
                                                     BY <5>2, <3>1, <2>3, <1>2 DEF VoteTn, TypeOK, VotesType 
                                               <10> QED BY <9>2, <7>1, <8>1, Pslt1
                                          <9>4 Votes'[j][g][a] = TRUE => \E q \in ProcessSet, z \in g.stronglysees, o \in b.stronglysees: o = z /\ Votes'[i][o][a] = FALSE /\ Votes'[j][z][a] = TRUE
                                               BY <2>3, <3>1, <9>3, Pslt1 DEF UniqueStronglyseenAs
                                          <9>5 Votes'[j][g][a] = TRUE => \E z \in g.stronglysees: Votes'[i][z][a] = FALSE /\ Votes'[j][z][a] = TRUE
                                               BY <9>4, <3>1, <1>2 DEF Inv8
                                          <9>7 ASSUME NEW z \in g.stronglysees, Votes'[i][z][a] = FALSE, Votes'[j][z][a] = TRUE
                                               PROVE Votes'[i][z][a] = Votes'[j][z][a]
                                               <10>1 z \in WitnessSet /\ a \in WitnessSet /\ i \in ProcessSet /\ j \in ProcessSet
                                                     BY <3>1, Pslt1
                                               <10>2 Votes'[i][z][a] \in BOOLEAN /\ Votes'[j][z][a] \in BOOLEAN
                                                     BY <9>7
                                               <10>3 z.frame >= a.frame+1
                                                     <11>1 z.frame = g.frame-1
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11>2 g.frame > a.frame+1
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11>3 g.frame \in Nat /\ z.frame \in Nat /\ a.frame \in Nat
                                                           BY <9>7, <3>1, <2>3, Pslt1
                                                     <11> QED BY <11>1, <11>2, <11>3
                                               <10> QED BY <10>1, <10>2, <1>2, <10>3 DEF Inv8
                                          <9>6 Votes'[j][g][a] = TRUE => FALSE \* \E z \in g.stronglysees: Votes[i][z][a] = TRUE /\ Votes[j][z][a] = FALSE /\ Votes[j][z][a] = Votes[i][z][a]
                                               BY <9>5, <9>7 \*<3>1, <1>2, Pslt1 DEF Inv8
                                          <9> QED BY <9>6
                                     <8>2 CASE g.frame # b.frame
                                          <9>1 g.frame > b.frame
                                               BY <8>2, <3>1
                                          <9>2 ASSUME Votes'[j][g][a] = TRUE PROVE \E m \in WitnessSet: m \in WitnessDAG'[j][m.frame][m.source] /\ m.frame = b.frame /\  Votes'[j][m][a] = Votes'[j][g][a]\*\E m \in WitnessSet: m \in WitnessDAG[j][m.frame][m.source] /\ m.frame = b.frame /\ Votes[j][m][a] = FALSE
                                               <10>1 j \in ProcessSet /\ g \in WitnessSet /\ a \in WitnessSet /\ b.frame \in Frames
                                                     BY <3>1, Pslt1
                                               <10>2 g \in WitnessDAG'[j][g.frame][g.source] 
                                                     BY <3>1, <2>3 DEF VoteTn
                                               <10>3 Votes'[j][g][a] = TRUE => Votes'[j][g][a] # "undecided"
                                                     BY unequalTF
                                               <10>4 a.frame < b.frame /\ b.frame < g.frame
                                                     BY <3>1, <9>1, Pslt1
                                               <10>5 b.frame \in Frames
                                                     BY <3>1, Pslt1
                                               <10> QED BY <9>2, <10>1, <10>2, <10>3, <10>4, <10>5, <1>2 DEF Inv5
                                          <9>3 ASSUME NEW m \in WitnessSet, m \in WitnessDAG'[j][m.frame][m.source], m.frame = b.frame, Votes'[j][m][a] = TRUE
                                               PROVE FALSE
                                               <10>1  Cardinality({q \in ProcessSet: \E z \in m.stronglysees : z.source = q /\ Votes'[j][z][a] = TRUE}) > f
                                                    <11>1 (m.frame-a.frame)%c # 0
                                                          BY <3>1, <9>3
                                                    <11>2 Votes'[j][m][a] = TRUE
                                                          BY <9>3
                                                    <11> QED BY <11>1, <11>2, <3>1, <1>2, <9>3 DEF Inv3
                                               <10>2 {q \in ProcessSet: \E z \in m.stronglysees : z.source = q /\ Votes'[j][z][a] = TRUE} \cap {d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = FALSE} # {}
                                                    BY <10>1, <3>1, Pslt3
                                               <10>3 \E q \in ProcessSet, z \in m.stronglysees, o \in b.stronglysees: o.source = q /\ z.source = q /\ Votes'[i][o][a] = FALSE /\ Votes'[j][z][a] = TRUE /\ z.frame = o.frame
                                                    BY <10>2, <7>1, <9>3, Pslt1
                                               <10>4  \E q \in ProcessSet, z \in m.stronglysees, o \in b.stronglysees: o = z /\ Votes'[i][o][a] = FALSE /\ Votes'[j][z][a] = TRUE
                                                    BY <2>3, <3>1, <10>3, Pslt1, <9>3 DEF UniqueStronglyseenAs, VoteTn
                                               <10>5 \E z \in m.stronglysees: Votes'[i][z][a] = FALSE /\ Votes'[j][z][a] = TRUE
                                                    BY <10>4, <3>1, <1>2 DEF Inv8
                                               <10>7 ASSUME NEW z \in m.stronglysees, Votes'[i][z][a] = FALSE, Votes'[j][z][a] = TRUE
                                                    PROVE Votes'[i][z][a] = Votes'[j][z][a]
                                                    <11>1 z \in WitnessSet /\ a \in WitnessSet /\ i \in ProcessSet /\ j \in ProcessSet
                                                          BY <3>1, Pslt1
                                                    <11>2 Votes'[i][z][a] \in BOOLEAN /\ Votes'[j][z][a] \in BOOLEAN
                                                          BY <10>7
                                                    <11>3 z.frame >= a.frame+1
                                                         <12>1 z.frame = m.frame-1
                                                            BY <10>7, <3>1, <2>3, <9>3, Pslt1
                                                         <12>2 m.frame > a.frame+1
                                                            BY <10>7, <3>1, <2>3, Pslt1, <9>3
                                                         <12>3 m.frame \in Nat /\ z.frame \in Nat /\ a.frame \in Nat
                                                            BY <10>7, <3>1, <2>3, Pslt1, <9>3
                                                         <12> QED BY <12>1, <12>2, <12>3
                                                    <11> QED BY <11>1, <11>2, <1>2, <11>3 DEF Inv8
                                               <10>6 FALSE \* \E z \in g.stronglysees: Votes[i][z][a] = TRUE /\ Votes[j][z][a] = FALSE /\ Votes[j][z][a] = Votes[i][z][a]
                                                    BY <10>5, <10>7 \*<3>1, <1>2, Pslt1 DEF Inv8
                                               <10> QED BY <10>6
                                          <9> QED BY <9>2, <9>3
                                     <8> QED BY <8>1, <8>2 \*Votes[j][g][a] = FALSE =>  
                                <7>4 Votes'[j][g][a] \in BOOLEAN \cup {"undecided"}
                                     BY <3>1, <1>2 DEF TypeOK, VotesType
                                <7>5 Votes'[j][g][a] ="undecided" \/ Votes'[j][g][a] = FALSE \/ Votes'[j][g][a] = TRUE
                                     BY <7>4
                                <7> QED BY <7>5, <7>3
                           <6>2 CASE j # p \/ g # s
                                <7>1 Votes'[i][b][a] = Votes[i][b][a] /\ Votes'[j][g][a] = Votes[j][g][a]
                                     BY <6>2, <5>2, <3>1, <2>3, <1>2, <4>1 DEF TypeOK, VotesType, VoteTn
                                <7>2 Votes[i][b][a] = FALSE => \A z \in b.stronglysees: Votes[i][z][a] # "undecided"
                                     BY <3>1, unequalTF, <1>2 DEF Inv1
                                <7>3 Votes[p][s][a] = "undecided"
                                     BY <2>3, <4>1 DEF VoteTn
                                <7>4 ASSUME NEW z \in b.stronglysees, Votes[i][b][a] = FALSE
                                     PROVE z # s \/ p # i
                                     <8>1 z = s /\ p = i => FALSE
                                         <9>1 z = s /\ p = i => Votes[i][z][a] = "undecided"
                                              BY <7>3
                                         <9>2 Votes[i][z][a] # "undecided"
                                              BY <7>4, <7>2
                                         <9> QED BY <9>1, <9>2
                                     <8> QED BY <8>1
                                <7>5 ASSUME NEW z \in b.stronglysees, Votes[i][b][a] = FALSE
                                     PROVE Votes[i][z][a] = Votes'[i][z][a]
                                     BY <7>4, <2>3, <3>1, <1>2, <7>5, <4>1, Pslt1 DEF VoteTn, TypeOK, VotesType
                                <7>6 Votes[i][b][a] = FALSE => Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes'[i][z][a] = FALSE}) = Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes[i][z][a] = FALSE})
                                     BY <7>5
                                <7> QED BY <7>6, <7>1, <3>1, <1>2 DEF Inv16
                           <6> QED BY <6>1, <6>2
                      <5> QED BY <5>1, <5>2
                 <4>2 CASE e # a
                      <5>1 ASSUME NEW z \in WitnessSet
                           PROVE Votes'[i][z][a] = Votes[i][z][a] /\ Votes'[j][z][a] = Votes[j][z][a]
                           BY <4>2, <3>1, <2>3, <1>2 DEF VoteTn, TypeOK, VotesType
                      <5>2 2*f < Cardinality({d \in ProcessSet: \E z \in b.stronglysees: z.source = d /\ Votes[i][z][a] = FALSE})
                           BY <5>1, <3>1, subsetCard, intCard, natfAs, Pslt1
                      <5>3 Votes'[i][b][a] = Votes[i][b][a] /\ Votes'[j][g][a] = Votes[j][g][a]
                           BY <3>1, <5>1
                      <5> QED BY <3>1, <1>2, <5>2, <5>3 DEF Inv16
                 <4> QED BY <4>1, <4>2
            <3> QED BY <3>1, <2>3 DEF Inv16,  VoteTn
       <2>4 ASSUME NEW p \in ProcessSet, NEW x \in Frames, DecideFrameTn(p, x)
            PROVE Inv16'
            BY <1>2, <2>4 DEF Inv16, DecideFrameTn
       <2>5 ASSUME UNCHANGED vars
            PROVE Inv16'
            BY <2>5, <1>2 DEF vars, Inv16
       <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <1>2 DEF Next
  <1> QED BY <1>1, <1>2, PTL, TypeOKcorrectness, Inv9proof, Inv3proof, Inv8proof, Inv5proof, Inv1proof DEF Spec

FameSafetyInv17 == \A p \in ProcessSet, q \in ProcessSet, e \in WitnessSet:
                      (/\ e \in WitnessDAG[p][e.frame][e.source] 
                       /\ e \in WitnessDAG[q][e.frame][e.source]
                       /\ Fame[p][e] # "undecided" 
                       /\ Fame[q][e] # "undecided") => Fame[p][e] = Fame[q][e]

THEOREM FameSafetyInv17proof == Spec => []FameSafetyInv17
  <1>1 ASSUME Inv15, Inv16, Inv10, Inv11, TypeOK
       PROVE FameSafetyInv17
       <2>1 ASSUME NEW p \in ProcessSet, NEW q \in ProcessSet, NEW e \in WitnessSet, Fame[p][e] # "undecided", Fame[q][e] # "undecided", e \in WitnessDAG[p][e.frame][e.source], e \in WitnessDAG[q][e.frame][e.source]
            PROVE Fame[p][e] = Fame[q][e]
            <3>1 CASE Fame[p][e] = Fame[q][e]
                 BY <3>1
            <3>2 CASE Fame[p][e] # Fame[q][e]
                 <4>1 CASE Fame[p][e] = TRUE /\ Fame[q][e] = FALSE
                      <5>1 \E s \in WitnessSet: s.frame > e.frame+1 /\ (s.frame-e.frame)%c # 0 /\ Cardinality({d \in ProcessSet: \E a \in s.stronglysees: a.source = d /\ Votes[p][a][e]=TRUE}) > 2*f /\ s \in WitnessDAG[p][s.frame][s.source] /\ Votes[p][s][e] = TRUE
                           BY <2>1, <4>1, <1>1 DEF Inv10 
                      <5>2 \E s \in WitnessSet: s.frame > e.frame+1 /\ (s.frame-e.frame)%c # 0 /\ Cardinality({d \in ProcessSet: \E a \in s.stronglysees: a.source = d /\ Votes[q][a][e]=FALSE}) > 2*f /\ s \in WitnessDAG[q][s.frame][s.source] /\ Votes[q][s][e] = FALSE
                           BY <2>1, <4>1, <1>1 DEF Inv11
                      <5>3 ASSUME NEW s \in WitnessSet, NEW z \in WitnessSet, s.frame > e.frame+1, (s.frame-e.frame)%c # 0, Cardinality({d \in ProcessSet: \E a \in s.stronglysees: a.source = d /\ Votes[p][a][e]=TRUE}) > 2*f, s \in WitnessDAG[p][s.frame][s.source], Votes[p][s][e] = TRUE,
                                  z.frame > e.frame+1, (z.frame-e.frame)%c # 0, Cardinality({d \in ProcessSet: \E a \in z.stronglysees: a.source = d /\ Votes[q][a][e]=FALSE}) > 2*f, z \in WitnessDAG[q][z.frame][z.source], Votes[q][z][e] = FALSE
                           PROVE FALSE
                           <6>1 CASE s.frame >= z.frame
                                <7>1 Votes[p][s][e] = "undecided" \/ Votes[p][s][e] = FALSE
                                     BY <6>1, <5>3, <2>1, <1>1 DEF Inv16
                                <7> QED BY  <7>1, <5>3, unequalTF
                           <6>2 CASE z.frame >= s.frame
                                <7>1 Votes[q][z][e] = "undecided" \/ Votes[q][z][e] = TRUE
                                     BY <6>2, <5>3, <2>1, <1>1 DEF Inv15
                                <7> QED BY  <7>1, <5>3, unequalTF
                           <6>3 s.frame \in Nat /\ z.frame \in Nat
                                BY <5>3, Pslt1
                           <6> QED BY <6>1, <6>2, <6>3
                      <5> QED  BY <5>1, <5>2, <5>3
                 <4>2 CASE Fame[p][e] = FALSE /\ Fame[q][e] = TRUE
                      <5>1 \E s \in WitnessSet: s.frame > e.frame+1 /\ (s.frame-e.frame)%c # 0 /\ Cardinality({d \in ProcessSet: \E a \in s.stronglysees: a.source = d /\ Votes[q][a][e]=TRUE}) > 2*f /\ s \in WitnessDAG[q][s.frame][s.source] /\ Votes[q][s][e] = TRUE
                           BY <2>1, <4>2, <1>1 DEF Inv10 
                      <5>2 \E s \in WitnessSet: s.frame > e.frame+1 /\ (s.frame-e.frame)%c # 0 /\ Cardinality({d \in ProcessSet: \E a \in s.stronglysees: a.source = d /\ Votes[p][a][e]=FALSE}) > 2*f /\ s \in WitnessDAG[p][s.frame][s.source] /\ Votes[p][s][e] = FALSE
                           BY <2>1, <4>2, <1>1 DEF Inv11
                      <5>3 ASSUME NEW s \in WitnessSet, NEW z \in WitnessSet, s.frame > e.frame+1, (s.frame-e.frame)%c # 0, Cardinality({d \in ProcessSet: \E a \in s.stronglysees: a.source = d /\ Votes[q][a][e]=TRUE}) > 2*f, s \in WitnessDAG[q][s.frame][s.source], Votes[q][s][e] = TRUE,
                                  z.frame > e.frame+1, (z.frame-e.frame)%c # 0, Cardinality({d \in ProcessSet: \E a \in z.stronglysees: a.source = d /\ Votes[p][a][e]=FALSE}) > 2*f, z \in WitnessDAG[p][z.frame][z.source], Votes[p][z][e] = FALSE
                           PROVE FALSE
                           <6>1 CASE s.frame >= z.frame
                                <7>1 Votes[q][s][e] = "undecided" \/ Votes[q][s][e] = FALSE
                                     BY <6>1, <5>3, <2>1, <1>1 DEF Inv16
                                <7> QED BY  <7>1, <5>3, unequalTF
                           <6>2 CASE z.frame >= s.frame
                                <7>1 Votes[p][z][e] = "undecided" \/ Votes[p][z][e] = TRUE
                                     BY <6>2, <5>3, <2>1, <1>1 DEF Inv15
                                <7> QED BY  <7>1, <5>3, unequalTF
                           <6>3 s.frame \in Nat /\ z.frame \in Nat
                                BY <5>3, Pslt1
                           <6> QED BY <6>1, <6>2, <6>3
                      <5> QED  BY <5>1, <5>2, <5>3
                 <4>3 Fame[p][e] \in BOOLEAN /\ Fame[q][e] \in BOOLEAN
                      BY <2>1, <1>1 DEF TypeOK, FameType
                 <4> QED BY <4>1, <4>2, <4>3, <3>2
            <3> QED BY <3>1, <3>2
       <2> QED BY <2>1 DEF FameSafetyInv17
  <1> QED BY <1>1, Inv15proof, Inv16proof, Inv10proof, Inv11proof, TypeOKcorrectness, PTL DEF FameSafetyInv17    
                                                                   
Inv18 == \A x \in Frames, p \in ProcessSet, q \in ProcessSet, e \in WitnessSet:
       (/\ e.frame =x
        /\ e \in WitnessDAG[p][x][e.source]
        /\ \E a \in WitnessSet: a \in WitnessDAG[p][x+2][a.source] /\ a.frame= x+2
        /\ Fame[p][e] = TRUE
        /\ \E a \in WitnessSet: a \in WitnessDAG[q][x+2][a.source] /\ a.frame= x+2)
           => e \in WitnessDAG[q][x][e.source]
           

LEMMA Inv18proof == Spec => []Inv18
 <1>1 ASSUME Inv12, Inv9, UniqueStronglyseenAs
      PROVE Inv18
      <2>1 ASSUME NEW x \in Frames, NEW p \in ProcessSet, NEW q \in ProcessSet, NEW e \in WitnessSet, e \in WitnessDAG[p][x][e.source], Fame[p][e] = TRUE, e.frame = x, \E a \in WitnessSet: a \in WitnessDAG[p][x+2][a.source] /\ a.frame= x+2, \E a \in WitnessSet: a \in WitnessDAG[q][x+2][a.source] /\ a.frame= x+2
           PROVE e \in WitnessDAG[q][x][e.source]
           <3>1 ASSUME NEW a \in WitnessSet, a \in WitnessDAG[q][x+2][a.source], a.frame = x+2
                PROVE Cardinality({j \in ProcessSet: \E z \in a.stronglysees: z.source = j /\ z.frame = a.frame-1 /\ z \in WitnessDAG[q][z.frame][z.source]})> 2*f
                <4>1 a \in WitnessSet /\ a \in WitnessDAG[q][a.frame][a.source] /\ q \in ProcessSet
                     BY <3>1, <2>1
                <4> QED BY <4>1, <1>1 DEF Inv9
           <3>2 \E a \in WitnessSet: a.frame = e.frame+2 /\ a \in WitnessDAG[p][a.frame][a.source] /\
                Cardinality({j \in ProcessSet: \E s \in a.stronglysees: s.source = j /\ s.frame = e.frame+1 /\ e \in s.stronglysees /\ s \in WitnessDAG[p][s.frame][s.source]}) > f
               BY <2>1, <1>1 DEF Inv12
           <3>3 \E b \in WitnessSet: b \in WitnessDAG[q][b.frame][b.source] /\ b.frame = e.frame+2 /\ Cardinality({j \in ProcessSet: \E z \in b.stronglysees: z.source = j /\ z.frame = b.frame-1 /\ z \in WitnessDAG[q][z.frame][z.source]})> 2*f
               BY <3>1, <2>1, Pslt1
           <3>4 \E a \in WitnessSet, b \in WitnessSet: /\ a.frame = e.frame+2 /\ b.frame = e.frame+2 /\ a \in WitnessDAG[p][a.frame][a.source] /\ b \in WitnessDAG[q][b.frame][b.source]
                                                       /\ Cardinality({j \in ProcessSet: \E s \in a.stronglysees: s.source = j /\ s.frame = e.frame+1 /\ e \in s.stronglysees /\ s \in WitnessDAG[p][s.frame][s.source]}) > f
                                                       /\ Cardinality({j \in ProcessSet: \E z \in b.stronglysees: z.source = j /\ z.frame = b.frame-1 /\ z \in WitnessDAG[q][z.frame][z.source]})> 2*f
                 BY <3>2, <3>3
           <3>5 \E a \in WitnessSet, b \in WitnessSet: /\ a.frame = e.frame+2 /\ b.frame = e.frame+2 /\ a \in WitnessDAG[p][a.frame][a.source] /\ b \in WitnessDAG[q][b.frame][b.source]
                                                       /\ \E j \in ProcessSet: \E s \in a.stronglysees, z \in b.stronglysees: s.source = z.source /\ s.frame = z.frame /\ s \in WitnessDAG[p][s.frame][s.source] /\ z \in WitnessDAG[q][z.frame][z.source] /\ e \in s.stronglysees
                <4>1 \A b \in WitnessSet: b.frame = e.frame+2 => e.frame+1 = b.frame-1
                      BY Pslt1
                <4> QED BY <4>1, <3>4, Pslt3
           <3>6 \E a \in WitnessSet, b \in WitnessSet: /\ a.frame = e.frame+2 /\ b.frame = e.frame+2 /\ a \in WitnessDAG[p][a.frame][a.source] /\ b \in WitnessDAG[q][b.frame][b.source]
                                                       /\ \E j \in ProcessSet: \E s \in a.stronglysees, z \in b.stronglysees: s.source = z.source /\ s.frame = z.frame /\ s \in WitnessDAG[p][s.frame][s.source] /\ (b \in WitnessDAG[q][b.frame][b.source] /\ z \in b.stronglysees) /\ (a \in WitnessDAG[p][a.frame][a.source] /\ s \in a.stronglysees) /\ z \in WitnessDAG[q][z.frame][z.source] /\ e \in s.stronglysees
                 BY Pslt1, <1>1, <3>5 DEF UniqueStronglyseenAs
           <3>7 \E a \in WitnessSet, b \in WitnessSet: /\ a.frame = e.frame+2 /\ b.frame = e.frame+2 /\ a \in WitnessDAG[p][a.frame][a.source] /\ b \in WitnessDAG[q][b.frame][b.source]
                                                       /\ \E j \in ProcessSet: \E s \in a.stronglysees, z \in b.stronglysees:  z \in WitnessDAG[q][z.frame][z.source] /\ e \in z.stronglysees
                 <4>1 ASSUME NEW a \in WitnessSet, NEW z \in a.stronglysees
                      PROVE z \in WitnessSet
                      BY <4>1, Pslt1
                 <4> QED BY <4>1, <1>1, <3>6 DEF UniqueStronglyseenAs
           <3>8 \E a \in WitnessSet, b \in WitnessSet: /\ a.frame = e.frame+2 /\ b.frame = e.frame+2 /\ a \in WitnessDAG[p][a.frame][a.source] /\ b \in WitnessDAG[q][b.frame][b.source]
                                                       /\ \E j \in ProcessSet: \E s \in a.stronglysees, z \in b.stronglysees:  z \in WitnessDAG[q][z.frame][z.source] /\ e \in z.stronglysees /\ e \in WitnessDAG[q][e.frame][e.source]
                 BY <1>1, <3>7, <2>1, Pslt1 DEF Inv9
           <3>9 e \in WitnessDAG[q][e.frame][e.source]
                BY <3>8
           <3> QED BY <3>9, <2>1
      <2> QED BY <2>1 DEF Inv18
 <1> QED BY <1>1, PTL, Inv12proof, UsAsproof, Inv9proof

THEOREM safetyproof == Spec => []Safety
 <1>1 ASSUME FameSafetyInv17, Inv18, TypeOK, Inv13, Inv14, Inv12, UniqueStronglyseenAs
      PROVE Safety
      <2>1 ASSUME NEW p \in ProcessSet, NEW q \in ProcessSet, NEW x \in Frames, DecidedFrames[p][x], DecidedFrames[q][x]
           PROVE FamousWitnesses[p][x] = FamousWitnesses[q][x]
           <3>1 CASE \E e \in WitnessSet: e \in FamousWitnesses[p][x] /\ e \notin FamousWitnesses[q][x]
                <4>1 \E e \in WitnessSet: e \in FamousWitnesses[p][x] /\ e \notin FamousWitnesses[q][x]  
                     BY <3>1, <2>1
                <4>2 ASSUME  NEW e \in WitnessSet, e \in FamousWitnesses[p][x], e \notin FamousWitnesses[q][x]
                     PROVE FALSE
                     <5>2 e.frame = x /\ e \in WitnessDAG[p][x][e.source] /\ Fame[p][e] = TRUE
                          BY <4>2, <2>1, <1>1 DEF Inv13
                     <5>5 e \in WitnessDAG[q][x][e.source]
                          BY <2>1, <5>2, <1>1, <4>2 DEF Inv18, Inv13
                     <5>1 Fame[q][e] = FALSE \/ (\E z \in WitnessSet: z.frame = e.frame+2 /\ z \in WitnessDAG[q][z.frame][z.source] /\ Cardinality({j \in ProcessSet: \E a \in z.stronglysees: a.source = j /\ a.frame = e.frame+1 /\ a \in WitnessDAG[q][a.frame][a.source] /\ e \notin a.stronglysees}) > 2*f)
                          <6>1 e \notin FamousWitnesses[q][x] /\ DecidedFrames[q][x] /\ x \in Frames /\ q \in ProcessSet /\ e \in WitnessSet
                               BY <4>2, <2>1
                          <6> QED BY <6>1, <1>1, <5>2 DEF  Inv14
                     <5>3 Fame[q][e] = FALSE => Fame[q][e] # "undecided" /\ Fame[p][e] # "undecided" 
                          BY <5>1, <4>2, <2>1, <1>1, <5>2, unequalTF, <5>5
                     <5>4 Fame[q][e] = FALSE => Fame[p][e] = Fame[q][e]
                          BY <5>2, <5>3, <4>2, <2>1, <1>1, <5>5 DEF FameSafetyInv17
                     <5>6 Fame[q][e] # FALSE
                          BY <5>4, <5>2
                     <5>7 \E b \in WitnessSet: b.frame = e.frame+2 /\ b \in WitnessDAG[p][b.frame][b.source] /\ Cardinality({j \in ProcessSet: \E s \in b.stronglysees: s.source = j /\ s.frame = e.frame+1 /\ e \in s.stronglysees /\ s \in WitnessDAG[p][s.frame][s.source]}) > f
                          BY <4>2, <2>1, <1>1, <5>2 DEF Inv12
                     <5>8 \E z \in WitnessSet, b \in WitnessSet: 
                                 /\ b.frame = e.frame+2 /\ b \in WitnessDAG[p][b.frame][b.source] 
                                 /\ z.frame = e.frame+2 /\ z \in WitnessDAG[q][z.frame][z.source]
                                 /\ Cardinality({j \in ProcessSet: \E s \in b.stronglysees: s.source = j /\ s.frame = e.frame+1 /\ s \in WitnessDAG[p][s.frame][s.source] /\ e \in s.stronglysees}) > f
                                 /\ Cardinality({j \in ProcessSet: \E a \in z.stronglysees: a.source = j /\ a.frame = e.frame+1 /\ a \in WitnessDAG[q][a.frame][a.source] /\ e \notin a.stronglysees}) > 2*f
                           BY <5>6, <5>7, <5>1, Pslt3
                     <5>9 \E z \in WitnessSet, b \in WitnessSet: 
                                 /\ b \in WitnessDAG[p][b.frame][b.source] 
                                 /\ z \in WitnessDAG[q][z.frame][z.source]
                                 /\ \E s \in b.stronglysees, a \in z.stronglysees: /\ s.source = a.source /\ s.frame = a.frame 
                                                                                   /\ s \in WitnessDAG[p][s.frame][s.source] /\ e \in s.stronglysees 
                                                                                   /\ a \in WitnessDAG[q][a.frame][a.source] /\ e \notin a.stronglysees
                           BY <5>8, Pslt3
                     <5>10 \E z \in WitnessSet, b \in WitnessSet: 
                                 /\ \E s \in b.stronglysees, a \in z.stronglysees: /\ \E m \in WitnessSet: m \in WitnessDAG[q][m.frame][m.source] /\ a \in m.stronglysees
                                                                                   /\ \E l \in WitnessSet: l \in WitnessDAG[p][l.frame][l.source] /\ s \in l.stronglysees
                                                                                   /\ s.source = a.source /\ s.frame = a.frame \*/\ s = a
                                                                                   /\  e \in s.stronglysees 
                                                                                   /\  e \notin a.stronglysees
                           BY <5>9, <1>1 DEF UniqueStronglyseenAs
                     <5>11 \E z \in WitnessSet, b \in WitnessSet: 
                                 /\ \E s \in b.stronglysees, a \in z.stronglysees: /\ s = a
                                                                                   /\ e \in s.stronglysees 
                                                                                   /\ e \notin a.stronglysees
                           BY <5>10, <1>1, <2>1, Pslt1 DEF UniqueStronglyseenAs
                     <5> QED BY <5>11
                <4> QED BY <4>1, <4>2
           <3>2 CASE \E e \in WitnessSet: e \in FamousWitnesses[q][x] /\ e \notin FamousWitnesses[p][x]
                <4>1 \E e \in WitnessSet: e \in FamousWitnesses[q][x] /\ e \notin FamousWitnesses[p][x] 
                     BY <3>2, <2>1
                <4>2 ASSUME  NEW e \in WitnessSet,  e \in FamousWitnesses[q][x], e \notin FamousWitnesses[p][x]
                     PROVE FALSE
                     <5>2 e.frame = x /\ e \in WitnessDAG[q][x][e.source] /\ Fame[q][e] = TRUE
                          BY <4>2, <2>1, <1>1 DEF Inv13
                     <5>5 e \in WitnessDAG[p][x][e.source]
                          BY <2>1, <5>2, <1>1, <4>2 DEF Inv18, Inv13
                     <5>1 Fame[p][e] = FALSE \/ (\E z \in WitnessSet: z.frame = e.frame+2 /\ z \in WitnessDAG[p][z.frame][z.source] /\ Cardinality({j \in ProcessSet: \E a \in z.stronglysees: a.source = j /\ a.frame = e.frame+1 /\ a \in WitnessDAG[p][a.frame][a.source] /\ e \notin a.stronglysees}) > 2*f)
                          <6>1 e \notin FamousWitnesses[p][x] /\ DecidedFrames[p][x] /\ x \in Frames /\ p \in ProcessSet /\ e \in WitnessSet
                               BY <4>2, <2>1
                          <6> QED BY <6>1, <1>1, <5>2 DEF  Inv14
                     <5>3 Fame[p][e] = FALSE => Fame[p][e] # "undecided" /\ Fame[q][e] # "undecided" 
                          BY <5>1, <4>2, <2>1, <1>1, <5>2, unequalTF, <5>5
                     <5>4 Fame[p][e] = FALSE => Fame[p][e] = Fame[q][e]
                          BY <5>2, <5>3, <4>2, <2>1, <1>1, <5>5 DEF FameSafetyInv17
                     <5>6 Fame[p][e] # FALSE
                          BY <5>4, <5>2
                     <5>7 \E b \in WitnessSet: b.frame = e.frame+2 /\ b \in WitnessDAG[q][b.frame][b.source] /\ Cardinality({j \in ProcessSet: \E s \in b.stronglysees: s.source = j /\ s.frame = e.frame+1 /\ e \in s.stronglysees /\ s \in WitnessDAG[q][s.frame][s.source]}) > f
                          BY <4>2, <2>1, <1>1, <5>2 DEF Inv12
                     <5>8 \E z \in WitnessSet, b \in WitnessSet: 
                                 /\ b.frame = e.frame+2 /\ b \in WitnessDAG[q][b.frame][b.source] 
                                 /\ z.frame = e.frame+2 /\ z \in WitnessDAG[p][z.frame][z.source]
                                 /\ Cardinality({j \in ProcessSet: \E s \in b.stronglysees: s.source = j /\ s.frame = e.frame+1 /\ s \in WitnessDAG[q][s.frame][s.source] /\ e \in s.stronglysees}) > f
                                 /\ Cardinality({j \in ProcessSet: \E a \in z.stronglysees: a.source = j /\ a.frame = e.frame+1 /\ a \in WitnessDAG[p][a.frame][a.source] /\ e \notin a.stronglysees}) > 2*f
                           BY <5>6, <5>7, <5>1, Pslt3
                     <5>9 \E z \in WitnessSet, b \in WitnessSet: 
                                 /\ b \in WitnessDAG[q][b.frame][b.source] 
                                 /\ z \in WitnessDAG[p][z.frame][z.source]
                                 /\ \E s \in b.stronglysees, a \in z.stronglysees: /\ s.source = a.source /\ s.frame = a.frame 
                                                                                   /\ s \in WitnessDAG[q][s.frame][s.source] /\ e \in s.stronglysees 
                                                                                   /\ a \in WitnessDAG[p][a.frame][a.source] /\ e \notin a.stronglysees
                           BY <5>8, Pslt3
                     <5>10 \E z \in WitnessSet, b \in WitnessSet: 
                                 /\ \E s \in b.stronglysees, a \in z.stronglysees: /\ \E m \in WitnessSet: m \in WitnessDAG[p][m.frame][m.source] /\ a \in m.stronglysees
                                                                                   /\ \E l \in WitnessSet: l \in WitnessDAG[q][l.frame][l.source] /\ s \in l.stronglysees
                                                                                   /\ s.source = a.source /\ s.frame = a.frame \*/\ s = a
                                                                                   /\  e \in s.stronglysees 
                                                                                   /\  e \notin a.stronglysees
                           BY <5>9, <1>1 DEF UniqueStronglyseenAs
                     <5>11 \E z \in WitnessSet, b \in WitnessSet: 
                                 /\ \E s \in b.stronglysees, a \in z.stronglysees: /\ s = a
                                                                                   /\ e \in s.stronglysees 
                                                                                   /\ e \notin a.stronglysees
                           BY <5>10, <1>1, <2>1, Pslt1 DEF UniqueStronglyseenAs
                     <5> QED BY <5>11
                <4> QED BY <4>1, <4>2
           <3>3 CASE FamousWitnesses[p][x] = FamousWitnesses[q][x]
                BY <3>3
           <3> QED BY <3>1, <3>2, <3>3, <1>1, <2>1 DEF TypeOK, FamousWitnessesType
      <2> QED BY <2>1 DEF Safety
 <1> QED BY <1>1, PTL, Inv18proof, FameSafetyInv17proof, Inv13proof, TypeOKcorrectness, Inv14proof, UsAsproof, Inv12proof
=============================================================================
\* Modification History
\* Last modified Wed Sep 04 18:11:20 AEST 2024 by pgho0778
\* Created Wed Sep 04 12:36:43 AEST 2024 by pgho0778
