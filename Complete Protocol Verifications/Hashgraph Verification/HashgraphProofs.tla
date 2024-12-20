-------------------------- MODULE HashgraphProofs --------------------------

EXTENDS FiniteSets,
        Integers,
        Sequences,
        TLAPS,
        TLC,
        HashgraphCompleteSpec

--------------------------------------------------------------------------- 

LEMMA Pslt1 == ASSUME NEW l \in WitnessSet, NEW a \in WitnessSet,
                      a \in l.stronglysees
               PROVE StronglySees(l.event, a.event)

LEMMA Pslt2 == ASSUME NEW a \in WitnessSet PROVE a.event.source = a.source

LEMMA Pslt3 == ASSUME NEW a \in WitnessSet, NEW b \in WitnessSet,
                      a.frame = b.frame, a.source = b.source
               PROVE ~Path(a.event, b.event) 

LEMMA Pslt4 == ASSUME NEW e \in EventSet
               PROVE /\ WitnessOfEvent(e) \in WitnessSet
                     /\ WitnessOfEvent(e).event = e

LEMMA Pslt5 == ASSUME NEW A \in SUBSET(EventSet), NEW B \in SUBSET(EventSet),
                      Cardinality({q \in ProcessSet: (\E u \in A: u.source = q)}) > 2*f,
                      Cardinality({q \in ProcessSet: (\E u \in B: u.source = q)}) > 2*f
               PROVE A \cap B \in SUBSET(ProcessSet) /\ Cardinality(A \cap B) > f

LEMMA Pslt6 == ASSUME NEW e \in EventSet, NEW u \in EventSet, NEW a \in EventSet,
                      Path(e, u), Sees(u, a)
               PROVE Sees(e, a)

LEMMA Pslt7 == ASSUME NEW e \in EventSet, NEW u \in EventSet, NEW a \in EventSet,
                      u.id <= e.id, ~Path(e, u), Sees(a, e)
               PROVE ~Sees(a, u)                     

LEMMA CardinalityPslt == 
  /\ Cardinality({}) = 0 
  /\ \A x \in Nat: Cardinality(1..(x+1)) = x+1
  /\ \A S \in SUBSET(Nat) : Cardinality(S) \in Nat
  /\ \A S \in SUBSET(Nat), p \in Nat: p \notin S => Cardinality(S \cup {p}) = Cardinality(S) + 1

LEMMA QouramIntersectPslt == 
  \A X \in SUBSET(Nat), b \in Nat: \A A \in SUBSET(X), B \in SUBSET(X), C \in SUBSET(X): 
                              (/\ Cardinality(X) = 3*b+1
                               /\ Cardinality(A) > 2*b
                               /\ Cardinality(B) > 2*b
                               /\ Cardinality(C) <= b)
                                   => (A \cap B) \cap (X\C) # {}
---------------------------------------------------------------------------              

Inv0 == 
  \A p \in ProcessSet, a \in EventSet: 
    (/\ p \notin faulty 
     /\ a \in hashgraph[p][a.source][a.id])
       => \A u \in EventSet: Path(a, u) => u \in hashgraph[p][u.source][u.id]

Inv1 == 
  \A p \in ProcessSet, u \in EventSet, a \in EventSet : 
    (/\ p \notin faulty 
     /\ StronglySees(a, u) 
     /\ a \in hashgraph[p][a.source][a.id])
       => \E A \in SUBSET(EventSet): 
           /\ Cardinality({q \in ProcessSet: (\E x \in A: x.source = q)}) > 2*f
           /\ \A x \in A: x \in hashgraph[p][x.source][x.id] /\ Sees(x, u)


Inv3 == 
  \A A \in SUBSET(EventSet), B \in SUBSET(EventSet) : 
       (/\ Cardinality({q \in ProcessSet: (\E u \in A: u.source = q)}) > 2*f
        /\ Cardinality({q \in ProcessSet: (\E u \in B: u.source = q)}) > 2*f)
          => \E a \in A, b \in B: /\ a.source = b.source 
                                  /\ a.source \notin faulty
 
Inv4 ==
  \A p \in ProcessSet, u \in EventSet:
    (/\ p \notin faulty
     /\ u.source \notin faulty
     /\ u \in hashgraph[p][u.source][u.id])
       => u \in hashgraph[u.source][u.source][u.id]

      
Inv5 ==
  \A u \in EventSet, e \in EventSet:
   (/\ u \in hashgraph[u.source][u.source][u.id]
    /\ e \in hashgraph[e.source][e.source][e.id]
    /\ u.source = e.source
    /\ u.source \notin faulty
    /\ u.id <= e.id)
     => Path(e, u)
 
Inv6 == 
  \A u \in EventSet, e \in EventSet, p \in ProcessSet, q \in ProcessSet:
    (/\ p \notin faulty /\ q \notin faulty
     /\ u \in hashgraph[p][u.source][u.id]
     /\ e \in hashgraph[q][e.source][e.id]
     /\ u.source = e.source
     /\ u.source \notin faulty)
       => Path(u, e) \/ Path(e, u)

---------------------------------------------------------------------------

HashgraphInv == 
  \A u \in EventSet, e \in EventSet, p \in ProcessSet, q \in ProcessSet: 
     (/\ p \notin faulty /\ q \notin faulty
      /\ u.source = e.source
      /\ ~Path(e, u) /\ ~Path(u, e)
      /\ \E a \in EventSet: /\ a \in hashgraph[p][a.source][a.id] 
                            /\ StronglySees(a, u)
      /\ \E b \in EventSet: /\ b \in hashgraph[q][b.source][b.id] 
                            /\ StronglySees(b, e)
     ) => FALSE
---------------------------------------------------------------------------

WitnessInv == 
  \A a \in WitnessSet, i \in ProcessSet: 
    (i \notin faulty /\ a \in witnessDAG[i][a.frame][a.source])
      =>(/\ a.event \in hashgraph[i][a.event.source][a.event.id]
         /\ \A b \in a.stronglysees: b \in witnessDAG[i][b.frame][b.source])

---------------------------------------------------------------------------

equalvar == witnessDAG = VVWitnessDAG

--------------------------------------------------------------------------

THEOREM TypeOKproof == Spec => []TypeOK
 <1>1 ASSUME Init
      PROVE TypeOK
      BY <1>1, WitnessSetTypeAs, EventSetAs DEF Init, TypeOK, Genesis, TypeOK
 <1>2 ASSUME [Next]_vars, TypeOK
      PROVE TypeOK'
      <3>2 ASSUME NEW p \in ProcessSet, NEW q \in ProcessSet, NEW x \in BlockIds, NEW E \in SUBSET(EventSet), FaultyChangeHashgraphTn(p, q, x, E)
           PROVE TypeOK'
           BY <3>2, <1>2 DEF FaultyChangeHashgraphTn, TypeOK
      <3>3 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, NEW z \in EventSet, ReceiveEventTn(e, p, z)
           PROVE TypeOK'
           BY <3>3, <1>2 DEF ReceiveEventTn, TypeOK
      <3>4 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, DecideWitnessTn(e, p)
           PROVE TypeOK'
           BY <3>4, <1>2, WitnessSetAs, WitnessSetTypeAs DEF DecideWitnessTn, TypeOK
      <3>5 ASSUME UNCHANGED vars
           PROVE TypeOK'
           BY <3>5, <1>2 DEF vars, TypeOK
      <3>6 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, DecideFameTn(p, g, d)
           PROVE TypeOK'
           BY <1>2, <3>6 DEF vars1, DecideFameTn, TypeOK
      <3>7 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, VoteTn(p, g, d)
           PROVE TypeOK'
           BY <1>2, <3>7 DEF vars1, VoteTn, TypeOK
      <3>8 ASSUME NEW p \in ProcessSet, NEW u \in Frames, NEW g \in WitnessSet, DecideFrameTn(p, u)
           PROVE TypeOK'
           BY <1>2, <3>8 DEF vars1, DecideFrameTn, TypeOK
      <3> QED BY <3>2, <3>3, <3>4, <3>5, <1>2, <3>6, <3>7, <3>8 DEF Next  
 <1> QED BY <1>1, <1>2, PTL DEF Spec

LEMMA Inv0proof == Spec => []Inv0
 <1>1 ASSUME Init, TypeOK 
      PROVE Inv0
      <2>1 ASSUME NEW u \in EventSet, NEW p \in ProcessSet, u \in hashgraph[p][u.source][u.id]
           PROVE p = u.source /\ u.id = 1
           BY EventSetTypeAs, <2>1, <1>1 DEF TypeOK, Init
      <2>2 ASSUME NEW u \in EventSet, NEW v \in EventSet, Path(u, v), u.id = 1
           PROVE v = u
           BY <2>2, PathAs
      <2> QED BY <2>1, <1>1, WitnessSetTypeAs, <2>2 DEF Init, TypeOK, Genesis, Inv0
 <1>2 ASSUME [Next]_vars, Inv0, TypeOK
      PROVE Inv0'
           
      <3>2 ASSUME NEW p \in ProcessSet, NEW q \in ProcessSet, NEW x \in BlockIds, NEW E \in SUBSET(EventSet), FaultyChangeHashgraphTn(p, q, x, E)
           PROVE Inv0'
           BY <3>2, <1>2 DEF TypeOK, FaultyChangeHashgraphTn, Inv0
      <3>3 ASSUME NEW i \in ProcessSet, NEW e \in EventSet, NEW z \in EventSet, ReceiveEventTn(e, i, z)
           PROVE Inv0'
           <4>1 ASSUME NEW p \in ProcessSet, NEW a \in EventSet, p \notin faulty , a \in hashgraph'[p][a.source][a.id]
                PROVE \A u \in EventSet: Path(a, u) => u \in hashgraph'[p][u.source][u.id]
                <5>1 ASSUME a # e /\ a # z
                     PROVE a \in hashgraph[p][a.source][a.id]
                     BY <5>1, <4>1, <3>3, <1>2, EventSetTypeAs DEF TypeOK, ReceiveEventTn
                <5>2 ASSUME NEW u \in EventSet, u \in hashgraph[p][u.source][u.id]
                     PROVE u \in hashgraph'[p][u.source][u.id]
                     BY <5>2, <4>1, <3>3, <1>2, EventSetTypeAs DEF TypeOK, ReceiveEventTn
                <5>3 e # z
                     BY <3>3 DEF ReceiveEventTn
                <5>4 CASE p = i /\ z = a
                     <6>1 ASSUME NEW u \in EventSet, Path(a, u) PROVE u \in hashgraph'[p][u.source][u.id]
                          <7>1 CASE u = e
                               BY <7>1, <5>4, <4>1, <3>3, <1>2, EventSetTypeAs DEF TypeOK, ReceiveEventTn
                          <7>2 CASE u # e
                               BY <5>4, <7>2, <3>3, <5>2, <6>1 DEF ReceiveEventTn
                          <7> QED BY <7>1, <7>2
                     <6> QED BY <6>1, <5>4, <3>3, <4>1, <5>2 DEF ReceiveEventTn
                <5>5 CASE p = i /\ e = a
                     <6>1 \A u \in EventSet: Path(a, u) => u \in hashgraph'[p][u.source][u.id]
                          <7>1 CASE e.id = 1
                               <8>1  \A u \in EventSet: Path(a, u) => a = u
                                     BY <5>5, <7>1, PathAs
                               <8> QED BY <8>1, <4>1, <3>3, <1>2, EventSetTypeAs DEF TypeOK, ReceiveEventTn
                          <7>2 CASE e.id # 1
                               BY <5>5, <7>2, <3>3, <5>2 DEF ReceiveEventTn
                          <7> QED BY <7>1, <7>2
                     <6> QED BY <6>1, <5>5, <3>3, <4>1, <5>2 DEF ReceiveEventTn
                <5>6 CASE p = i /\ e # a /\ z # a
                     BY <5>6, <3>3, <4>1, <1>2, <5>2, <5>1 DEF ReceiveEventTn, Inv0, TypeOK
                <5>7 CASE p # i
                     <6>1 ASSUME NEW u \in EventSet
                          PROVE hashgraph'[p][u.source][u.id] = hashgraph[p][u.source][u.id]
                          BY <3>3, <5>7, <1>2, <6>1 DEF ReceiveEventTn, TypeOK
                     <6> QED BY <6>1, <4>1, <1>2, <5>2 DEF Inv0
                <5> QED BY <5>3, <5>4, <5>5, <5>6, <5>7 
           <4> QED BY <4>1, <3>3 DEF ReceiveEventTn, Inv0
      <3>4 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, DecideWitnessTn(e, p)
           PROVE Inv0'
           BY <3>4, <1>2 DEF TypeOK, DecideWitnessTn, Inv0
      <3>5 ASSUME UNCHANGED vars
           PROVE Inv0'
           BY <3>5, <1>2 DEF vars, Inv0
      <3>6 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, DecideFameTn(p, g, d)
           PROVE Inv0'
           BY <1>2, <3>6 DEF vars1, DecideFameTn, Inv0
      <3>7 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, VoteTn(p, g, d)
           PROVE Inv0'
           BY <1>2, <3>7 DEF vars1, VoteTn, Inv0
      <3>8 ASSUME NEW p \in ProcessSet, NEW u \in Frames, NEW g \in WitnessSet, DecideFrameTn(p, u)
           PROVE Inv0'
           BY <1>2, <3>8 DEF vars1, DecideFrameTn, Inv0
      <3> QED BY <3>2, <3>3, <3>4, <3>5, <1>2, <3>6, <3>7, <3>8 DEF Next 
 <1> QED BY <1>1, <1>2, PTL, TypeOKproof DEF Spec
     
LEMMA Inv1proof == Spec => []Inv1
  <1>1 ASSUME Inv0, TypeOK
       PROVE Inv1
       <2>1 ASSUME NEW p \in ProcessSet, NEW u \in EventSet, NEW a \in EventSet, p \notin faulty, StronglySees(a, u), a \in hashgraph[p][a.source][a.id]
            PROVE \E A \in SUBSET(EventSet): /\ Cardinality({q \in ProcessSet: (\E x \in A: x.source = q)}) > 2*f
                                             /\ \A x \in A: x \in hashgraph[p][x.source][x.id] /\ Sees(x, u)
            <3>1 \E A \in SUBSET(EventSet): /\ Cardinality({q \in ProcessSet: (\E x \in A: x.source = q)}) > 2*f
                                            /\ \A x \in A: Path(a, x) /\ Sees(x, u)
                  BY <2>1 DEF StronglySees
            <3> QED BY <3>1, <2>1, <1>1 DEF Inv0
       <2> QED BY <2>1 DEF Inv1
  <1> QED BY <1>1, PTL, Inv0proof, TypeOKproof

 
LEMMA Inv3proof == Spec => []Inv3
 <1>1 ASSUME  TypeOK
      PROVE Inv3
      <2>1 ProcessSet \in SUBSET(Nat) /\ f \in Nat /\ Cardinality(ProcessSet) = 3*f+1
           BY fAs, CardinalityPslt DEF ProcessSet
      <2>2 faulty \in SUBSET(ProcessSet) /\ Cardinality(faulty) <= f
           BY faultyAs, <1>1 DEF  TypeOK
      <2>3 ASSUME NEW A \in SUBSET(EventSet), NEW B \in SUBSET(EventSet), Cardinality({q \in ProcessSet: (\E u \in A: u.source = q)}) > 2*f, Cardinality({q \in ProcessSet: (\E u \in B: u.source = q)}) > 2*f
           PROVE \E a \in A, b \in B: a.source = b.source /\ a.source \notin faulty
          <3>1 ({q \in ProcessSet: (\E u \in A: u.source = q)} \cap {q \in ProcessSet: (\E u \in B: u.source = q)}) \cap (ProcessSet \ faulty) # {}
               BY <2>3, <2>2, <2>1, QouramIntersectPslt
          <3> QED BY <3>1
      <2> QED BY <2>3 DEF Inv3
 <1> QED BY <1>1, PTL, TypeOKproof

LEMMA Inv4proof == Spec => []Inv4
 <1>1 ASSUME Init, TypeOK 
      PROVE Inv4
      <2>1 ASSUME NEW u \in EventSet, NEW p \in ProcessSet, u \in hashgraph[p][u.source][u.id]
           PROVE p = u.source
           BY EventSetTypeAs, <2>1, <1>1 DEF TypeOK, Init
      <2> QED BY <2>1, <1>1, WitnessSetTypeAs DEF Init, TypeOK, Genesis, Inv4
 <1>2 ASSUME [Next]_vars, Inv4, TypeOK
      PROVE Inv4'
      <3>2 ASSUME NEW p \in ProcessSet, NEW q \in ProcessSet, NEW x \in BlockIds, NEW E \in SUBSET(EventSet), FaultyChangeHashgraphTn(p, q, x, E)
           PROVE Inv4'
           BY <3>2, <1>2 DEF TypeOK, FaultyChangeHashgraphTn, Inv4
      <3>3 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, NEW z \in EventSet, ReceiveEventTn(e, p, z)
           PROVE Inv4'
           <4>1 ASSUME NEW u \in EventSet, NEW i \in ProcessSet, u \in hashgraph'[i][u.source][u.id], i \notin faulty, u.source \notin faulty
                PROVE u \in hashgraph'[u.source][u.source][u.id]
                <5>1 ASSUME u # e /\ u # z
                     PROVE u \in hashgraph[i][u.source][u.id]
                     BY <5>1, <4>1, <3>3, <1>2, EventSetTypeAs DEF TypeOK, ReceiveEventTn
                <5>2 ASSUME u \in hashgraph[u.source][u.source][u.id]
                     PROVE u \in hashgraph'[u.source][u.source][u.id]
                     BY <5>2, <4>1, <3>3, <1>2, EventSetTypeAs DEF TypeOK, ReceiveEventTn
                <5>3 e # z
                     BY <3>3 DEF ReceiveEventTn
                <5>4 CASE p = i /\ z = u
                     BY <5>4, <3>3, <4>1 DEF ReceiveEventTn
                <5>5 CASE p = i /\ e = u
                     BY <5>5, <3>3, <4>1 DEF ReceiveEventTn
                <5>6 CASE p = i /\ e # u /\ z # u
                     BY <5>6, <3>3, <4>1, <1>2, <5>2, <5>1 DEF ReceiveEventTn, Inv4, TypeOK
                <5>7 CASE p # i
                     <6>1 hashgraph'[i][u.source][u.id] = hashgraph[i][u.source][u.id]
                          BY <3>3, <5>7, <1>2 DEF ReceiveEventTn, TypeOK
                     <6> QED BY <6>1, <4>1, <1>2, <5>2 DEF Inv4
                <5> QED BY <5>3, <5>4, <5>5, <5>6, <5>7
           <4> QED BY <4>1, <3>3 DEF TypeOK, ReceiveEventTn, Inv4
      <3>4 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, DecideWitnessTn(e, p)
           PROVE Inv4'
           BY <3>4, <1>2 DEF TypeOK, DecideWitnessTn, Inv4
      <3>5 ASSUME UNCHANGED vars
           PROVE Inv4'
           BY <3>5, <1>2 DEF vars, Inv4
      <3>6 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, DecideFameTn(p, g, d)
           PROVE Inv4'
           BY <1>2, <3>6 DEF vars1, DecideFameTn, Inv4
      <3>7 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, VoteTn(p, g, d)
           PROVE Inv4'
           BY <1>2, <3>7 DEF vars1, VoteTn, Inv4
      <3>8 ASSUME NEW p \in ProcessSet, NEW u \in Frames, NEW g \in WitnessSet, DecideFrameTn(p, u)
           PROVE Inv4'
           BY <1>2, <3>8 DEF vars1, DecideFrameTn, Inv4
      <3> QED BY <3>2, <3>3, <3>4, <3>5, <1>2, <3>6, <3>7, <3>8 DEF Next 
 <1> QED BY <1>1, <1>2, PTL, TypeOKproof DEF Spec

LEMMA Inv5proof == Spec => []Inv5
 <1>1 ASSUME Init, TypeOK 
      PROVE Inv5
      <2>1 ASSUME NEW e \in EventSet
           PROVE Path(e, e)
           BY PathAs, <2>1
      <2> QED BY <2>1, <1>1, WitnessSetTypeAs, EventSetTypeAs DEF Init, TypeOK, Genesis, Inv5
 <1>2 ASSUME [Next]_vars, Inv5, TypeOK
      PROVE Inv5'
      <3>2 ASSUME NEW p \in ProcessSet, NEW q \in ProcessSet, NEW x \in BlockIds, NEW E \in SUBSET(EventSet), FaultyChangeHashgraphTn(p, q, x, E)
           PROVE Inv5'
           BY <3>2, <1>2 DEF TypeOK, FaultyChangeHashgraphTn, Inv5
      <3>3 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, NEW z \in EventSet, ReceiveEventTn(e, p, z)
           PROVE Inv5'
           <4>1 ASSUME NEW a \in EventSet, NEW b \in EventSet, b \in hashgraph'[b.source][b.source][b.id], a \in hashgraph'[a.source][a.source][a.id], a.source = b.source, a.source \notin faulty, a.id <= b.id
                PROVE Path(b, a)
                <5>1 ASSUME NEW x \in EventSet, x # e /\ x # z, x \in hashgraph'[x.source][x.source][x.id]
                     PROVE x \in hashgraph[x.source][x.source][x.id]
                     BY <5>1, <4>1, <3>3, <1>2, EventSetTypeAs DEF TypeOK, ReceiveEventTn
                <5>2 ASSUME NEW x \in EventSet, x \in hashgraph[x.source][x.source][x.id]
                     PROVE x \in hashgraph'[x.source][x.source][x.id]
                     BY <5>2, <4>1, <3>3, <1>2, EventSetTypeAs DEF TypeOK, ReceiveEventTn
                <5>3 e # z
                     BY <3>3 DEF ReceiveEventTn
                <5>4 CASE b.source = p
                     <6>1 b # e /\ a # e
                          BY <3>3, <4>1, <5>4 DEF ReceiveEventTn
                     <6>2 CASE z = b /\ z # a
                          BY <5>4, <6>2, <4>1, <3>3, <5>1 DEF ReceiveEventTn
                     <6>3 CASE z = a /\ z # b
                          <7>1 b \in hashgraph[b.source][b.source][b.id]
                               BY <6>3, <6>1, <5>1, <4>1
                          <7>2 b.id < a.id
                               BY <7>1, <6>3, <5>4, <3>3 DEF ReceiveEventTn
                          <7> QED BY <7>2, <4>1, EventSetTypeAs DEF BlockIds
                     <6>4 CASE z # b /\ z # a
                          BY <6>4, <6>1, <4>1, <5>1, <1>2 DEF Inv5
                     <6>5 CASE a = b
                          BY <4>1, <6>5, PathAs
                     <6> QED BY <6>2, <6>3, <6>4, <6>5
                <5>5 CASE b.source # p
                     <6>1 hashgraph'[b.source][b.source][b.id] = hashgraph[b.source][b.source][b.id]
                          BY <3>3, <5>5, <1>2 DEF ReceiveEventTn, TypeOK
                     <6>2 hashgraph'[a.source][a.source][a.id] = hashgraph[a.source][a.source][a.id]
                          BY <3>3, <5>5, <1>2, <4>1 DEF ReceiveEventTn, TypeOK
                     <6> QED BY <6>1, <6>2, <4>1, <1>2, <5>2 DEF Inv5 
                <5> QED BY <5>4, <5>5
           <4> QED BY <4>1, <3>3 DEF ReceiveEventTn, Inv5
      <3>4 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, DecideWitnessTn(e, p)
           PROVE Inv5'
           BY <3>4, <1>2 DEF TypeOK, DecideWitnessTn, Inv5
      <3>5 ASSUME UNCHANGED vars
           PROVE Inv5'
           BY <3>5, <1>2 DEF vars, Inv5
      <3>6 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, DecideFameTn(p, g, d)
           PROVE Inv5'
           BY <1>2, <3>6 DEF vars1, DecideFameTn, Inv5
      <3>7 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, VoteTn(p, g, d)
           PROVE Inv5'
           BY <1>2, <3>7 DEF vars1, VoteTn, Inv5
      <3>8 ASSUME NEW p \in ProcessSet, NEW u \in Frames, NEW g \in WitnessSet, DecideFrameTn(p, u)
           PROVE Inv5'
           BY <1>2, <3>8 DEF vars1, DecideFrameTn, Inv5
      <3> QED BY <3>2, <3>3, <3>4, <3>5, <1>2, <3>6, <3>7, <3>8 DEF Next 
 <1> QED BY <1>1, <1>2, PTL, TypeOKproof DEF Spec

LEMMA Inv6proof == Spec => []Inv6
 <1>1 ASSUME Inv4, Inv5
      PROVE Inv6
      <2>1 ASSUME NEW a \in EventSet, NEW  b \in EventSet, NEW p \in ProcessSet, NEW q \in ProcessSet, p \notin faulty, q \notin faulty, a \in hashgraph[p][a.source][a.id], b \in hashgraph[q][b.source][b.id], a.source = b.source, a.source \notin faulty
           PROVE Path(a, b) \/ Path(b, a)
           <3>1 a \in hashgraph[a.source][a.source][a.id] /\ b \in hashgraph[b.source][b.source][b.id]
                BY <2>1, <1>1 DEF Inv4
           <3>2 a.id \in Nat /\ b.id \in Nat
                BY <2>1, EventSetTypeAs DEF BlockIds
           <3>3 CASE a.id <= b.id
                BY <3>3, <2>1, <3>1, <1>1 DEF Inv5
           <3>4 CASE a.id >= b.id
                BY <3>4, <2>1, <3>1, <1>1 DEF Inv5
           <3> QED BY <3>3, <3>4, <3>2
      <2> QED BY <2>1 DEF Inv6
 <1> QED BY <1>1, PTL, Inv4proof, Inv5proof

LEMMA HashgraphInvproof == Spec => []HashgraphInv
  <1>1 ASSUME Inv1, Inv3, Inv6, TypeOK
       PROVE HashgraphInv
       <2>1 ASSUME NEW u \in EventSet, NEW e \in EventSet,
                   NEW p \in ProcessSet, NEW q \in ProcessSet,
                   NEW a \in EventSet, NEW b \in EventSet,
                   p \notin faulty, q \notin faulty, 
                   u.source = e.source, ~Path(e, u), ~Path(u, e),
                   a \in hashgraph[p][a.source][a.id],
                   b \in hashgraph[q][b.source][b.id],
                   StronglySees(a, u), StronglySees(b, e)
           PROVE FALSE
           <3>1 \E A \in SUBSET(EventSet): /\ Cardinality({i \in ProcessSet: (\E x \in A: x.source = i)}) > 2*f
                                           /\ \A x \in A: x \in hashgraph[p][x.source][x.id] /\ Sees(x, u)
                BY <2>1, <1>1 DEF Inv1
           <3>2 \E B \in SUBSET(EventSet): /\ Cardinality({i \in ProcessSet: (\E x \in B: x.source = i)}) > 2*f
                                           /\ \A x \in B: x \in hashgraph[q][x.source][x.id] /\ Sees(x, e)
               BY <2>1, <1>1 DEF Inv1
           <3>3 ASSUME NEW A \in SUBSET(EventSet), NEW B \in SUBSET(EventSet), 
                       Cardinality({i \in ProcessSet: (\E x \in A: x.source = i)}) > 2*f,
                       Cardinality({i \in ProcessSet: (\E x \in B: x.source = i)}) > 2*f,
                       \A x \in A: x \in hashgraph[p][x.source][x.id] /\ Sees(x, u),
                       \A x \in B: x \in hashgraph[q][x.source][x.id] /\ Sees(x, e)
                PROVE FALSE
                <4>1 \E w \in A, v \in B: w.source = v.source /\ w.source \notin faulty
                     BY <3>3, <1>1 DEF Inv3
                <4>2 ASSUME NEW w \in EventSet, NEW v \in EventSet, w \in A, v \in B, w.source = v.source, w.source \notin faulty
                     PROVE FALSE
                     <5>1 /\ w \in hashgraph[p][w.source][w.id] /\ Sees(w, u) 
                          /\ v \in hashgraph[q][v.source][v.id] /\ Sees(v, e)
                          BY <4>2, <3>3
                     <5>2 Path(w, v) \/ Path(v, w)
                          BY <4>2, <5>1, <1>1, <2>1 DEF Inv6
                     <5>3 Sees(v, u) \/ Sees(w, e)
                          BY <5>2, <5>1, Pslt6
                     <5>4 ASSUME Sees(v, u), Sees(v, e) PROVE FALSE
                          <6>1 CASE e.id <= u.id
                               BY <6>1, <5>4, <2>1, Pslt7
                          <6>2 CASE u.id <= e.id
                               BY <6>2, <5>4, <2>1, Pslt7
                          <6>3 u.id \in BlockIds /\ e.id \in BlockIds
                               BY <2>1, EventSetTypeAs
                          <6> QED BY <6>1, <6>2, <6>3 DEF BlockIds
                     <5>5 ASSUME Sees(w, e), Sees(w, u) PROVE FALSE
                          <6>1 CASE e.id <= u.id
                               BY <6>1, <5>5, <2>1, Pslt7
                          <6>2 CASE u.id <= e.id
                               BY <6>2, <5>5, <2>1, Pslt7
                          <6>3 u.id \in BlockIds /\ e.id \in BlockIds
                               BY <2>1, EventSetTypeAs
                          <6> QED BY <6>1, <6>2, <6>3 DEF BlockIds 
                     <5> QED BY <5>4, <5>5, <5>3, <5>1
                <4> QED BY <4>1, <4>2, <3>3
           <3> QED BY <3>1, <3>2, <3>3
      <2> QED BY <2>1 DEF HashgraphInv             
  <1> QED BY <1>1, PTL, Inv1proof, Inv3proof, Inv6proof, TypeOKproof

---------------------------------------------------------------------------

LEMMA WitnessInvproof == Spec => []WitnessInv
 <1>1 ASSUME Init, TypeOK 
      PROVE WitnessInv
      BY <1>1, WitnessSetTypeAs DEF Init, TypeOK, WitnessInv
 <1>2 ASSUME [Next]_vars, WitnessInv, TypeOK
      PROVE WitnessInv'
      <3>2 ASSUME NEW p \in ProcessSet, NEW q \in ProcessSet, NEW x \in BlockIds, NEW E \in SUBSET(EventSet), FaultyChangeHashgraphTn(p, q, x, E)
           PROVE WitnessInv'
           BY <3>2, <1>2 DEF TypeOK, FaultyChangeHashgraphTn, WitnessInv
      <3>3 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, NEW z \in EventSet, ReceiveEventTn(e, p, z)
           PROVE WitnessInv'
           BY <3>3, <1>2, WitnessSetTypeAs, EventSetTypeAs DEF TypeOK, ReceiveEventTn, WitnessInv
      <3>4 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, DecideWitnessTn(e, p)
           PROVE WitnessInv'
           <4>1 ASSUME NEW i \in ProcessSet, NEW a \in WitnessSet, i \notin faulty, a \in witnessDAG'[i][a.frame][a.source]
                PROVE a.event \in hashgraph[i][a.event.source][a.event.id] /\ \A b \in a.stronglysees: b \in witnessDAG'[i][b.frame][b.source]
                <5>1 ASSUME NEW b \in WitnessSet, b \in witnessDAG[i][b.frame][b.source]
                     PROVE b \in witnessDAG'[i][b.frame][b.source]
                     BY <5>1, WitnessSetTypeAs, <1>2, <4>1, <3>4 DEF TypeOK, DecideWitnessTn
                <5>2 CASE i = p /\ a.event = e
                     <6>1 \A b \in a.stronglysees: b \in witnessDAG'[i][b.frame][b.source]
                          BY <5>2, <3>4, WitnessSetTypeAs, <5>1, WitnessSetAs DEF DecideWitnessTn
                     <6>2 a.event \in hashgraph[i][a.event.source][a.event.id]
                          BY <5>2, <3>4 DEF DecideWitnessTn
                     <6> QED BY <6>1, <6>2
                <5>3 CASE i # p \/ a.event # e
                     <6>1 a \in witnessDAG[i][a.frame][a.source]
                          <7>1 CASE i # p
                               BY <5>3, WitnessSetTypeAs, <1>2, <7>1, <4>1, <3>4 DEF TypeOK, DecideWitnessTn
                          <7>2 CASE i = p /\ a.event # e
                               <8>1 a # WitnessOfEvent(e)
                                   BY <3>4, <7>2, Pslt4, WitnessSetTypeAs
                               <8> QED BY <5>3, WitnessSetTypeAs, <1>2, <7>2, <4>1, <3>4, <8>1 DEF TypeOK, DecideWitnessTn
                          <7> QED BY <7>1, <7>2, <5>3
                     <6> QED BY <6>1, <4>1, <1>2, WitnessSetTypeAs, <5>1 DEF WitnessInv
                <5> QED BY <5>2, <5>3
           <4>2 QED BY <4>1, <3>4 DEF WitnessInv, DecideWitnessTn
      <3>5 ASSUME UNCHANGED vars
           PROVE WitnessInv'
           BY <3>5, <1>2 DEF vars, WitnessInv
      <3>6 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, DecideFameTn(p, g, d)
           PROVE WitnessInv'
           BY <1>2, <3>6 DEF vars1, DecideFameTn, WitnessInv
      <3>7 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, VoteTn(p, g, d)
           PROVE WitnessInv'
           BY <1>2, <3>7 DEF vars1, VoteTn, WitnessInv
      <3>8 ASSUME NEW p \in ProcessSet, NEW u \in Frames, NEW g \in WitnessSet, DecideFrameTn(p, u)
           PROVE WitnessInv'
           BY <1>2, <3>8 DEF vars1, DecideFrameTn, WitnessInv
      <3> QED BY <3>2, <3>3, <3>4, <3>5, <1>2, <3>6, <3>7, <3>8 DEF Next 
 <1> QED BY <1>1, <1>2, PTL, TypeOKproof DEF Spec

---------------------------------------------------------------------------

THEOREM Safety
 <1>1 ASSUME Init, TypeOK 
      PROVE StronglySeenConsistency
      BY <1>1, WitnessSetTypeAs DEF Init, TypeOK, Genesis, StronglySeenConsistency
 <1>2 ASSUME [Next]_vars, StronglySeenConsistency, TypeOK, HashgraphInv', WitnessInv'
      PROVE StronglySeenConsistency'
      <3>2 ASSUME NEW p \in ProcessSet, NEW q \in ProcessSet, NEW x \in BlockIds, NEW E \in SUBSET(EventSet), FaultyChangeHashgraphTn(p, q, x, E)
           PROVE StronglySeenConsistency'
           BY <3>2, <1>2 DEF TypeOK, FaultyChangeHashgraphTn, StronglySeenConsistency
      <3>3 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, NEW z \in EventSet, ReceiveEventTn(e, p, z)
           PROVE StronglySeenConsistency'
           BY <3>3, <1>2 DEF TypeOK, ReceiveEventTn, StronglySeenConsistency
      <3>4 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, DecideWitnessTn(e, p)
           PROVE StronglySeenConsistency'
           <4>1 ASSUME NEW i \in ProcessSet, NEW j \in ProcessSet, NEW a \in WitnessSet, NEW b \in WitnessSet, NEW s \in WitnessSet, NEW l \in WitnessSet,
                i \notin faulty, j \notin faulty, a.frame = b.frame, a.source = b.source, s \in witnessDAG'[j][s.frame][s.source], b \in s.stronglysees,
                l \in witnessDAG'[i][l.frame][l.source], a \in l.stronglysees
                PROVE a = b
                     <5>1 a # b => a.event # b.event
                          BY WitnessSetAs, WitnessSetTypeAs, <4>1
                     <5>2 a.event = b.event
                          <6>1 a.event.source = b.event.source
                               BY <4>1, Pslt2
                          <6>2 ~Path(a.event, b.event) /\ ~Path(b.event, a.event)
                               BY <4>1, Pslt3
                          <6>3 StronglySees(l.event, a.event) /\ StronglySees(s.event, b.event)
                               BY <4>1, Pslt1
                          <6>4 l.event \in hashgraph'[i][l.event.source][l.event.id] /\ s.event \in hashgraph'[j][s.event.source][s.event.id]
                               BY <4>1, <1>2, <3>4 DEF WitnessInv, DecideWitnessTn
                          <6> QED BY <6>1, <6>2, <6>3, <6>4, <4>1, <1>2, <4>1, WitnessSetTypeAs, <3>4 DEF HashgraphInv, DecideWitnessTn
                     <5> QED BY <5>1, <5>2
           <4> QED BY <4>1, <3>4 DEF StronglySeenConsistency, DecideWitnessTn
      <3>5 ASSUME UNCHANGED vars
           PROVE StronglySeenConsistency'
           BY <3>5, <1>2 DEF vars, StronglySeenConsistency
      <3>6 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, DecideFameTn(p, g, d)
           PROVE StronglySeenConsistency'
           BY <1>2, <3>6 DEF vars1, DecideFameTn, StronglySeenConsistency
      <3>7 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, VoteTn(p, g, d)
           PROVE StronglySeenConsistency'
           BY <1>2, <3>7 DEF vars1, VoteTn, StronglySeenConsistency
      <3>8 ASSUME NEW p \in ProcessSet, NEW u \in Frames, NEW g \in WitnessSet, DecideFrameTn(p, u)
           PROVE StronglySeenConsistency'
           BY <1>2, <3>8 DEF vars1, DecideFrameTn, StronglySeenConsistency
      <3> QED BY <3>2, <3>3, <3>4, <3>5, <1>2, <3>6, <3>7, <3>8 DEF Next 
 <1> QED BY <1>1, <1>2, PTL, TypeOKproof, HashgraphInvproof, WitnessInvproof DEF Spec, Safety

---------------------------------------------------------------------------

LEMMA equalVar == Spec => []equalvar
<1>1 ASSUME Init
      PROVE equalvar
      <2>1 /\ VVOrdering!ProcessSet = ProcessSet
           /\ VVOrdering!Frames = Frames
         BY DEF  VVOrdering!ProcessSet, ProcessSet, VVOrdering!Frames, Frames
      <2> QED BY <1>1, <2>1 DEF Init, equalvar, VVOrdering!Init, VVOrdering!InitWitnessDAG
<1>2 ASSUME [Next]_vars, equalvar
      PROVE equalvar'
      <3>2 ASSUME NEW p \in ProcessSet, NEW q \in ProcessSet, NEW x \in BlockIds, NEW E \in SUBSET(EventSet), FaultyChangeHashgraphTn(p, q, x, E)
           PROVE equalvar'
           BY <3>2, <1>2 DEF FaultyChangeHashgraphTn, equalvar, VVOrdering!vars
      <3>3 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, NEW z \in EventSet, ReceiveEventTn(e, p, z)
           PROVE equalvar'
           BY <3>3, <1>2 DEF ReceiveEventTn, equalvar, VVOrdering!vars
      <3>4 ASSUME NEW p \in ProcessSet, NEW e \in EventSet, DecideWitnessTn(e, p)
           PROVE equalvar'
           BY <3>4, <1>2, WitnessSetAs, WitnessSetTypeAs DEF DecideWitnessTn, equalvar, VVOrdering!AddWitnessTn
      <3>5 ASSUME UNCHANGED vars
           PROVE equalvar'
           BY <3>5, <1>2 DEF vars, equalvar
      <3>6 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, DecideFameTn(p, g, d)
           PROVE equalvar'
           BY <1>2, <3>6 DEF vars1, DecideFameTn, equalvar, VVOrdering!DecideFameTn
      <3>7 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, VoteTn(p, g, d)
           PROVE equalvar'
           BY <1>2, <3>7 DEF vars1, VoteTn, equalvar, VVOrdering!VoteTn
      <3>8 ASSUME NEW p \in ProcessSet, NEW u \in Frames, NEW g \in WitnessSet, DecideFrameTn(p, u)
           PROVE equalvar'
           BY <1>2, <3>8 DEF vars1, DecideFrameTn, equalvar, VVOrdering!DecideFrameTn
      <3> QED BY <3>2, <3>3, <3>4, <3>5, <1>2, <3>6, <3>7, <3>8 DEF Next
 <1> QED BY <1>1, <1>2, PTL DEF Spec
 
LEMMA SpecPreservingThm == Spec => VVOrdering!Spec
 <1>1 Init => VVOrdering!Init
    BY DEF Init
 <1>2 ASSUME TypeOK, [Next]_vars, StronglySeenConsistency, StronglySeenConsistency', equalvar, equalvar' \*witnessDAG = VVWitnessDAG \*, witnessDAG' = VVWitnessDAG'
      PROVE VVOrdering!Next \/ UNCHANGED VVOrdering!vars
      <2>1 VVOrdering!UniqueStronglyseenAs /\ VVOrdering!UniqueStronglyseenAs'
            <3>1 /\ VVOrdering!ProcessSet = ProcessSet
                 /\ VVOrdering!Frames = Frames
               BY DEF  VVOrdering!ProcessSet, ProcessSet, VVOrdering!Frames, Frames
            <3> QED BY <1>2, <3>1 DEF StronglySeenConsistency, VVOrdering!UniqueStronglyseenAs, equalvar
      <2>2 ASSUME NEW p \in ProcessSet, NEW q \in ProcessSet, NEW  x \in BlockIds, NEW E \in SUBSET(EventSet), FaultyChangeHashgraphTn(p, q, x, E)
           PROVE VVOrdering!Next \/ UNCHANGED VVOrdering!vars
           BY <2>2 DEF FaultyChangeHashgraphTn, VVOrdering!vars
      <2>3 ASSUME NEW e \in EventSet, NEW p \in ProcessSet, NEW z \in EventSet, ReceiveEventTn(e, p, z)
           PROVE VVOrdering!Next \/ UNCHANGED VVOrdering!vars
           BY <2>3 DEF ReceiveEventTn, VVOrdering!vars
      <2>4 ASSUME NEW e \in EventSet, NEW p \in ProcessSet, DecideWitnessTn(e, p)
           PROVE VVOrdering!Next \/ UNCHANGED VVOrdering!vars
           <3>1 p \in VVOrdering!ProcessSet /\ WitnessOfEvent(e) \in WitnessSet /\ VVOrdering!AddWitnessTn(p, WitnessOfEvent(e)) /\ VVOrdering!Frames # {}
                BY  <2>4, frameAs, WitnessOfEventTypeAs DEF DecideWitnessTn, Frames, VVOrdering!ProcessSet, ProcessSet, VVOrdering!Frames, Frames
           <3> QED BY <3>1, <2>1 DEF VVOrdering!Next
      <2>5 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, DecideFameTn(p, g, d)
           PROVE VVOrdering!Next \/ UNCHANGED VVOrdering!vars
           <3>1 p \in VVOrdering!ProcessSet /\ d \in WitnessSet /\ g \in WitnessSet /\ VVOrdering!DecideFameTn(p, g, d) /\ VVOrdering!Frames # {}
                BY <2>5, frameAs DEF DecideFameTn, Frames, VVOrdering!ProcessSet, ProcessSet, VVOrdering!Frames, Frames
           <3> QED BY <3>1, <2>1 DEF VVOrdering!Next
      <2>6 ASSUME NEW p \in ProcessSet, NEW d \in WitnessSet, NEW g \in WitnessSet, VoteTn(p, g, d)
           PROVE VVOrdering!Next \/ UNCHANGED VVOrdering!vars
           <3>1 p \in VVOrdering!ProcessSet /\ d \in WitnessSet /\ g \in WitnessSet /\ VVOrdering!VoteTn(p, g, d) /\ VVOrdering!Frames # {}
                BY <2>6, frameAs DEF VoteTn, Frames, VVOrdering!ProcessSet, ProcessSet, VVOrdering!Frames, Frames
           <3> QED BY <3>1, <2>1 DEF VVOrdering!Next
      <2>7 ASSUME NEW p \in ProcessSet, NEW u \in Frames, NEW g \in WitnessSet, DecideFrameTn(p, u)
           PROVE VVOrdering!Next \/ UNCHANGED VVOrdering!vars
           <3>1 p \in VVOrdering!ProcessSet /\ g \in WitnessSet /\ VVOrdering!DecideFrameTn(p, u) /\ u \in VVOrdering!Frames
                BY <2>7, frameAs DEF DecideFrameTn, Frames, VVOrdering!ProcessSet, ProcessSet, VVOrdering!Frames, Frames
           <3> QED BY <3>1, <2>1 DEF VVOrdering!Next
      <2>8 ASSUME UNCHANGED vars
           PROVE VVOrdering!Next \/ UNCHANGED VVOrdering!vars
           BY <2>8 DEF vars, VVOrdering!vars
      <2> QED BY  <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <1>2 DEF Next
 <1> QED BY <1>1, <1>2, PTL, Safety, TypeOKproof, equalVar DEF Spec, VVOrdering!Spec
 
LEMMA HashgraphSafety == Spec => []Safety
   <1>1 Safety = VVOrdering!Safety
         BY DEF Safety, VVOrdering!Safety, VVOrdering!ProcessSet, ProcessSet, VVOrdering!Frames, Frames
   <1>2 Spec => []VVOrdering!Safety
         BY VVOrdering!safetyproof, SpecPreservingThm, fAs, rAs, cAs
   <1> QED BY <1>1, <1>2, VVOrdering!safetyproof, SpecPreservingThm, PTL DEF Safety, VVOrdering!Safety
   
=============================================================================
\* Modification History
\* Last modified Tue Dec 10 18:19:00 AEDT 2024 by pgho0778
\* Created Tue Dec 10 17:45:45 AEDT 2024 by pgho0778
