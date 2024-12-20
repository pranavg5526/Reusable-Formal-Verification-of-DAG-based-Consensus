----------------------- MODULE CordialMinersProofs -----------------------

EXTENDS CordialMinersSpecification,
        FiniteSets,
        Integers,
        Sequences,
        TLC,
        TLAPS

------------------------------------------------------------------------------------------------------------
Invariant1 == \A p \in Proc, r \in Rounds, o \in Proc: (p \notin faulty /\ dag[p][r][o].ratifiedVertex # "Nil") =>  \E A \in SUBSET(VertexSet) : /\ Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f 
                                                                                                                                                 /\ \A u \in A: u \in dag[p][u.round][u.source].vertices /\ Approves(u, dag[p][r][o].ratifiedVertex)

Invariant2 == Cardinality(faulty) <= f

Invariant3 == \A A \in SUBSET(VertexSet), B \in SUBSET(VertexSet) : /\ Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f
                                                                    /\ Cardinality({q \in Proc: (\E u \in B: u.source = q)}) = n-f
                                                                    => \E a \in A, b \in B: a.source = b.source /\ a.source \notin faulty


Invariant4 == \A p \in Proc, u \in VertexSet: p \notin faulty /\ u.source \notin faulty /\ u \in dag[p][u.round][u.source].vertices => u \in dag[u.source][u.round][u.source].vertices

Invariant5 == \A u \in VertexSet, v \in VertexSet : /\ u \in dag[u.source][u.round][u.source].vertices 
                                                    /\ v \in dag[v.source][v.round][v.source].vertices 
                                                    /\ u.source = v.source /\ u.source \notin faulty 
                                                    /\ u.round <= v.round 
                                                    => Observes(v, u)

Invariant6 == \A a \in VertexSet, b \in VertexSet, p \in Proc, q \in Proc: /\ p \notin faulty /\ a \in dag[p][a.round][a.source].vertices
                                                                           /\ q \notin faulty /\ b \in dag[q][b.round][b.source].vertices
                                                                           /\ a.source = b.source /\ a.source \notin faulty
                                                                           => Observes(a, b) \/ Observes(b, a)
------------------------------------------------------------------------------------------------------------

LEMMA Invariant1PrimeAs == Invariant1' = \A p \in Proc, r \in Rounds, o \in Proc: (p \notin faulty' /\ dag'[p][r][o].ratifiedVertex # "Nil") => \E A \in SUBSET(VertexSet):
                                                      /\ Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f
                                                      /\ \A u \in A: u \in dag'[p][u.round][u.source].vertices /\ Approves(u, dag'[p][r][o].ratifiedVertex)

LEMMA Invariant5PrimePlt == Invariant5' = \A u \in VertexSet, v \in VertexSet : (/\ u \in dag'[u.source][u.round][u.source].vertices 
                                                                                 /\ v \in dag'[v.source][v.round][v.source].vertices 
                                                                                 /\ u.source = v.source /\ u.source \notin faulty'
                                                                                 /\ u.round <= v.round) 
                                                                                  => Observes(v, u)

LEMMA TransitiveObserveAs == \A a \in VertexSet, b \in VertexSet, c \in VertexSet : Observes(a, b) /\ Observes(b, c) => Observes(a, c)

LEMMA CardinalityPlt == /\ Cardinality({}) = 0 
                        /\ \A S \in SUBSET(Nat) : Cardinality(S) \in Nat
                        /\ \A S \in SUBSET(Nat), p \in Nat: p \notin S => Cardinality(S \cup {p}) = Cardinality(S) + 1

LEMMA QouramIntersectPlt == \A X \in SUBSET(Nat), a \in Nat, b \in Nat: \A A \in SUBSET(X), B \in SUBSET(X), C \in SUBSET(X): /\ Cardinality(X) = a 
                                                                                                                              /\ 3*b < a 
                                                                                                                              /\ Cardinality(A) = a-b
                                                                                                                              /\ Cardinality(B) = a-b 
                                                                                                                              /\ Cardinality(C) <= b 
                                                                                                                                => (A \cap B) \cap (X\C) # {}

LEMMA ObservesPlt == \A u \in VertexSet: Observes(u, u)

LEMMA NatComparablePlt == \A a \in Nat, b \in Nat: /\ (a <= b) \/ (b <= a)
                                                   /\ (a <= b) => ~(b < a)

LEMMA DivProperty1Plt == ASSUME NEW y \in Nat, NEW x \in 0..5*y, x % 5 = 1
                 PROVE (x \div 5)+1 \in 1..y
                 
LEMMA DivProperty2Plt == ASSUME NEW y \in Nat, NEW x \in 0..5*y, x % 5 = 0, x>0
                  PROVE (x \div 5) \in 1..y
-------------------------------------------------------------------------------------------------------------

THEOREM TypeOKThm == Spec => []TypeOK
 <1>1 ASSUME Init 
      PROVE TypeOK
      BY <1>1, DVinVSAs DEF Init, TypeOK
 <1>2 ASSUME Next, TypeOK
      PROVE TypeOK'
      <2>1 ASSUME NEW s \in Proc, ProcessFailureTn(s)
           PROVE TypeOK'
           BY <2>1, <1>2 DEF ProcessFailureTn, TypeOK
      <2>2 ASSUME NEW s \in Proc, NEW v \in VertexSet, AddVertexTn(s, v)
           PROVE TypeOK'
           <3>1 ASSUME NEW a \in Proc, NEW b \in Proc, NEW r \in Rounds
                PROVE dag'[a][r][b] \in [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]
                <4>1 dag[a][r][b] \in [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]
                     <5>1 dag[a] \in [Rounds -> [Proc -> [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]]]
                          BY <1>2, <3>1 DEF TypeOK
                     <5>2 dag[a][r] \in [Proc -> [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]]
                          BY <5>1, <3>1
                     <5>3 dag[a][r][b] \in [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]
                          BY <5>2, <3>1
                     <5> QED BY <5>3
                <4>2 CASE a = s /\ r = v.round /\ b = v.source
                     <5>1 dag'[a][r][b] = [vertices |-> dag[a][r][b].vertices \cup {v}, ratifiedVertex |-> dag[a][r][b].ratifiedVertex]
                          BY <4>2, <3>1, <2>2 DEF AddVertexTn
                     <5>2 dag[a][r][b].vertices \cup {v} \in SUBSET(VertexSet) /\ dag[a][r][b].ratifiedVertex \in VertexSet \cup {"Nil"}
                          BY <4>1, <2>2
                     <5> QED BY <5>1, <5>2
                <4>3 CASE ~(a = s /\ r = v.round /\ b = v.source)
                     <5>1 dag'[a][r][b] = dag[a][r][b]
                          BY <4>3, <3>1, <2>2 DEF AddVertexTn
                     <5> QED BY <5>1, <4>1
                <4> QED BY <4>3, <4>2
           <3> QED BY <3>1, <1>2, <2>2 DEF TypeOK, AddVertexTn
      <2>3 ASSUME NEW s \in Proc, NEW B \in SUBSET(VertexSet), NEW v \in VertexSet, RatifyVertexTn(s, v, B)
           PROVE TypeOK'
           <3>1 ASSUME NEW a \in Proc, NEW b \in Proc, NEW r \in Rounds
                PROVE dag'[a][r][b] \in [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]
                <4>1 dag[a][r][b] \in [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]
                     <5>1 dag[a] \in [Rounds -> [Proc -> [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]]]
                          BY <1>2, <3>1 DEF TypeOK
                     <5>2 dag[a][r] \in [Proc -> [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]]
                          BY <5>1, <3>1
                     <5>3 dag[a][r][b] \in [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]
                          BY <5>2, <3>1
                     <5> QED BY <5>3
                <4>2 CASE a = s /\ r = v.round /\ b = v.source
                     <5>1 dag'[a][r][b] = [vertices |-> dag[a][r][b].vertices, ratifiedVertex |-> v]
                          BY <4>2, <3>1, <2>3 DEF RatifyVertexTn
                     <5>2 dag[a][r][b].vertices \in SUBSET(VertexSet) /\ dag[a][r][b].ratifiedVertex \in VertexSet \cup {"Nil"}
                          BY <4>1, <2>2
                     <5> QED BY <5>1, <5>2
                <4>3 CASE ~(a = s /\ r = v.round /\ b = v.source)
                     <5>1 dag'[a][r][b] = dag[a][r][b]
                          BY <4>3, <3>1, <2>3 DEF RatifyVertexTn
                     <5> QED BY <5>1, <4>1
                <4> QED BY <4>2, <4>3
           <3> QED BY <3>1, <1>2, <2>3 DEF TypeOK, RatifyVertexTn
      <2> QED BY <2>1, <2>2, <2>3, <1>2 DEF Next
 <1>3 ASSUME UNCHANGED vars, TypeOK
      PROVE TypeOK'
      BY <1>3 DEF vars, TypeOK
 <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec

LEMMA Invariant1Lm == Spec => []Invariant1
 <1>1 ASSUME Init
      PROVE Invariant1
      BY <1>1 DEF Init, Invariant1
 <1>2 ASSUME Next, Invariant1, TypeOK, TypeOK'
      PROVE Invariant1'
      <2>1 ASSUME NEW p \in Proc, NEW r \in Rounds, NEW o \in Proc, p \notin faulty',  dag'[p][r][o].ratifiedVertex # "Nil"
           PROVE \E A \in SUBSET(VertexSet) : /\ Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f
                                              /\ \A u \in A: u \in dag'[p][u.round][u.source].vertices /\ Approves(u, dag'[p][r][o].ratifiedVertex)
           <3>1 ASSUME NEW s \in Proc, ProcessFailureTn(s)
                PROVE \E A \in SUBSET(VertexSet) : /\ Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f
                                                   /\ \A u \in A: u \in dag'[p][u.round][u.source].vertices /\ Approves(u, dag'[p][r][o].ratifiedVertex)
                <4>1 p \notin faulty
                     BY <2>1, <3>1 DEF ProcessFailureTn
                <4>2 dag = dag'
                     BY <3>1 DEF ProcessFailureTn
                <4> QED BY <4>1, <4>2, <2>1, <1>2 DEF Invariant1
           <3>2 ASSUME NEW s \in Proc, NEW v \in VertexSet, AddVertexTn(s, v)
                PROVE \E A \in SUBSET(VertexSet) : /\ Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f 
                                                   /\ \A u \in A: u \in dag'[p][u.round][u.source].vertices /\ Approves(u, dag'[p][r][o].ratifiedVertex)
                <4>1 p \notin faulty
                     BY <2>1, <3>2 DEF AddVertexTn
                <4>2 dag[p][r][o].ratifiedVertex = dag'[p][r][o].ratifiedVertex
                     BY <2>1, <3>2 DEF AddVertexTn
                <4>3 ASSUME NEW u \in VertexSet
                     PROVE dag[p][u.round][u.source].vertices  \in SUBSET(dag'[p][u.round][u.source].vertices)
                     <5>4 u.round \in Rounds /\ u.source \in Proc
                          BY <4>3, VertexSetTypeAs
                     <5> QED BY <5>4, <2>1, <3>2 DEF AddVertexTn
                <4>4 \E A \in SUBSET(VertexSet) : /\ Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f 
                                                  /\ \A u \in A: u \in dag[p][u.round][u.source].vertices /\ Approves(u, dag[p][r][o].ratifiedVertex)
                     BY <4>1, <4>2, <2>1, <1>2 DEF Invariant1
                <4>5 ASSUME NEW A \in SUBSET(VertexSet), Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f, \A u \in A: u \in dag[p][u.round][u.source].vertices /\ Approves(u, dag[p][r][o].ratifiedVertex)
                     PROVE \A u \in A: u \in dag'[p][u.round][u.source].vertices /\ Approves(u, dag'[p][r][o].ratifiedVertex)
                     BY <4>3, <4>2, <4>5
                <4> QED BY <4>4, <4>5 
           
           <3>3 ASSUME NEW s \in Proc, NEW B \in SUBSET(VertexSet), NEW v \in VertexSet, RatifyVertexTn(s, v, B)
                PROVE \E A \in SUBSET(VertexSet) : /\ Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f
                                                   /\ \A u \in A: u \in dag'[p][u.round][u.source].vertices /\ Approves(u, dag'[p][r][o].ratifiedVertex)
                <4>1 CASE p = s /\ v.round = r /\ v.source = o
                     <5>1 Cardinality({q \in Proc: (\E u \in B: u.source = q)}) = n-f
                          BY <4>1, <3>3 DEF RatifyVertexTn
                     <5>2 dag'[p][r][o].ratifiedVertex = v
                          BY <4>1, <3>3 DEF RatifyVertexTn
                     <5>3 ASSUME NEW u \in VertexSet
                          PROVE dag[p][u.round][u.source].vertices  = dag'[p][u.round][u.source].vertices
                          <6>1 u.round \in Rounds /\ u.source \in Proc
                               BY <5>3, VertexSetTypeAs
                          <6> QED BY <6>1, <2>1, <3>3 DEF RatifyVertexTn
                     <5>4 \A u \in B: u \in dag'[p][u.round][u.source].vertices /\ Approves(u, dag'[p][r][o].ratifiedVertex)
                          BY <5>2, <5>3, <4>1, <3>3 DEF RatifyVertexTn
                     <5> QED BY <3>3, <5>4, <5>1
                <4>2 CASE ~(p = s /\ v.round = r /\ v.source = o)
                     <5>1 p \notin faulty
                          BY <2>1, <3>3 DEF RatifyVertexTn
                     <5>2 dag[p][r][o].ratifiedVertex = dag'[p][r][o].ratifiedVertex
                          BY <2>1, <3>3, <4>2 DEF RatifyVertexTn
                     <5>3 ASSUME NEW u \in VertexSet
                          PROVE dag[p][u.round][u.source].vertices  \in SUBSET(dag'[p][u.round][u.source].vertices)
                          <6>1 u.round \in Rounds /\ u.source \in Proc
                               BY <5>3, VertexSetTypeAs
                          <6> QED BY <6>1, <2>1, <3>3 DEF RatifyVertexTn
                     <5>4 \E A \in SUBSET(VertexSet) : /\ Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f 
                                                       /\ \A u \in A: u \in dag[p][u.round][u.source].vertices /\ Approves(u, dag[p][r][o].ratifiedVertex)
                          BY <5>1, <5>2, <2>1, <1>2 DEF Invariant1
                     <5>5 ASSUME NEW A \in SUBSET(VertexSet), Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f, \A u \in A: u \in dag[p][u.round][u.source].vertices /\ Approves(u, dag[p][r][o].ratifiedVertex)
                          PROVE \A u \in A: u \in dag'[p][u.round][u.source].vertices /\ Approves(u, dag'[p][r][o].ratifiedVertex)
                          BY <5>3, <5>2, <5>5
                     <5> QED BY <5>4, <5>5 
                <4> QED BY <4>1, <4>2
          <3> QED BY <3>1, <3>2, <3>3, <1>2, <2>1 DEF Next
      <2> QED BY <2>1, Invariant1PrimeAs DEF Invariant1
 <1>3 ASSUME Invariant1, UNCHANGED vars
      PROVE Invariant1'
      BY<1>3, Invariant1PrimeAs DEF Invariant1, vars
 <1> QED BY <1>1, <1>2, <1>3, TypeOKThm, PTL DEF Spec

LEMMA Invariant2Lm == Spec => []Invariant2
 <1>1 ASSUME Init 
      PROVE Invariant2
      BY <1>1, CardinalityPlt, fAs DEF Init, Invariant2
 <1>2 ASSUME Next, Invariant2, TypeOK
      PROVE Invariant2'
      <2>1 ASSUME NEW p \in Proc, ProcessFailureTn(p)
           PROVE Cardinality(faulty') <= f
           <3>1 Cardinality(faulty') = Cardinality(faulty)+1
                <5>1 faulty \in SUBSET(Nat)
                          <6>1 faulty \in SUBSET(Proc)
                               BY <1>2 DEF TypeOK
                          <6> QED BY <6>1, ProcType
                <5>2 p \in Nat
                     BY <2>1, ProcType
                <5> QED BY <5>1, <5>2, <2>1, CardinalityPlt DEF ProcessFailureTn
           <3>2 Cardinality(faulty)+1 <= f
                <4>1 Cardinality(faulty) \in Nat /\ f \in Nat
                     <5>1 faulty \in SUBSET(Nat)
                          <6>1 faulty \in SUBSET(Proc)
                               BY <1>2 DEF TypeOK
                          <6> QED BY <6>1, ProcType
                     <5> QED BY <5>1, CardinalityPlt, fAs
                <4>2 Cardinality(faulty) < f
                     BY <2>1 DEF ProcessFailureTn
                <4> QED BY <4>1, <4>2
           <3> QED BY <3>1, <3>2
      <2>2 ASSUME  NEW s \in Proc, NEW v \in VertexSet, AddVertexTn(s, v)
           PROVE Cardinality(faulty') <= f
           BY <2>2, <1>2 DEF AddVertexTn, Invariant2
      <2>3 ASSUME NEW s \in Proc, NEW B \in SUBSET(VertexSet), NEW v \in VertexSet, RatifyVertexTn(s, v, B)
           PROVE Cardinality(faulty') <= f
           BY <2>3, <1>2 DEF RatifyVertexTn, Invariant2
      <2> QED BY <2>1, <2>2, <2>3, <1>2 DEF Next, Invariant2
 <1>3 ASSUME UNCHANGED vars, Invariant2
      PROVE Invariant2'
      BY <1>3 DEF vars, Invariant2
 <1> QED BY <1>1, <1>2, <1>3, PTL, TypeOKThm DEF Spec

LEMMA Invariant3Lm == Spec => []Invariant3
 <1>2 ASSUME Invariant2, TypeOK
      PROVE Invariant3
      <2>1 ASSUME NEW A \in SUBSET(VertexSet), NEW B \in SUBSET(VertexSet), Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f, Cardinality({q \in Proc: (\E u \in B: u.source = q)}) = n-f
           PROVE \E a \in A, b \in B: a.source = b.source /\ a.source \notin faulty
           <3>1 {q \in Proc: (\E u \in A: u.source = q)} \in SUBSET(Proc) /\ {q \in Proc: (\E u \in B: u.source = q)} \in SUBSET(Proc)
                OBVIOUS
           <3>2 faulty \in SUBSET(Proc) /\ Cardinality(faulty) <= f
                BY <1>2 DEF TypeOK, Invariant2
           <3>3 ({q \in Proc: (\E u \in A: u.source = q)} \cap {q \in Proc: (\E u \in B: u.source = q)}) \cap (Proc\faulty) # {}
                BY <3>1, <3>2, <2>1, nAs, FailureBoundAs, QouramIntersectPlt, ProcType
           <3> QED BY <3>3
      <2> QED BY <2>1 DEF Invariant3
 <1> QED BY  <1>2, PTL, Invariant2Lm, TypeOKThm

LEMMA Invariant4Lm == Spec => []Invariant4
 <1>1 ASSUME Init
      PROVE Invariant4
      <2>1 ASSUME NEW p \in Proc, NEW u \in VertexSet, u.source \notin faulty, p \notin faulty, u \in dag[p][u.round][u.source].vertices
           PROVE u \in dag[u.source][u.round][u.source].vertices
           <3>1 CASE u.round = 0
                <4>2 dag[p][u.round][u.source].vertices = {DummyVertex(u.source)} /\ dag[u.source][u.round][u.source].vertices = {DummyVertex(u.source)}
                     BY <3>1, <2>1, <1>1, VertexSetTypeAs DEF Init
                <4> QED BY <4>2, <2>1
           <3>2 CASE u.round # 0
                <4>1 dag[p][u.round][u.source].vertices = {}
                     BY <3>2, <1>1, VertexSetTypeAs DEF Init
                <4> QED BY <4>1, <2>1
           <3> QED BY <3>1, <3>2
      <2> QED BY <2>1 DEF Invariant4
 <1>2 ASSUME Next, Invariant4
      PROVE Invariant4'
      <2>1 ASSUME NEW p \in Proc, NEW u \in VertexSet, u.source \notin faulty', p \notin faulty', u \in dag'[p][u.round][u.source].vertices
           PROVE u \in dag'[u.source][u.round][u.source].vertices
           <3>1 ASSUME NEW s \in Proc, ProcessFailureTn(s)
                PROVE u \in dag'[u.source][u.round][u.source].vertices
                <4>1 p \notin faulty /\ u.source \notin faulty
                     BY <2>1, <3>1 DEF ProcessFailureTn
                <4>2 dag = dag'
                     BY <3>1 DEF ProcessFailureTn
                <4> QED BY <4>1, <4>2, <2>1, <1>2 DEF Invariant4
           <3>2 ASSUME NEW s \in Proc, NEW v \in VertexSet, AddVertexTn(s, v)
                PROVE u \in dag'[u.source][u.round][u.source].vertices
                <4>1 dag[u.source][u.round][u.source].vertices  \in SUBSET(dag'[u.source][u.round][u.source].vertices)
                     <5>4 u.round \in Rounds /\ u.source \in Proc
                          BY VertexSetTypeAs
                     <5> QED BY <5>4, <2>1, <3>2 DEF AddVertexTn
                <4>2 CASE p = s /\ u = v /\ p # u.source
                     <5>1 u \in dag[u.source][u.round][u.source].vertices
                          BY <4>2, <2>1, <3>2 DEF AddVertexTn
                     <5> QED BY <5>1, <4>1
                <4>3 CASE p = u.source
                     BY <4>3, <2>1
                <4>4 CASE p # s \/ u.round # v.round \/ u.source # v.source
                     <5>1 dag'[p][u.round][u.source].vertices = dag[p][u.round][u.source].vertices
                          BY <4>4, <3>2, <2>1, VertexSetTypeAs DEF AddVertexTn
                     <5> QED BY <5>1, <3>2, <2>1, <1>2, <4>1 DEF Invariant4, AddVertexTn
                <4>5 CASE ~(p # s \/ u.round # v.round \/ u.source # v.source) /\ u # v
                     <5>1 dag'[p][u.round][u.source].vertices = dag[p][u.round][u.source].vertices \cup {v}
                          BY <4>5, <3>2, <2>1, VertexSetTypeAs DEF AddVertexTn
                     <5> QED BY <5>1, <3>2, <2>1, <1>2, <4>1, <4>5 DEF Invariant4, AddVertexTn
                <4>  QED BY <4>4, <4>2, <4>3, <4>5
           <3>3 ASSUME NEW s \in Proc, NEW B \in SUBSET(VertexSet), NEW v \in VertexSet, RatifyVertexTn(s, v, B)
                PROVE u \in dag'[u.source][u.round][u.source].vertices
                <4>1 dag[p][u.round][u.source].vertices  = dag'[p][u.round][u.source].vertices
                     BY <2>1, <3>3, VertexSetTypeAs DEF RatifyVertexTn
                <4>2 dag[u.source][u.round][u.source].vertices  = dag'[u.source][u.round][u.source].vertices
                     BY <2>1, <3>3, VertexSetTypeAs DEF RatifyVertexTn
                <4>3 faulty' = faulty
                     BY <3>3 DEF RatifyVertexTn
                <4> QED BY <4>1, <4>2, <4>3, <2>1, <1>2 DEF Invariant4
           <3> QED BY <3>1, <3>2, <3>3, <1>2, <2>1 DEF Next
      <2> QED BY <2>1 DEF Invariant4
 <1>3 ASSUME UNCHANGED vars, Invariant4
      PROVE Invariant4'
      BY <1>3 DEF vars, Invariant4
 <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec
 
LEMMA Invariant5Lm == Spec => []Invariant5
 <1>1 ASSUME Init 
      PROVE Invariant5
      <2>1 ASSUME NEW u \in VertexSet, NEW v \in VertexSet, u \in dag[u.source][u.round][u.source].vertices, v \in dag[v.source][v.round][v.source].vertices, u.source = v.source, u.source \notin faulty, u.round <= v.round 
           PROVE Observes(v, u)
           <3>1 CASE u.round = 0 /\ v.round = 0
                <4>1 u = DummyVertex(u.source) /\ v = DummyVertex(v.source)
                     BY <2>1, <1>1, VertexSetTypeAs DEF Init
                <4>2 u \in VertexSet
                    BY <4>1, DVinVSAs 
                <4> QED BY <4>1, <2>1, <4>2, ObservesPlt, VertexSetTypeAs
           <3>2 CASE u.round  # 0 \/ v.round # 0
                <4>1 dag[u.source][u.round][u.source].vertices = {} \/ dag[v.source][v.round][v.source].vertices = {}
                     BY <3>2, <1>1, VertexSetTypeAs DEF Init
                <4> QED BY <4>1, <2>1 DEF Invariant5
           <3> QED BY <3>1, <3>2
      <2> QED BY <2>1 DEF Invariant5
  <1>2 ASSUME Next, Invariant5, TypeOK
      PROVE Invariant5'
      <2>1 ASSUME NEW u \in VertexSet, NEW v \in VertexSet, u \in dag'[u.source][u.round][u.source].vertices, v \in dag'[v.source][v.round][v.source].vertices, u.source = v.source, u.source \notin faulty', u.round <= v.round
           PROVE Observes(v, u)
           <3>1 ASSUME NEW s \in Proc, ProcessFailureTn(s)
                PROVE Observes(v, u)
                <4>1 u.source \notin faulty 
                     BY <2>1, <3>1 DEF ProcessFailureTn
                <4>2 dag = dag'
                     BY <3>1 DEF ProcessFailureTn
                <4> QED BY <4>1, <4>2, <2>1, <1>2 DEF Invariant5
           <3>2 ASSUME NEW s \in Proc, NEW z \in VertexSet, AddVertexTn(s, z)
                PROVE Observes(v, u)
                <4>1 u.source \notin faulty
                     BY <3>2, <2>1 DEF AddVertexTn
                <4>2 CASE u = v
                     BY <2>1, <4>2, ObservesPlt
                <4>3 CASE u # v
                     <5>1 CASE u.source # s
                          <6>1 dag'[u.source][u.round][u.source].vertices = dag[u.source][u.round][u.source].vertices /\ dag'[v.source][v.round][v.source].vertices = dag[v.source][v.round][v.source].vertices
                               BY <5>1, <2>1, <3>2, VertexSetTypeAs, <1>2 DEF AddVertexTn, TypeOK
                          <6> QED BY <6>1, <4>1, <1>2, <2>1 DEF Invariant5
                     <5>2 CASE u.source = s
                          <6>1 CASE u = z
                               <7>1 v \in dag[v.source][v.round][v.source].vertices  => v.round < u.round
                                    BY <2>1, <3>2, <4>1, <5>2, <6>1, <5>2 DEF AddVertexTn
                               <7>2 v \in dag[v.source][v.round][v.source].vertices
                                    <8>1 CASE v.round = u.round
                                         <9>1 dag[v.source][v.round][v.source].vertices = {}
                                              BY <8>1, <5>2, <6>1, <2>1, <4>1, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9>2 dag'[v.source][v.round][v.source].vertices = {u}
                                              BY <9>1, <8>1, <5>2, <6>1, <2>1, <4>1, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9> QED BY <9>2, <4>3, <2>1
                                    <8>2 CASE v.round # u.round
                                         <9>1 dag[v.source][v.round][v.source].vertices = dag'[v.source][v.round][v.source].vertices
                                              BY <8>2, <6>1, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9> QED BY <9>1, <2>1
                                    <8> QED BY <8>1, <8>2 
                               <7> QED BY <7>1, <7>2, <2>1, NatComparablePlt, VertexSetTypeAs, RoundType
                          <6>2 CASE v = z
                               <7>1 u \in dag[u.source][u.round][u.source].vertices  => Observes(v, u)
                                    BY <2>1, <3>2, <4>1, <5>2, <6>2, <5>2 DEF AddVertexTn
                               <7>2 u \in dag[u.source][u.round][u.source].vertices
                                    <8>1 CASE v.round = u.round
                                         <9>1 dag[u.source][u.round][u.source].vertices = {}
                                              BY <8>1, <5>2, <6>2, <2>1, <4>1, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9>2 dag'[u.source][u.round][u.source].vertices = {v}
                                              BY <9>1, <8>1, <5>2, <6>2, <2>1, <4>1, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9> QED BY <9>2, <4>3, <2>1
                                    <8>2 CASE v.round # u.round
                                         <9>1 dag[u.source][u.round][u.source].vertices = dag'[u.source][u.round][u.source].vertices
                                              BY <8>2, <6>2, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9> QED BY <9>1, <2>1
                                    <8> QED BY <8>1, <8>2 
                               <7> QED BY <7>1, <7>2, <2>1, NatComparablePlt, VertexSetTypeAs, RoundType
                          <6>3 CASE v # z /\ u # z
                               <7>1 u \in dag[u.source][u.round][u.source].vertices
                                    <8>1 CASE z.round = u.round /\ z.source = u.source
                                         <9>1 dag[u.source][u.round][u.source].vertices = {}
                                              BY <8>1, <5>2, <6>3, <2>1, <4>1, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9>2 dag'[u.source][u.round][u.source].vertices = {z}
                                              BY <9>1, <8>1, <5>2, <6>3, <2>1, <4>1, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9> QED BY <9>2, <6>3, <2>1
                                    <8>2 CASE z.round # u.round \/ z.source # u.source
                                         <9>1 dag[u.source][u.round][u.source].vertices = dag'[u.source][u.round][u.source].vertices
                                              BY <8>2, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9> QED BY <9>1, <2>1
                                    <8> QED BY <8>1, <8>2 
                               <7>2 v \in dag[v.source][v.round][v.source].vertices
                                    <8>1 CASE z.round = v.round /\ z.source = v.source
                                         <9>1 dag[v.source][v.round][v.source].vertices = {}
                                              BY <8>1, <5>2, <6>3, <2>1, <4>1, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9>2 dag'[v.source][v.round][v.source].vertices = {z}
                                              BY <9>1, <8>1, <5>2, <6>3, <2>1, <4>1, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9> QED BY <9>2, <6>3, <2>1
                                    <8>2 CASE z.round # v.round \/ z.source # v.source
                                         <9>1 dag[v.source][v.round][v.source].vertices = dag'[v.source][v.round][v.source].vertices
                                              BY <8>2, <3>2, VertexSetTypeAs DEF AddVertexTn
                                         <9> QED BY <9>1, <2>1
                                    <8> QED BY <8>1, <8>2 
                              <7> QED BY <7>1, <7>2, <4>1, <2>1, <1>2 DEF Invariant5
                          <6> QED BY <6>1, <6>2, <6>3
                     <5> QED BY <5>1, <5>2
                <4> QED BY <4>2, <4>3
           <3>3 ASSUME NEW s \in Proc, NEW B \in SUBSET(VertexSet), NEW z \in VertexSet, RatifyVertexTn(s, z, B)
                PROVE Observes(v, u)
                <4>1 dag'[u.source][u.round][u.source].vertices = dag[u.source][u.round][u.source].vertices
                     BY <2>1, <3>3, VertexSetTypeAs DEF RatifyVertexTn
                <4>2 dag'[v.source][v.round][v.source].vertices = dag[v.source][v.round][v.source].vertices
                     BY <2>1, <3>3, VertexSetTypeAs DEF RatifyVertexTn
                <4>3 faulty' = faulty
                     BY <3>3 DEF RatifyVertexTn
                <4> QED BY <4>1, <4>2, <4>3, <2>1, <1>2 DEF Invariant5
           <3> QED BY <3>1, <3>2, <3>3, <1>2 DEF Next
      <2> QED BY <2>1, Invariant5PrimePlt DEF Invariant5
 <1>3 ASSUME UNCHANGED vars, Invariant5
      PROVE Invariant5'
      BY <1>3, Invariant5PrimePlt DEF vars, Invariant5
 <1> QED BY <1>1, <1>2, <1>3, PTL, TypeOKThm DEF Spec

LEMMA Invariant6Lm == Spec => []Invariant6
 <1>1 ASSUME Invariant4, Invariant5
      PROVE Invariant6
      <2>1 ASSUME NEW a \in VertexSet, NEW  b \in VertexSet, NEW p \in Proc, NEW q \in Proc, p \notin faulty, a \in dag[p][a.round][a.source].vertices, q \notin faulty, b \in dag[q][b.round][b.source].vertices, a.source = b.source, a.source \notin faulty
           PROVE Observes(a, b) \/ Observes(b, a)
           <3>1 a \in dag[a.source][a.round][a.source].vertices /\ b \in dag[b.source][b.round][b.source].vertices
                BY <2>1, <1>1 DEF Invariant4
           <3>2 a.round \in Nat /\ b.round \in Nat
                BY <2>1, VertexSetTypeAs, RoundType
           <3>3 CASE a.round <= b.round
                BY <3>3, <2>1, <3>1, <1>1 DEF Invariant5
           <3>4 CASE a.round >= b.round
                BY <3>4, <2>1, <3>1, <1>1 DEF Invariant5
           <3> QED BY <3>3, <3>4, <3>2, NatComparablePlt
      <2> QED BY <2>1 DEF Invariant6
 <1> QED BY <1>1, PTL, Invariant4Lm, Invariant5Lm

THEOREM SafetyThm == Spec => []SafetyInv
 <1>1 ASSUME Init
      PROVE SafetyInv
      BY <1>1 DEF Init, SafetyInv
 <1>2 ASSUME Next, SafetyInv, TypeOK, TypeOK', Invariant1, Invariant3, Invariant6
      PROVE SafetyInv'
      <2>1 ASSUME NEW p \in Proc, NEW q \in Proc, NEW r \in Rounds, NEW o \in Proc, p \notin faulty', q \notin faulty', dag'[p][r][o].ratifiedVertex # "Nil", dag'[q][r][o].ratifiedVertex # "Nil"
           PROVE dag'[p][r][o].ratifiedVertex = dag'[q][r][o].ratifiedVertex
           <3>1 ASSUME NEW s \in Proc, ProcessFailureTn(s)
                PROVE dag'[p][r][o].ratifiedVertex = dag'[q][r][o].ratifiedVertex
                <4>1 p \notin faulty /\ q \notin faulty
                     BY <2>1, <3>1 DEF ProcessFailureTn
                <4>2 dag = dag'
                     BY <3>1 DEF ProcessFailureTn
                <4> QED BY <4>1, <4>2, <2>1, <1>2 DEF SafetyInv
           
           <3>2 ASSUME NEW s \in Proc, NEW v \in VertexSet, AddVertexTn(s, v)
                PROVE dag'[p][r][o].ratifiedVertex = dag'[q][r][o].ratifiedVertex
                <4>1 ASSUME NEW t \in Proc
                     PROVE dag'[t][r][o].ratifiedVertex = dag[t][r][o].ratifiedVertex
                     <5>1 CASE t = s /\ v.round = r /\ v.source = o
                          BY <5>1, <3>2, <2>1, <1>2 DEF AddVertexTn, TypeOK
                     <5>2 CASE ~(t = s /\ v.round = r /\ v.source = o)
                          BY <4>1, <5>2, <3>2, <2>1, <1>2 DEF AddVertexTn, TypeOK
                     <5> QED BY <5>1, <5>2
                <4>2 faulty = faulty'
                     BY <3>2 DEF AddVertexTn
                <4>3 dag'[p][r][o].ratifiedVertex = dag[p][r][o].ratifiedVertex /\ dag'[q][r][o].ratifiedVertex = dag[q][r][o].ratifiedVertex
                     BY <4>1, <2>1
                <4> QED BY <4>1, <4>3, <2>1, <4>2, <1>2 DEF SafetyInv
           
           <3>3 ASSUME NEW s \in Proc, NEW A \in SUBSET(VertexSet), NEW v \in VertexSet, RatifyVertexTn(s, v, A), Invariant1, Invariant3, Invariant6
                PROVE dag'[p][r][o].ratifiedVertex = dag'[q][r][o].ratifiedVertex
                <4>1 CASE s = p /\ r = v.round /\  o = v.source
                     <5>1 CASE p = q
                          BY <5>1
                     <5>2 CASE p # q
                          <6>1 dag[q][r][o] = dag'[q][r][o] /\ faulty = faulty' /\ dag'[p][r][o].ratifiedVertex = v
                               BY <5>2, <4>1, <3>3, <2>1, <1>2 DEF RatifyVertexTn, TypeOK
                          <6>2 dag[q][r][o].ratifiedVertex # "Nil" /\ q \notin faulty /\ q \in Proc /\ r \in Rounds /\ o \in Proc
                               BY <6>1, <2>1, <1>2 DEF TypeOK
                          <6>3 \E B \in SUBSET(VertexSet): Cardinality({t \in Proc: (\E u \in B: u.source = t)}) = n-f /\ \A u \in B: u \in dag[q][u.round][u.source].vertices /\ Approves(u, dag[q][r][o].ratifiedVertex)
                               BY <6>2, <1>2, <2>1, <3>3 DEF Invariant1
                          <6>4 Cardinality({t \in Proc: (\E u \in A: u.source = t)}) = n-f /\ \A u \in A: u \in dag[p][u.round][u.source].vertices /\ Approves(u, v)
                               BY <3>3, <4>1 DEF RatifyVertexTn
                          <6>5 ASSUME NEW B \in SUBSET(VertexSet), Cardinality({t \in Proc: (\E u \in B: u.source = t)}) = n-f, \A u \in B: u \in dag[q][u.round][u.source].vertices /\ Approves(u, dag[q][r][o].ratifiedVertex)
                               PROVE v = dag[q][r][o].ratifiedVertex
                               <7>1 \E a \in A, b \in B: a.source = b.source /\ a.source \notin faulty \*/\ a \in dag[p][a.round][a.source].vertices /\ Approves(a, v) /\ b \in dag[q][b.round][b.source].vertices /\ Approves(b, dag[q][r][o].ratifiedVertex)
                                    BY <6>5, <6>4, <1>2, <3>3 DEF Invariant3
                               <7>2 ASSUME NEW a \in A, NEW b \in B, a.source = b.source /\ a.source \notin faulty
                                    PROVE  v = dag[q][r][o].ratifiedVertex
                                    <8>1 Approves(a, v) /\ Approves(b, dag[q][r][o].ratifiedVertex)
                                         BY <6>5, <7>2, <6>4
                                    <8>2 b \in dag[q][b.round][b.source].vertices /\ a \in dag[p][a.round][a.source].vertices
                                         BY <6>5, <7>2, <6>4
                                    <8>3 a \in VertexSet /\ b \in VertexSet /\ dag[q][r][o].ratifiedVertex \in VertexSet\*todo
                                         <9>1 dag[q] \in [Rounds -> [Proc -> [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]]]
                                              BY <1>2, <2>1 DEF TypeOK
                                         <9>2 dag[q][r] \in [Proc -> [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]]
                                              BY <9>1, <2>1
                                         <9>3 dag[q][r][o] \in [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]
                                              BY <9>2, <2>1
                                         <9> QED BY <7>2, <6>5, <3>3, <9>3, <6>2
                                    <8>4 Observes(a, b) \/ Observes(b, a)
                                         BY <8>3, <8>2, <8>1, <6>1, <2>1, <3>3, <7>2 DEF Invariant6
                                    <8>5 Observes(a, v) /\ Observes(b, dag[q][r][o].ratifiedVertex)
                                         BY <8>1 DEF Approves
                                    <8>6 Observes(a, dag[q][r][o].ratifiedVertex) \/ Observes(b, v) 
                                         BY <8>4, <8>5, <3>3, <8>3, TransitiveObserveAs
                                    <8>7 v # dag[q][r][o].ratifiedVertex => ~ (Observes(a, dag[q][r][o].ratifiedVertex) \/ Observes(b, v))
                                        BY <8>1, <8>3 DEF Approves
                                    <8> QED BY <8>7, <8>6
                               <7>6 QED BY <7>1, <7>2
                          <6> QED BY <6>3, <6>5, <6>1, <1>2 DEF TypeOK
                     <5> QED BY <5>1, <5>2
                <4>2 CASE s = q /\ v.round = r /\ v.source = o
                     <5>1 CASE p = q
                          BY <5>1
                     <5>2 CASE q # p
                          <6>1 dag[p][r][o] = dag'[p][r][o] /\ faulty = faulty' /\ dag'[q][r][o].ratifiedVertex = v
                               BY <5>2, <4>2, <3>3, <2>1, <1>2 DEF RatifyVertexTn, TypeOK
                          <6>2 dag[p][r][o].ratifiedVertex # "Nil" /\ p \notin faulty /\ p \in Proc /\ r \in Rounds /\ o \in Proc
                               BY <6>1, <2>1, <1>2 DEF TypeOK
                          <6>3 \E B \in SUBSET(VertexSet): Cardinality({t \in Proc: (\E u \in B: u.source = t)}) = n-f /\ \A u \in B: u \in dag[p][u.round][u.source].vertices /\ Approves(u, dag[p][r][o].ratifiedVertex)
                               BY <6>2, <1>2, <2>1, <3>3 DEF Invariant1
                          <6>4 Cardinality({t \in Proc: (\E u \in A: u.source = t)}) = n-f /\ \A u \in A: u \in dag[q][u.round][u.source].vertices /\ Approves(u, v)
                               BY <3>3, <4>2 DEF RatifyVertexTn
                          <6>5 ASSUME NEW B \in SUBSET(VertexSet), Cardinality({t \in Proc: (\E u \in B: u.source = t)}) = n-f, \A u \in B: u \in dag[p][u.round][u.source].vertices /\ Approves(u, dag[p][r][o].ratifiedVertex)
                               PROVE v = dag[p][r][o].ratifiedVertex
                               <7>1 \E a \in A, b \in B: a.source = b.source /\ a.source \notin faulty \*/\ a \in dag[p][a.round][a.source].vertices /\ Approves(a, v) /\ b \in dag[q][b.round][b.source].vertices /\ Approves(b, dag[q][r][o].ratifiedVertex)
                                    BY <6>5, <6>4, <1>2, <3>3 DEF Invariant3
                               <7>2 ASSUME NEW a \in A, NEW b \in B, a.source = b.source /\ a.source \notin faulty
                                    PROVE  v = dag[p][r][o].ratifiedVertex
                                    <8>1 Approves(a, v) /\ Approves(b, dag[p][r][o].ratifiedVertex)
                                         BY <6>5, <7>2, <6>4
                                    <8>2 b \in dag[p][b.round][b.source].vertices /\ a \in dag[q][a.round][a.source].vertices
                                         BY <6>5, <7>2, <6>4
                                    <8>3 a \in VertexSet /\ b \in VertexSet /\ dag[p][r][o].ratifiedVertex \in VertexSet\*todo
                                         <9>1 dag[p] \in [Rounds -> [Proc -> [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]]]
                                              BY <1>2, <2>1 DEF TypeOK
                                         <9>2 dag[p][r] \in [Proc -> [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]]
                                              BY <9>1, <2>1
                                         <9>3 dag[p][r][o] \in [vertices : SUBSET(VertexSet), ratifiedVertex : VertexSet \cup {"Nil"}]
                                              BY <9>2, <2>1
                                         <9> QED BY <7>2, <6>5, <3>3, <9>3, <6>2
                                    <8>4 Observes(a, b) \/ Observes(b, a)
                                         BY <8>3, <8>2, <8>1, <6>1, <2>1, <3>3, <7>2 DEF Invariant6
                                    <8>5 Observes(a, v) /\ Observes(b, dag[p][r][o].ratifiedVertex)
                                         BY <8>1 DEF Approves
                                    <8>6 Observes(a, dag[p][r][o].ratifiedVertex) \/ Observes(b, v) 
                                         BY <8>4, <8>5, <3>3, <8>3, TransitiveObserveAs
                                    <8>7 v # dag[p][r][o].ratifiedVertex => ~ (Observes(a, dag[p][r][o].ratifiedVertex) \/ Observes(b, v))
                                        BY <8>1, <8>3 DEF Approves
                                    <8> QED BY <8>7, <8>6
                               <7>6 QED BY <7>1, <7>2
                          <6> QED BY <6>3, <6>5, <6>1, <1>2 DEF TypeOK
                     <5> QED BY <5>1, <5>2
                <4>3 CASE ~(s = p /\ v.round = r /\ v.source = o) /\ ~(s = q /\ v.round = r /\ v.source = o) 
                     <5>1 dag'[p][r][o].ratifiedVertex = dag[p][r][o].ratifiedVertex /\ dag'[q][r][o].ratifiedVertex = dag[q][r][o].ratifiedVertex
                          BY <4>3, <3>3,<2>1,<1>2 DEF TypeOK, RatifyVertexTn
                     <5>2 faulty = faulty'
                          BY <4>3, <3>3,<2>1,<1>2 DEF TypeOK, RatifyVertexTn
                     <5> QED BY <5>1, <5>2, <2>1, <1>2 DEF SafetyInv
                <4> QED BY <4>1, <4>2, <4>3
           
           <3> QED BY <3>1, <3>2, <3>3, <1>2, <2>1 DEF Next
      <2> QED BY <1>2, <2>1 DEF SafetyInv
 <1>3 ASSUME SafetyInv, UNCHANGED vars
      PROVE SafetyInv'
      BY <1>3 DEF SafetyInv, vars
 <1> QED BY <1>1, <1>2, <1>3, PTL, TypeOKThm, Invariant1Lm, Invariant3Lm, Invariant6Lm DEF Spec

LEMMA UnchangedDefLem == Waves = LeaderConsensus!WaveSet /\ Proc = LeaderConsensus!ProcessorSet /\ wAs = LeaderConsensus!NumWaveAsm /\ nAs = LeaderConsensus!NumProcessorAsm
                      BY DEF  Waves, LeaderConsensus!WaveSet, Proc, LeaderConsensus!ProcessorSet, wAs, LeaderConsensus!NumWaveAsm, nAs, LeaderConsensus!NumProcessorAsm

 
LEMMA SpecLem == Spec => LeaderConsensus!Spec
 <1>1 Init => LeaderConsensus!Init
    BY DEF Init
 <1>2 ASSUME TypeOK, [Next]_vars
      PROVE LeaderConsensus!Next \/ UNCHANGED LeaderConsensus!vars
      <2>1 ASSUME NEW s \in Proc, ProcessFailureTn(s)
           PROVE LeaderConsensus!Next \/ UNCHANGED LeaderConsensus!vars
           <3>1 LeaderConsensus!ProcessFailureTn(s)
                BY <2>1 DEF ProcessFailureTn
           <3>2 s \in LeaderConsensus!ProcessorSet
                BY <2>1, UnchangedDefLem
           <3>3 (\E w_1 \in LeaderConsensus!WaveSet, E \in SUBSET(LeaderConsensus!WaveSet) : LeaderConsensus!ProcessFailureTn(s)) => LeaderConsensus!Next
                BY <3>2 DEF LeaderConsensus!Next
           <3>4 \E w_1 \in LeaderConsensus!WaveSet, E \in SUBSET(LeaderConsensus!WaveSet) : LeaderConsensus!ProcessFailureTn(s)
                <4>1 Waves # {}
                     BY NonEmptyWaves
                <4> QED BY <4>1, UnchangedDefLem, <3>1 
           <3> QED BY <3>4, <3>3     
      <2>2 ASSUME NEW s \in Proc, NEW A \in SUBSET(VertexSet), NEW v \in VertexSet, RatifyVertexTn(s, v, A)
           PROVE LeaderConsensus!Next \/ UNCHANGED LeaderConsensus!vars
           <3>2 CASE v.round % 5 = 1 /\ v.source = ChooseLeader((v.round \div 5)+1)
                <4>1 (v.round \div 5)+1 \in 1..w
                     <5>1 v.round \in 0..(5*w)
                          BY VertexSetTypeAs DEF Rounds
                     <5> QED BY <5>1, <3>2, DivProperty1Plt, wAs
                <4>2 RatifiableWaveLeaders(v) \in SUBSET(Waves)
                     BY <2>2 DEF RatifiableWaveLeaders
                <4> QED BY <3>2, <2>2, <4>1, <4>2, UnchangedDefLem DEF RatifyVertexTn, LeaderConsensus!Next, Waves
           <3>3 CASE ~(v.round % 5 = 1 /\ v.source = ChooseLeader((v.round \div 5)+1))
                BY <3>3, <2>2 DEF RatifyVertexTn
           <3> QED BY <3>2, <3>3
      <2>3 ASSUME NEW s \in Proc, NEW v \in VertexSet, AddVertexTn(s, v)
           PROVE LeaderConsensus!Next \/ UNCHANGED LeaderConsensus!vars
           <3>1 ASSUME NEW q \in Proc, NEW x \in Waves, ReadyWave(s, x)
                PROVE LeaderConsensus!Next \/ UNCHANGED LeaderConsensus!vars
                BY UnchangedDefLem, <3>1, <1>2 DEF ReadyWave, TypeOK, LeaderConsensus!Next
           <3>2 CASE s \notin faulty /\ v.source = s /\ v.round > 0 /\ (v.round % 5) = 0
                <4>1 v.round \div 5 \in 1..w
                     <5>1 v.round \in 0..(5*w)
                          BY VertexSetTypeAs DEF Rounds
                     <5> QED BY <5>1, <3>2, DivProperty2Plt, wAs
                <4> QED BY <4>1, <2>3, <3>1, <3>2 DEF AddVertexTn, Waves
           <3>3 CASE s \notin faulty /\ ~(v.source = s /\ v.round > 0 /\ (v.round % 5) = 0 )
                BY <2>3, <3>3 DEF AddVertexTn, Waves
           <3>4 CASE s \in faulty
                <4> QED BY <2>3, <3>1, <3>4, UnchangedDefLem DEF AddVertexTn
           <3> QED BY <3>3, <3>2, <3>4
      <2>5 CASE UNCHANGED vars
           BY <2>5 DEF vars, LeaderConsensus!vars
      <2> QED BY <1>2, <2>1, <2>2, <2>3, <2>5 DEF Next
 <1> QED BY <1>1, <1>2, PTL, TypeOKThm DEF Spec, LeaderConsensus!Spec

THEOREM LeaderConsensusConsistencyThm == Spec=> []LeaderConsistency
  BY LeaderConsensus!ConsistencyThm, SpecLem, wAs, nAs, UnchangedDefLem DEF LeaderConsensus!Consistency, LeaderConsistency

THEOREM LeaderConsensusMonotonicityThm == Spec => []LeaderMonotonicity
  BY LeaderConsensus!MonotonicityThm, SpecLem, wAs, nAs, UnchangedDefLem DEF LeaderConsensus!Monotonicity, LeaderMonotonicity

THEOREM FullSafetyThm == Safety
  BY LeaderConsensusConsistencyThm, LeaderConsensusMonotonicityThm, SafetyThm DEF Safety
=============================================================================
\* Modification History
\* Last modified Fri Mar 22 17:09:30 AEDT 2024 by Pranav
\* Created Wed Mar 20 18:23:38 AEDT 2024 by Pranav
