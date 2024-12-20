------------------------- MODULE UnreliableStructuredDAGconstructionSpecification -------------------------

EXTENDS FiniteSets,
        Integers,
        Sequences

----------------------------------------------------------------------------

CONSTANT n

Proc == 1..n

ASSUME nAs == n \in Nat \ {0}

LEMMA ProcType == Proc \in SUBSET(Nat)
  BY nAs DEF Proc
----------------------------------------------------------------------------

CONSTANT f

ASSUME fAs == f \in Nat

ASSUME FailureBoundAs == 3*f < n
----------------------------------------------------------------------------

CONSTANT w

Waves == 1..w

Rounds == 0..(5*w)

ASSUME wAs == w \in Nat \ {0}

LEMMA RoundType == Rounds \in SUBSET(Nat)
  BY wAs DEF Rounds
LEMMA NonEmptyWaves == Waves # {}
      BY wAs DEF Waves
----------------------------------------------------------------------------

CONSTANT Blocks
----------------------------------------------------------------------------

CONSTANT VertexSet

DummyVertex(p) == [block : "Empty", source : p, round : 0, parents : {}]

ASSUME DVinVSAs == \A p \in Proc: DummyVertex(p) \in VertexSet

ASSUME VertexSetTypeAs == 
         VertexSet \in SUBSET([block : Blocks, 
                               source : Proc,
                               round : Rounds, 
                               parents : SUBSET(VertexSet)])
----------------------------------------------------------------------------
----------------------------------------------------------------------------

VARIABLES dag, faulty

------------------------------------------------------------------------------

TypeOK == 
  /\ dag \in [Proc -> [Rounds -> [Proc -> 
             [vertices : SUBSET(VertexSet), 
              ratifiedVertex : VertexSet \cup {"Nil"}]]]]
  /\ faulty \in SUBSET(Proc)

Init == 
  /\ dag = [p \in Proc |-> [r \in Rounds |-> [q \in Proc |->
            [vertices |-> IF r = 0 THEN {DummyVertex(q)} ELSE {}, 
             ratifiedVertex |-> "Nil"]]]]
  /\ faulty = {}
  
-----------------------------------------------------------------------------
RECURSIVE Observes(_, _)

Observes(v, u) == 
  IF v = u 
  THEN TRUE 
  ELSE IF v.round = 0 
       THEN FALSE 
       ELSE \E x \in v.parents : Observes(x, u)

Approves(v, u) == 
  /\ Observes(v, u) 
  /\ \A x \in VertexSet: ( /\ x.round = u.round 
                           /\ x.source = u.source)
                            => ~Observes(v, x)
----------------------------------------------------------------------------

ProcessFailureTn(p) == 
  /\ Cardinality(faulty) < f
  /\ p \notin faulty
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<dag>>
----------------------------------------------------------------------------

AddVertexTn(p, v) == 
  /\ p \notin faulty => 
     (/\ \E u \in v.parents: u.round = v.round - 1 /\ v.source = u.source
      /\ \E Q \in SUBSET(Proc): /\ Cardinality(Q) = n-f 
                                /\ \A q \in Q: \E u \in v.parents : 
                                     u.source = q /\ u.round = v.round-1
      /\ \A u \in v.parents: u \in dag[p][u.round][u.source].vertices
      /\ v.source = p =>  /\ dag[v.source][v.round][v.source].vertices = {} 
                          /\ \A u \in VertexSet : 
                             u \in dag[p][u.round][u.source].vertices  
                              => Observes(v, u) /\ u.round < v.round )
  /\ dag' = [a \in Proc |-> [r \in Rounds |-> [b \in Proc |-> 
            IF a = p /\ r = v.round /\ b = v.source 
            THEN [vertices |-> dag[p][v.round][v.source].vertices \cup {v}, 
                ratifiedVertex |-> dag[p][v.round][v.source].ratifiedVertex]
            ELSE dag[a][r][b]]]]
  /\ v.source # p /\ v.source \notin faulty 
      => v \in dag[v.source][v.round][v.source].vertices
  /\ UNCHANGED <<faulty>>
----------------------------------------------------------------------------

Ratifies(v, u) ==
  \E A \in SUBSET(VertexSet):
              /\ Cardinality({q \in Proc: (\E z \in A: z.source = q)}) = n-f
              /\ \A z \in A: Observes(v, z) /\ Approves(z, u)
              
RatifiableVertices(v) ==
  {u \in VertexSet : Ratifies(v, u)}
  
RatifyVertexTn(p, v, A) ==
  /\ dag[p][v.round][v.source].ratifiedVertex = "Nil"
  /\ \A u \in RatifiableVertices(v) : u = dag[p][u.round][u.source].ratifiedVertex
  /\ v \in dag[p][v.round][v.source].vertices
  /\ \A u \in A: u \in dag[p][u.round][u.source].vertices /\ Approves(u, v)
  /\ Cardinality({q \in Proc: (\E u \in A: u.source = q)}) = n-f
  /\ dag' = [a \in Proc |-> [r \in Rounds |-> [b \in Proc |->
               IF a = p /\ r = v.round /\ b = v.source
               THEN [vertices |-> dag[a][r][b].vertices,
                     ratifiedVertex |-> v]
               ELSE dag[a][r][b]]]]
  /\ UNCHANGED <<faulty>>
----------------------------------------------------------------------------

Next == 
  \E p \in Proc, v \in VertexSet, A \in SUBSET(VertexSet): 
     \/ ProcessFailureTn(p)
     \/ AddVertexTn(p, v)
     \/ RatifyVertexTn(p, v, A)
----------------------------------------------------------------------------

vars ==
  <<dag, faulty>>

Spec == 
  Init /\ [][Next]_vars
----------------------------------------------------------------------------

SafetyInv == 
  \A p \in Proc, q \in Proc, r \in Rounds, o \in Proc: 
     (/\ p \notin faulty 
      /\ dag[p][r][o].ratifiedVertex # "Nil"
      /\ q \notin faulty 
      /\ dag[q][r][o].ratifiedVertex # "Nil")
       => dag[p][r][o].ratifiedVertex = dag[q][r][o].ratifiedVertex
=============================================================================
