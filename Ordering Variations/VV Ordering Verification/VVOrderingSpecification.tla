-------------------- MODULE VVOrderingSpecification --------------------

EXTENDS FiniteSets,
        Integers,
        Sequences,
        TLAPS,
        TLC

CONSTANTS r, f, c, WitnessSet, faulty

ASSUME natfAs == f \in Nat

ASSUME natcAs == c \in Nat /\ c > 2

ASSUME natrAs == r \in Nat

Frames == 1..r

ProcessSet == 1..(3*f+1)

-----------------------------------------------------------------------------

VARIABLE WitnessDAG

WitnessDAGType == WitnessDAG \in [ProcessSet -> [Frames -> [ProcessSet -> SUBSET(WitnessSet)]]]

InitWitnessDAG == WitnessDAG = [p \in ProcessSet |-> [x \in Frames |-> [q \in ProcessSet |-> {}]]]

VARIABLE Fame

FameType == Fame \in [ProcessSet -> [WitnessSet -> BOOLEAN \cup {"undecided"}]]

InitFame == Fame = [p \in ProcessSet |-> [e \in WitnessSet |-> "undecided"]]

VARIABLE DecidedFrames

DecidedFramesType == DecidedFrames \in [ProcessSet -> [Frames -> BOOLEAN]]

InitDecidedFrames == DecidedFrames = [p \in ProcessSet |-> [x \in Frames |-> FALSE]]

VARIABLE FamousWitnesses

FamousWitnessesType == FamousWitnesses \in [ProcessSet -> [Frames -> SUBSET(WitnessSet)]]

InitFamousWitnesses == FamousWitnesses = [p \in ProcessSet |-> [x \in Frames |-> {}]]

VARIABLE Votes

VotesType == Votes \in [ProcessSet -> [WitnessSet -> [WitnessSet -> BOOLEAN \cup {"undecided"}]]]

InitVotes == Votes = [p \in ProcessSet |-> [e \in WitnessSet |-> [s \in WitnessSet |-> "undecided"]]]

-----------------------------------------------------------------------------

AddWitnessTn(p, e) == 
  /\ \A s \in e.stronglysees: s.frame = e.frame-1 /\ s \in WitnessDAG[p][s.frame][s.source] 
  /\ WitnessDAG' = [WitnessDAG EXCEPT![p][e.frame][e.source] = WitnessDAG[p][e.frame][e.source] \cup {e}]
  /\ WitnessDAG' [p][e.frame][e.source] = WitnessDAG[p][e.frame][e.source] \cup {e}
  /\ Cardinality({q \in ProcessSet: \E a \in e.stronglysees: a.source = q /\ a.frame = e.frame-1 /\ a \in WitnessDAG[p][a.frame][a.source]})> 2*f
  /\ \A s \in WitnessSet: Votes[p][s][e] = "undecided" /\ Votes[p][e][s] = "undecided"
  /\ UNCHANGED <<Fame, DecidedFrames, Votes, FamousWitnesses>>
             
VoteIn(p, s, e) == IF s.frame = e.frame+1 THEN (e \in s.stronglysees)
                   ELSE IF (s.frame - e.frame)%c # 0 THEN Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= TRUE}) >= Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= FALSE})
                        ELSE IF Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]}) > 2*f THEN TRUE
                             ELSE IF Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= FALSE}) > 2*f  THEN FALSE
                                  ELSE e.coinvote

VoteTn(p, s, e) ==
  /\ s.frame > e.frame
  /\ s \in WitnessDAG[p][s.frame][s.source] /\ e \in WitnessDAG[p][e.frame][e.source]
  /\ Votes[p][s][e] = "undecided"
  /\ \A a \in s.stronglysees: Votes[p][a][e] # "undecided" /\ a \in WitnessDAG[p][a.frame][a.source]
  /\ Votes' = [Votes EXCEPT ![p][s][e] = VoteIn(p, s, e)]
  /\ UNCHANGED <<WitnessDAG, Fame, FamousWitnesses, DecidedFrames>>

FameIn(p, s, e) == 
  IF Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]}) > 2*f THEN TRUE
     ELSE IF Cardinality({q \in ProcessSet: \E a \in s.stronglysees: a.source = q /\ Votes[p][a][e]= FALSE}) > 2*f THEN FALSE
          ELSE "undecided"
          
DecideFameTn(p, s, e) == 
  /\ Fame[p][e] = "undecided"
  /\ s \in WitnessDAG[p][s.frame][s.source] /\ e \in WitnessDAG[p][e.frame][e.source]
  /\ s.frame> e.frame+1
  /\ (s.frame-e.frame)%c # 0
  /\ Votes[p][s][e] = FameIn(p, s, e) 
  /\ FameIn(p, s, e) # "undecided"
  /\ Fame' = [Fame EXCEPT ![p][e] = FameIn(p, s, e)]
  /\ UNCHANGED <<WitnessDAG, DecidedFrames, Votes, FamousWitnesses>>

DecideFrameTn(p, x) == 
  /\ \E q \in ProcessSet: WitnessDAG[p][x][q] # {}
  /\ \E a \in WitnessSet: a \in WitnessDAG[p][x+2][a.source] /\ a.frame = x+2
  /\ DecidedFrames[p][x] = FALSE
  /\ \A e \in WitnessSet: e \in WitnessDAG[p][x][e.source] => Fame[p][e] # "undecided"
  /\ DecidedFrames' = [DecidedFrames EXCEPT ![p][x] = TRUE]
  /\ UNCHANGED <<Fame, WitnessDAG, Votes>>
  /\ FamousWitnesses' = [FamousWitnesses EXCEPT ![p][x] = {e \in WitnessSet: e.frame = x /\ e \in WitnessDAG[p][x][e.source] /\ Fame[p][e] = TRUE}]

--------------------------------------------------------------------------

UniqueStronglyseenAs == \A p \in ProcessSet, q \in ProcessSet, e \in WitnessSet, a \in WitnessSet: 
        (/\ p \notin faulty /\ q \notin faulty
         /\ a.frame = e.frame 
         /\ a.source = e.source 
         /\ \E s \in WitnessSet: s \in WitnessDAG[q][s.frame][s.source] /\ a \in s.stronglysees
         /\ \E l \in WitnessSet: l \in WitnessDAG[p][l.frame][l.source] /\ e \in l.stronglysees) => a = e
       
TypeOK == WitnessDAGType /\ VotesType /\ FameType /\ DecidedFramesType /\ FamousWitnessesType

Init == InitWitnessDAG /\ InitVotes /\ InitFame /\ InitDecidedFrames /\ InitFamousWitnesses

vars == <<WitnessDAG, Votes, Fame, DecidedFrames, FamousWitnesses>>

Next == /\ UniqueStronglyseenAs
        /\ UniqueStronglyseenAs'
        /\ \E p \in ProcessSet, x \in Frames, e \in WitnessSet, s \in WitnessSet: 
                     \/ AddWitnessTn(p, e)
                     \/ DecideFameTn(p, s, e)
                     \/ VoteTn(p, s, e)
                     \/ DecideFrameTn(p, x)

Spec == Init /\ [][Next]_vars
--------------------------------------------------------------------------  

Safety == \A p \in ProcessSet, q \in ProcessSet, x \in Frames:
              p \notin faulty /\ q \notin faulty /\ DecidedFrames[p][x] /\ DecidedFrames[q][x] => FamousWitnesses[p][x] = FamousWitnesses[q][x]

-----------------------------------------------------------------------------
=============================================================================
\* Modification History
\* Last modified Wed Sep 04 18:14:00 AEST 2024 by pgho0778
\* Created Wed Sep 04 12:37:39 AEST 2024 by pgho0778
