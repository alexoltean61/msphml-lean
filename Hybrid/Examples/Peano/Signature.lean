import Hybrid.BNF

hybrid_def Peano :=
  sort Nat ::= zero | "succ"(Nat)

#print Peano.Sorts
#print Peano.Ops
#print Peano.CtNoms
#print Peano
