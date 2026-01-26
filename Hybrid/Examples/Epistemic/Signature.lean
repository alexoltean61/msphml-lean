import Hybrid.BNF

hybrid_def Epistemic :=
  sort Agent ::= builtin Nat       -- countable set of agents
  sort Fact  ::= builtin Nat       -- countable set of atomic fats
               | "K"(Agent, Fact)  -- knowledge operator

#print Epistemic.Sorts
#print Epistemic.Ops
#print Epistemic.CtNoms
#print Epistemic
