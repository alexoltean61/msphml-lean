import Hybrid.SMC.Axioms

open SMC

def Pgm (s i n : Symb.nominal SortVar)
  : SMCForm SortStmt :=
  s ::= 0;
  i ::= 0;
  while (++i <= n) do'
    s ::= s + i

def PgmCorrect (vs : SMCForm SortValStack)
        (mem : SMCForm SortMem)
        (s i n : Symb.nominal SortVar)
        (vn : ℕ) : SMCForm SortConfig :=
    ⟨vs, set(mem, n, vn)⟩ ⟶ [c(Pgm s i n)] ⟨vs, set(set(set(mem, n, vn), n, vn * (vn.add 1).div2), i, vn.add 1)⟩

def todo : SMCProof _ (PgmCorrect vs mem s i n vn) := sorry
