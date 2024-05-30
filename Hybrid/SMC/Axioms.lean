import Hybrid.SMC.Signature

namespace SMC

-- c(s1 ; s2) ↔ c(s1) ; c(s2)
def CStmtAx (s1 s2 : SMCForm SortStmt)
  : SMCForm SortCtrlStack :=
    c(s1 ; s2) ↔ c(s1) ; c(s2)

-- ⟨vs, mem⟩ → [c(n)] ⟨n ⬝ vs, mem⟩, where n is an integer
def Aint (vs : SMCForm SortValStack)
         (mem : SMCForm SortMem)
         (n : ℕ)
    : SMCForm SortConfig :=
    ⟨vs, mem⟩ ⟶ [c(n)] ⟨n ⬝ vs, mem⟩

-- ⟨vs, set(mem, x, n)⟩ → [c(x)] ⟨n ⬝ vs, set(mem, x, n)⟩
def Aid (vs : SMCForm SortValStack)
        (mem : SMCForm SortMem)
        (x : SMCForm SortVar)
        (n : ℕ)
    : SMCForm SortConfig :=
    ⟨vs, set(mem, x, n)⟩ ⟶ [c(x)] ⟨n ⬝ vs, set(mem, x, n)⟩

-- ⟨vs, set(mem, x, n)⟩ → [c(++x)] ⟨(n+1) ⬝ vs, set(mem, x, n+1)⟩
def App  (vs : SMCForm SortValStack)
         (mem : SMCForm SortMem)
         (x : SMCForm SortVar)
         (n : ℕ)
  : SMCForm SortConfig :=
    ⟨vs, set(mem, x, n)⟩ ⟶ [c(++x)] ⟨↑(n+1) ⬝ vs, set(mem, x, ↑(n+1))⟩

-- c(a1 + a2) ↔ c(a1) ; c(a2) ; plus
def DPlus (a1 a2 : SMCForm SortAExp) : SMCForm SortCtrlStack :=
    c(a1 +Nat a2) ↔ c(a1) ; c(a2) ; plus

-- ⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [plus] ⟨n1 + n2 ⬝ vs, mem⟩
def Aplus (n1 n2 : ℕ)
          (vs : SMCForm SortValStack)
          (mem : SMCForm SortMem)
    : SMCForm SortConfig :=
      ⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [plus] ⟨↑(n1 + n2) ⬝ vs, mem⟩

-- c(a1 <= a2) ↔ c(a1) ; c(a2) ; leq
def DLeq (a1 a2 : SMCForm SortAExp) : SMCForm SortCtrlStack :=
    c(a1 <=AExp a2) ↔ c(a1) ; c(a2) ; leq

-- ⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [leq] ⟨↑(n1 ≤ n2), mem⟩
def ALeq (n1 n2 : ℕ)
          (vs : SMCForm SortValStack)
          (mem : SMCForm SortMem)
    : SMCForm SortConfig :=
      ⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [leq] ⟨↑(n1.ble n2) ⬝ vs, mem⟩

-- γ ⟶ [skip] γ
def ASkip (γ : SMCForm SortConfig): SMCForm SortConfig :=
      γ ⟶ [skip] γ

-- DAsgn c(x := a) ↔ c(a) ; asgn(x)

-- AAsgn ⟨n ⬝ vs, mem) ⟶ [c(asgn(x))] ⟨vs, set(mem, x, n)⟩

-- DIf
--   c(if bexp then s1 else s2) ↔ c(bexp) ; ( (true? ; c(s1)) ∪ (false? ; c(s2)) )

-- DWhile
--   c(while bexp do s) ↔ c(bexp) ; ( (true?) ; c(s) ; c(bexp) )* ; false?

end SMC
