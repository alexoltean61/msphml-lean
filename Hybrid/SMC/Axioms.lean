import Hybrid.SMC.Signature

namespace SMC

-- c(s1 ; s2) ↔ c(s1) ; c(s2)
def CStmtAx (s1 s2 : SMCForm SortStmt)
  : SMCForm SortCtrlStack :=
    c(s1 ; s2) ←→ c(s1) ; c(s2)

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
    ⟨vs, set(mem, x, n)⟩ ⟶ [c(++x)] ⟨↑(n.add 1) ⬝ vs, set(mem, x, ↑(n.add 1))⟩

-- c(a1 + a2) ↔ c(a1) ; c(a2) ; plus
def DPlus (a1 a2 : SMCForm SortAExp) : SMCForm SortCtrlStack :=
    c(a1 + a2) ←→ c(a1) ; c(a2) ; plus

-- ⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [plus] ⟨n1 + n2 ⬝ vs, mem⟩
def Aplus (n1 n2 : ℕ)
          (vs : SMCForm SortValStack)
          (mem : SMCForm SortMem)
    : SMCForm SortConfig :=
      ⟨n2 ⬝ n1 ⬝ vs, mem⟩ ⟶ [plus] ⟨↑(n1.add n2) ⬝ vs, mem⟩

-- c(a1 <= a2) ↔ c(a1) ; c(a2) ; leq
def DLeq (a1 a2 : SMCForm SortAExp) : SMCForm SortCtrlStack :=
    c(a1 <= a2) ←→ c(a1) ; c(a2) ; leq

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
def DAsgn (x : SMCForm SortVar)
          (a : SMCForm SortAExp) : SMCForm SortCtrlStack :=
      c(x ::= a) ←→ c(a) ; asgn(x)

-- AAsgn ⟨n ⬝ vs, mem) ⟶ [asgn(x)] ⟨vs, set(mem, x, n)⟩
def AAsgn (n : SMCForm SortVal)
          (vs : SMCForm SortValStack)
          (mem : SMCForm SortMem)
          (x : SMCForm SortVar): SMCForm SortConfig :=
      ⟨n ⬝ vs, mem⟩ ⟶ [asgn(x)] ⟨vs, set(mem, x, n)⟩

-- DIf
--   c(if bexp then s1 else s2) ↔ c(bexp) ; ( (true? ; c(s1)) ∪ (false? ; c(s2)) )
def DIf (bexp : SMCForm SortBExp)
          (s1 s2 : SMCForm SortStmt) : SMCForm SortCtrlStack :=
      c(if bexp then s1 else s2 endif) ←→ c(bexp) ; ((true ? ; c(s1)) ∪ (false ? ; c(s2)))

-- DWhile
--   c(while bexp do s) ↔ c(bexp) ; ( (true?) ; c(s) ; c(bexp) )* ; false?
def DWhile (bexp : SMCForm SortBExp)
          (s : SMCForm SortStmt) : SMCForm SortCtrlStack :=
    c(while bexp do' s ) ←→ c(bexp) ; (true ? ; c(s) ; c(bexp))* ; false ?

-- Memory consistency axioms:

def AMem1 (x y : SMCForm SortVar)
          (h : x ≠ y)
          (n m : SMCForm SortVal)
          (mem : SMCForm SortMem) : SMCForm SortMem :=
        set(set(mem, x, n), y, m) ←→ set(set(mem, y, m), x, n)

def AMem2 (x : SMCForm SortVar)
          (n m : SMCForm SortVal)
          (mem : SMCForm SortMem) : SMCForm SortMem :=
        set(set(mem, x, n), x, m) ←→ set(mem, x, m)

-- PDL-inspired axioms:
def ACup (π π' : SMCForm SortCtrlStack)
         (γ : SMCForm SortConfig) : SMCForm SortConfig :=
        [π ∪ π'] γ ←→ [π] γ ⋀ [π'] γ

def ASeq (π π' : SMCForm SortCtrlStack)
         (γ : SMCForm SortConfig) : SMCForm SortConfig :=
        [π ; π'] γ ←→ [π][π'] γ

def ATestTrue (v : SMCForm SortVal)
         (vs : SMCForm SortValStack)
         (mem : SMCForm SortMem) : SMCForm SortConfig :=
        ⟨v ⬝ vs, mem⟩ ←→ [v ?] ⟨vs, mem⟩

-- TODO: Take a look here.
--  What if v is not a nominal, but a different kind of formula of sort SortVal?
--  You cannot use the ℋ@ binder then.
-- The paper asks for v being a state variable. That also doesn't work.
def ATestFalse (v : Symb.nominal SortVal)
         (v' : SMCForm SortVal)
         (vs : SMCForm SortValStack)
         (mem : SMCForm SortMem) : SMCForm SortConfig :=
        ⟨v ⬝ vs, mem⟩ ⋀ ℋ@ v (∼v') ←→ [v' ?] ℋ⊥

def AStar (π : SMCForm SortCtrlStack)
         (γ : SMCForm SortConfig) : SMCForm SortConfig :=
        [π*] γ ←→ γ ⋀ [π][π*] γ

def AInd (π : SMCForm SortCtrlStack)
         (γ : SMCForm SortConfig) : SMCForm SortConfig :=
        γ ⋀ [π*](γ ⟶ [π]γ) ←→ [π*] γ

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

end SMC
