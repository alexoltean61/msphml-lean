import Hybrid.Examples.SMC.Lemmas

open SMC
open Proof

def assgnNat (s : SMCForm Var) (v : SMCForm Nat):
  SMCProof _
    (⟨vs, mem⟩ ⟶ [c(s ::= v)] ⟨vs, set(mem, s, v)⟩) := by
    apply propagateDAsgn
    apply composition
    case φ₁ => exact ⟨v ⬝ vs, mem⟩
    . exact aint
    . exact aasgn

def swapPgm (x y aux : SMCForm Var) : SMCForm Stmt :=
  aux ::= x;
  x   ::= y;
  y   ::= aux

def swapCorrect
  (neq1 : y ≠ x)
  (neq2 : y ≠ aux)
  : SMCProof _
    (⟨vs, set(set(mem, y, yn), x, xn)⟩ ⟶ [c(swapPgm x y aux)] ⟨vs, set(set(set(mem, x, yn), aux, xn), y, xn)⟩) := by
  apply propagateSeq
  apply composition
  . apply assgnVar
    exact aid
  . apply propagateSeq
    apply composition
    . apply assgnVar
      . apply propagateMemL (bubble3Mem neq1 neq2) ?transition -- HERE
        . exact yn
        . apply propagateMemR (bubble3Mem neq1 neq2)           -- HERE
          apply aid
    . apply @propagateMemL _ _ _ _ (set(set(set(mem, y, yn), x, yn), aux, xn))
      . -- HERE
        admit
      . apply @propagateMemR _ _ _ _ (set(set(set(set(mem, y, yn), x, yn), aux, xn), y, xn))
        . -- HERE
          admit
        . apply assgnVar
          exact aid

def sumPgm (s i n : SMCForm Var)
  : SMCForm Stmt :=
  s ::= 0;
  i ::= 0;
  while (++i <= n) do'
    s ::= s + i

def sumCorrect (vs : SMCForm ValStack)
        (mem : SMCForm Mem)
        (s i n : CtNoms Var)
        (vn : ℕ) :
    SMCProof _
      (⟨vs, set(mem, n, vn)⟩ ⟶ [c(sumPgm s i n)] ⟨vs, set(set(set(mem, n, vn), s, vn * (vn.add 1).div2), i, vn.add 1)⟩) := by
    apply propagateSeq
    apply composition
    . apply assgnNat
    . apply propagateSeq
      apply composition
      . apply assgnNat
      . apply weakeningPost
        . apply iteration
          repeat admit
        . admit

def effectfulIf (i : SMCForm Var): SMCForm Stmt :=
  if (++i <= 1) then
    i ::= 2
  else
    i ::= 3
  endif

def ifCorr (i : SMCForm Var):
    SMCProof _
      (⟨vs, set(mem, i, (0 : ℕ))⟩ ⟶ [c(effectfulIf i)] ⟨vs, set(mem, i, (2 : ℕ))⟩) := by
    apply conditional
    . have test := @app vs mem i 0
      simp at test

      admit
    repeat admit
