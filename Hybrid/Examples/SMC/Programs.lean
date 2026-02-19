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

def incrementMax (x y aux : SMCForm Var): SMCForm Stmt :=
  if (x <= ++y) then
    aux ::= x;
    x   ::= y;
    y   ::= aux
  endif

def swapCorrect
  (neq1 : y ≠ x)
  (neq2 : y ≠ aux)
  (neq3 : x ≠ aux)
  : SMCProof _
    (⟨vs, set(set(mem, y, yn), x, xn)⟩ ⟶ [c(swapPgm x y aux)] ⟨vs, set(set(set(mem, x, yn), aux, xn), y, xn)⟩) := by
  apply propagateSeq
  apply composition
  . apply assignment
    exact aid
  . apply propagateSeq
    apply composition
    . apply assignment
      . apply propagateMemL (bubble3Mem neq1 neq2) ?transition
        . exact yn
        . apply propagateMemR (bubble3Mem neq1 neq2)
          apply aid
    . apply propagateMemL
      . apply Proof.ax ⟨_, Nonempty.intro (.AStackLike3 neq1.symm neq3 neq2)⟩
      . apply propagateMemR
        . apply Proof.ax ⟨_, Nonempty.intro (.AStackLike4 neq1.symm neq3 neq2)⟩
        . apply assignment
          exact aid

def ifCorr
  (neq1 : x ≠ y)
  (neq2 : y ≠ aux)
  (neq3 : x ≠ aux):
    SMCProof _
      (⟨vs, set(set(mem, x, (0:ℕ)), y, (2:ℕ))⟩ ⟶
        [c(incrementMax x y aux)] ⟨vs, set(set(mem, x, (3:ℕ)), y, (0:ℕ))⟩) := by
    apply conditional
    . apply propagateDLeq
      apply composition
      . apply propagateMemL (amem1 neq1)
        . apply aid
      . apply composition
        . apply propagateMemL (amem1 neq1.symm)
          apply app
        . apply propagateDAdd
          apply aleq
    . apply import_proof
      apply imp_trans_proof
      . apply propagateMemL (amem1 neq1)
        apply swapCorrect neq1.symm neq2 neq3
      . apply imp_com_proof
        apply imp_trans_proof
        . apply atInv
          . exact c(swapPgm x y aux)
        . apply imp_trans_proof _ kPgm
          . apply mp kPgm
            apply necessPgm
            apply mp (prop1 _ _)
            apply Proof.ax ⟨_, Nonempty.intro <| .AMemStack neq3⟩
    . apply import_proof
      apply imp_com_proof
      apply imp_trans_proof _ exfalso
      apply falseNatLeq
      simp only [Nat.ble_eq, Nat.zero_le]
