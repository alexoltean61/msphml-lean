import Hybrid.Examples.Modal.Base.S5

namespace S5
open Proof

/- Some helper propositional proofs, lifted from the general logic -/
def dni : S5Pf (φ ⟶ ~~φ) := by
  apply Proof.fragment.mk Proof.dni
  simp [Proof.dni, inFragment]
  apply modalIsBase
def impTrans : S5Pf ((φ ⟶ ψ) ⟶ (ψ ⟶ χ) ⟶ (φ ⟶ χ)) := by
  apply Proof.fragment.mk Proof.imp_trans_theorem_proof
  simp [Proof.imp_trans_theorem_proof, inFragment]
  apply And.intro (And.intro _ _) (And.intro (And.intro _ _) (And.intro _ _))
  repeat { apply modalIsBase }
def contraP : S5Pf ((ψ ⟶ φ) ⟶ (~φ ⟶ ~ψ)) := by
  apply Proof.fragment.mk Proof.contraposition
  simp [Proof.contraposition, inFragment]
  apply And.intro (And.intro _ _) (And.intro _ _)
  repeat { apply modalIsBase }


/-
  Now we can prove some interesting S5 facts...
-/
def posNecActual : S5Pf (◇□ φ ⟶ φ) := by
  have l1 : S5Pf (◇(~φ) ⟶ □◇(~φ)) := ax_a5
  have l2 : S5Pf (~(□◇(~φ)) ⟶ ~(◇(~φ))) := modusPonens contraP l1
  have l3 : S5Pf ((◇□φ) ⟶ ~(□◇ ~φ)) := dni
  have l4 : S5Pf ((~(□◇(~φ)) ⟶ ~(◇(~φ))) ⟶ (◇□φ ⟶ ~(◇(~φ)))) := modusPonens impTrans l3
  have l5 : S5Pf (◇□ φ ⟶ □ φ) := modusPonens l4 l2
  have l5 : S5Pf ((□ φ ⟶ φ) ⟶ (◇□ φ ⟶ φ)) := modusPonens impTrans l5
  have l6 : S5Pf (◇□ φ ⟶ φ) := modusPonens l5 ax_t
  exact l6
