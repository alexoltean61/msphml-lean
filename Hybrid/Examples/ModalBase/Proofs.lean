import Hybrid.Examples.ModalBase.S5

namespace S5
open Proof

/- Some helper propositional proofs. TODO: Prove me! -/
def dni : S5Pf (φ ⟶ ~~φ) := dni_frag (by simp; apply modalIsBase)
def impTrans : S5Pf ((φ ⟶ ψ) ⟶ (ψ ⟶ χ) ⟶ (φ ⟶ χ)) := sorry
def contraP : S5Pf ((ψ ⟶ φ) ⟶ (~φ ⟶ ~ψ)) := sorry

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
