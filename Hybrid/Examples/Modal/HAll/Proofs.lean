import Hybrid.Examples.Modal.HAll.NormalLogic

namespace PfHAll
open Proof

/- Some helper propositional proofs. TODO: Prove me! -/
def dni : PfHAll (φ ⟶ ~~φ) := sorry
def impTrans : PfHAll ((φ ⟶ ψ) ⟶ (ψ ⟶ χ) ⟶ (φ ⟶ χ)) := sorry
def contraP : PfHAll ((ψ ⟶ φ) ⟶ (~φ ⟶ ~ψ)) := sorry

def ax_nom_instance {i : nom} (m n : ℕ) :
  PfHAll (◇^m (i ⋀ φ) ⟶ □^n (i ⟶ φ)) := by

  sorry
