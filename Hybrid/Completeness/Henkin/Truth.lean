import Hybrid.Completeness.Henkin.Model

namespace Completeness

open Completeness

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s t : symbs.signature.S}
variable {j : symbs.nominal t}
variable {φ : Form symbs t}
variable {Λ : AxiomSet symbs}
variable {Γ : NamedPastedWitnessedMCS symbs s Λ}

lemma Truth : (⟨Γ.HenkinModel, Γ.HenkinAsgn, |j| Γ⟩ ⊨ φ) ↔ (ℋ@j φ) ∈ Γ.set := sorry

end Completeness
