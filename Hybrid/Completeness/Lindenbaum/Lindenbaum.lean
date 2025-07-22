import Hybrid.Completeness.Lindenbaum.Sets
import Hybrid.Completeness.Lindenbaum.Expansion

namespace Completeness

open Completeness

variable {α : Type u}
variable [DecidableEq α]
variable {S : Symbols α}
variable {s : S.signature.S}
variable {Λ : AxiomSet S}
variable {Γ : PremiseSet S s}

noncomputable abbrev m  := Classical.choice S.new_nominals.choose_spec
noncomputable abbrev S_plus := S.new_nominals.choose

lemma Lindenbaum (h : Γ.consistent Λ) : ∃ Γ' : NamedPastedWitnessedMCS S_plus (m+ s) (m+ Λ), (m+ Γ) ⊆ Γ'.set := sorry

end Completeness
