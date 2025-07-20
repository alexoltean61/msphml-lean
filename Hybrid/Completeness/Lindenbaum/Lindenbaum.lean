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

abbrev m  := S.new_nominals.2
abbrev S_plus := S.new_nominals.1
abbrev s_plus := m.m.morph_sort s

lemma Lindenbaum (h : Γ.consistent Λ) : ∃ Γ' : NamedPastedWitnessedMCS S_plus s_plus (m.m.morph_axiom Λ), (m.m.morph_premise Γ) ⊆ Γ'.set := sorry

end Completeness
