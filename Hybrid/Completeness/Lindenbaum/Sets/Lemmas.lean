import Hybrid.Completeness.Lindenbaum.Sets.Sets
import Hybrid.Completeness.Lindenbaum.Sets.ExtendiblePremiseSet
import Hybrid.Completeness.Lindenbaum.Expansion.Def
import Hybrid.Completeness.Lindenbaum.Expansion.Helpers

namespace Completeness

open Completeness

section MCS

  variable {α : Type u}
  variable [DecidableEq α]
  variable {symbs : Symbols α}
  variable {s : symbs.signature.S}
  variable {Γ : PremiseSet symbs s}

  lemma mcs_and (h : Γ.maximal_consistent Λ) (φ ψ) : (φ ⋀ ψ) ∈ Γ ↔ (φ ∈ Γ ∧ ψ ∈ Γ) := sorry

  lemma mcs_and_left (h : Γ.maximal_consistent Λ) (ψ) : (φ ⋀ ψ) ∈ Γ → φ ∈ Γ := sorry

  lemma mcs_and_right (h : Γ.maximal_consistent Λ) (φ) : (φ ⋀ ψ) ∈ Γ → ψ ∈ Γ := sorry

  lemma mcs_em (h : Γ.maximal_consistent Λ) : ¬ (φ ∈ Γ ∧ ∼φ ∈ Γ) := sorry

  lemma mcs_pf (h : Γ.maximal_consistent Λ) : Γ ⊢(Λ) φ ↔ φ ∈ Γ := sorry

  lemma gen_at_closed (h : Γ.maximal_consistent Λ) (φ : ↑Γ) (j : symbs.nominal s) (h2 : ℋNom j ∈ ↑Γ) : ℋ@j φ ∈ Γ := by
    have h1 := φ.2
    rw [←mcs_pf h] at h1 h2 ⊢
    apply Proof.premise_gen_at
    repeat assumption

  lemma mcs_conjunction (h : Γ.maximal_consistent Λ) (φ_list : FiniteChoice Γ) : φ_list.conjunction ∈ Γ := by
    simp only [FiniteChoice.conjunction]
    induction φ_list.1 with
    | nil =>
        rw [←mcs_pf h]
        admit
    | cons φ φs ih =>
        unfold List.conjunction
        rw [mcs_and h]
        apply And.intro _ φ.2
        exact ih

end MCS

section ExtendiblePremiseSet

  variable {α : Type u} [DecidableEq α]
  variable {β : Type v} [β_deq : DecidableEq β]
  variable {S : Symbols α}
  variable {s : S.signature.S}
  variable {Λ : AxiomSet S}
  variable {Γ : PremiseSet S s}

  def enough_nominals_embed {ext : @S.nominal_extension α β β_deq β} {u : ext.target.signature.S} : { n : ext.target.nominal u | ¬(ext.m+ Λ).occurs n ∧ ¬(ext.m+ Γ).occurs n } ≃ ℕ := sorry

  def enough_nominals_singleton {Γ : ExtendiblePremiseSet S s Λ} : { n : S.nominal t | ¬Λ.occurs n ∧ ¬(Γ.set ∪ { φ }).occurs n } ≃ ℕ := sorry

  def enough_nominals_at_witness {Γ : ExtendiblePremiseSet S s Λ} : { n : S.nominal t | ¬Λ.occurs n ∧ ¬(Γ.set ∪ Γ.at_witness_vars).occurs n } ≃ ℕ := sorry

  def enough_nominals_paste {Γ : ExtendiblePremiseSet S s Λ} : { n : S.nominal t | ¬Λ.occurs n ∧ ¬(Γ.set ∪ Γ.paste_args j σ χ i).occurs n } ≃ ℕ := sorry

  lemma Lindenbaum.odd_nominal_inj [inst : Encodable β] {Γ : ExtendiblePremiseSet symbs sort ax} : (@Γ.odd_nominal α _ _ _ _ _ inst t).Injective :=
    λ _ _ h => sorry

  lemma Lindenbaum.even_nominal_inj [inst : Encodable β] {Γ : ExtendiblePremiseSet symbs sort ax} : (@Γ.even_nominal α _ _ _ _ _ inst t).Injective :=
    λ _ _ h => sorry

  lemma Lindenbaum.odd_nom_nocc_axioms [Encodable β] {x : β} {es : ExtendiblePremiseSet S s Λ}: ¬Λ.occurs (es.odd_nominal t x) := sorry

  lemma Lindenbaum.odd_nom_nocc_premises [Encodable β] {x : β} {es : ExtendiblePremiseSet S s Λ}: ¬es.set.occurs (es.odd_nominal t x) := sorry

  lemma Lindenbaum.prod_even_nom_nocc_axioms [Encodable β] [Encodable γ] {x₁ : β} {x₂ : γ} {t : S.signature.S} {es : ExtendiblePremiseSet S s Λ}: ¬Λ.occurs (es.prod_even_nominal t x₁ x₂) := sorry

  lemma Lindenbaum.prod_even_nom_nocc_premises [Encodable β] [Encodable γ] {x₁ : β} {x₂ : γ} {es : ExtendiblePremiseSet S s Λ}: ¬es.set.occurs (es.prod_even_nominal t x₁ x₂) := sorry


end ExtendiblePremiseSet
