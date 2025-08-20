import Hybrid.Completeness.Henkin.Lemmas
import Hybrid.Soundness.Lemmas

namespace Completeness

open Completeness
open NamedPastedWitnessedMCS

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s : symbs.signature.S}
variable {Λ : AxiomSet symbs}
variable {Γ : NamedPastedWitnessedMCS symbs s Λ}

lemma Truth {t : symbs.signature.S} {j : symbs.nominal t} {φ : Form symbs t} : (⟨Γ.HenkinModel, Γ.HenkinAsgn, ⟦j⟧⟩ ⊨ φ) ↔ (ℋ@j φ) ∈ Γ.set := by
  match φ with
  | ℋProp p =>
      simp
      apply Iff.intro
      . intro ⟨k, ⟨at_k, k_eq_j⟩⟩
        admit
      . intro h
        exists j
        apply And.intro h
        admit
  | ℋNom n =>
      cases n <;>
      . simp [Model.VNom]
  | ℋVar x =>
      have by_witnessed := (Γ.witnessed.2 x).choose_spec
      simp [HenkinAsgn]
      apply Iff.intro
      . intro h
        -- Use h to substitute Classical.choose ... for j in the goal
        -- The close it with by_witnessed
        admit
      . intro h
        -- Use Nom axiom
        admit
  | φ ⋁ ψ =>
      simp only [Sat.or]
      apply Iff.intro
      . intro h
        apply Or.elim h
        . clear h
          intro h
          rw [Truth] at h
          admit
        . clear h
          intro h
          rw [Truth] at h
          admit
      . intro h
        -- Since Γ is maximal consistent, from h you can show that
        -- ℋ@ j φ ∈ Γ.set ∨ ℋ@ j ψ ∈ Γ.set
        admit
  | ℋ⟨σ⟩ φs =>
      rw [Sat.appl]
      apply Iff.intro
      . intro ⟨qs, ⟨sat_args, ⟨k, ⟨ks, ⟨h_mem, ⟨nom_quot_eq, prod_quot_eq⟩⟩⟩⟩⟩⟩
        simp at nom_quot_eq
        conv at sat_args =>
            rw [Sat.context', ←prod_quot_eq]
            ext
            rw [WProd.to_quotient_select]
            -- induction:
            rw [Truth]
        rw [WProd.to_quotient_eq] at prod_quot_eq

        admit
      . rename_i st ss
        intro h
        /-
          Take the nominals on the diagonal:
                       @j σ(φ₁, φ₂, ..., φₙ) ∈ Γ →
          @k₁ φ₁ ∈ Γ ∧ @j σ(k₁, φ₂, ..., φₙ) ∈ Γ →
          @k₂ φ₂ ∈ Γ ∧ @j σ(k₁, k₂, ..., φₙ) ∈ Γ →
          ...................................... →
          @kₙ φₙ ∈ Γ ∧ @j σ(k₁, k₂, ..., kₙ) ∈ Γ

          INVARIANT:
            At each step n, for all i < n, @kᵢ φᵢ ∈ Γ ∧ @j σ(k₁, ..., kᵢ, ..., φₙ) ∈ Γ
        -/
        have by_paste := paste_everything Γ.pasted h
        match by_paste with
        | ⟨ws, h_ws⟩ =>
            exists ws.to_quotient Γ
            clear by_paste
            obtain ⟨left, right⟩ := h_ws
            apply And.intro
            . rw [Sat.context']
              intro e
              have : sizeOf e.form < sizeOf (ℋ⟨σ⟩ φs) := sorry -- todo
              rw [WProd.to_quotient_select, Truth]
              exact right e
            . simp
              exists j
              exists ws
              simp only [nominal_eq_refl, and_self, and_true]
              exact left
  | ℋ@ (.inl k) φ =>
      simp only [Sat.at, Model.VNom]
      conv =>
        lhs ; lhs
        simp only [HenkinModel.eq_1, nominalSetoid.eq_1]
      apply Iff.intro
      . intro h
        have := (@Truth _ (Sum.inl k) φ).mp h
        -- Rewrite the goal using Agree, since Γ is maximal consistent
        -- Goal will be closed by exact this.
        admit
      . intro h
        apply (@Truth _ (Sum.inl k) φ).mpr
        -- Same as above
        admit
  | ℋ@ (.inr k) φ =>
      simp only [Sat.at, Model.VNom]
      conv =>
        lhs ; lhs
        simp only [HenkinModel.eq_1,
          nominalSetoid.eq_1]
      apply Iff.intro
      . intro h
        have := (@Truth _ (Sum.inr k) φ).mp h
        -- Rewrite the goal using Agree, since Γ is maximal consistent
        -- Goal will be closed by exact this.
        admit
      . intro h
        apply (@Truth _ (Sum.inr k) φ).mpr
        -- Same as above
        admit
  | ℋ∃ x φ =>
      simp only [Sat.exists]
      rename_i st
      apply Iff.intro
      . intro ⟨g', ⟨g'_var, h⟩⟩
        have ⟨l, l_is_rep⟩ := (g' x).exists_rep
        have : g' x = Γ.HenkinModel.VNom l := by
            cases l <;>
            simp [←l_is_rep, Model.VNom]
        rw [←Soundness.SubstitutionNominal g'_var this] at h
        have : sizeOf (φ[l // x]) < sizeOf (ℋ∃ x φ) := sorry -- todo
        rw [Truth] at h
        -- Use the contrapositive of the (Q2) axiom, `⊢ φ[l // x] ⟶ ℋ∃ x φ`
        -- and the (Gen@) and (K@) rules to obtain   `ℋ@ j φ[l // x] ⟶ ℋ∃ x φ ∈ Γ.set`.
        -- Therefore, `@j ∃x φ ∈ Γ.set`.
        admit
      . intro h
        have ⟨l, by_witnessed⟩ := Γ.witnessed.1 h
        have : sizeOf (φ[l // x]) < sizeOf (ℋ∃ x φ) := sorry -- todo
        rw [←Truth] at by_witnessed
        let g' : Assignment Γ.HenkinModel :=
              λ {u : symbs.signature.S} (z : symbs.svar u) =>
                if h : u = st then
                  if h ▸ z = x then
                    h ▸ Γ.HenkinModel.VNom l
                  else Γ.HenkinAsgn z
                else Γ.HenkinAsgn z
        have g'_variant : g'.variant Γ.HenkinAsgn x := by
          unfold g'
          unfold Assignment.variant
          aesop
        exists g'
        exists g'_variant
        rw [←Soundness.SubstitutionNominal]
        . exact by_witnessed
        . exact g'_variant
        . unfold g'
          simp only [↓reduceDIte, ↓reduceIte]
  | ∼φ =>
      simp only [Sat.neg]
      apply Iff.intro
      . intro h
        rw [Truth] at h
        -- Use SelfDual axiom + maximal consistence to rewrite the goal to ∼ ℋ@ j φ ∈ Γ.set,
        -- which by maximal consistence is equivalent to ℋ@ j φ ∉ Γ.set.
        -- This is simply h.
        admit
      . intro h
        rw [Truth]
        -- Same as above.
        admit
  | ℋ∀ x φ =>
      -- ℋ∀ x φ is equivalent to ∼ ℋ∃ x ∼φ,
      -- so in fact this reduces to the negation case.
      admit

end Completeness
