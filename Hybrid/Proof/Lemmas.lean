import Hybrid.Proof.Proofs
import Hybrid.Language.Context.Elem

namespace Proof

open Proof

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {Λ : AxiomSet symbs}

section Provable

  lemma top : ⊢(Λ, s) ℋ⊤ := ⟨top_proof⟩

  lemma impex : ⊢ (Λ, s) (φ ⋀ ψ ⟶ χ) ↔ ⊢ (Λ, s) (φ ⟶ ψ ⟶ χ) := by
    apply Iff.intro
    . intro ⟨pf⟩
      exact ⟨export_proof pf⟩
    . intro ⟨pf⟩
      exact ⟨import_proof pf⟩

  lemma imp_com : ⊢ (Λ, s) (φ ⟶ ψ ⟶ χ) ↔ ⊢ (Λ, s) (ψ ⟶ φ ⟶ χ) := by
  apply Iff.intro <;> (
    intro ⟨pf⟩; exact ⟨imp_com_proof pf⟩
  )

end Provable


section Deduction

  def deduction_list {Γ : PremiseSet symbs s} {L : List Γ} {φ : Γ} (h : φ ∈ L) : Proof Λ s (L.conjunction ⟶ φ ⟶ ψ) → Proof Λ s (L.conjunction ⟶ ψ) := by
    intro pf
    induction L generalizing ψ with
    | nil => contradiction
    | cons χ L ih =>
        by_cases eq : φ = χ
        . subst eq
          have l1 := imp_com_proof' $ imp_com_proof $ export_proof pf
          have l2 := imp_idem_proof l1
          have l3 := import_proof $ imp_com_proof l2
          exact l3
        . simp [eq] at h ; clear eq
          have l1 := imp_com_proof' $ export_proof pf
          specialize ih h l1
          have l2 := import_proof ih
          exact l2

  def deduction_dedup {Γ : PremiseSet symbs s} {L : List Γ}: Proof Λ s (L.conjunction ⟶ ψ) → Proof Λ s (L.dedup.conjunction ⟶ ψ) := by
    induction L generalizing ψ with
    | nil => exact id
    | cons φ L ih =>
        intro l1
        have l2 := export_proof l1
        specialize ih l2
        clear l1 l2
        by_cases mem : φ ∈ L
        . have dedup_eq : (φ :: L).dedup = L.dedup := List.dedup_cons_of_mem mem
          rw [dedup_eq]
          clear dedup_eq
          rw [←List.mem_dedup] at mem
          exact deduction_list mem ih
        . have l1 := import_proof ih
          have : (φ :: L.dedup).conjunction = L.dedup.conjunction ⋀ φ := rfl
          rw [←this] at l1
          have dedup_eq : (φ :: L.dedup) = (φ :: L).dedup := by
            simp_all only [not_false_eq_true, List.dedup_cons_of_notMem]
          rw [dedup_eq] at l1
          exact l1

  lemma monotonicity (h : Γ ⊆ Δ) : (Γ ⊢(Λ) φ) → (Δ ⊢(Λ) φ) := by
    intro ⟨⟨Γ_list, nodup⟩, ⟨pf⟩⟩
    induction Γ_list generalizing φ with
    | nil =>
        exists ⟨[], List.nodup_nil⟩
        exact ⟨pf⟩
    | cons ψ Γ_list ih =>
        have l1 := export_proof pf
        simp at nodup
        specialize ih nodup.2 l1
        let ψ_Δ : Δ.Elem := ⟨ψ.1, h ψ.2⟩
        have : ψ.1 = ψ_Δ.1 := rfl
        rw [this] at ih
        clear this
        have ⟨⟨Δ_list, _⟩, ⟨l2⟩⟩ := ih
        simp at l2
        have l3 := import_proof l2
        let Δ_list' := ψ_Δ :: Δ_list
        have : Δ_list.conjunction ⋀ ψ_Δ = Δ_list'.conjunction := rfl
        rw [this] at l3
        clear this
        have l4 := deduction_dedup l3
        exists ⟨Δ_list'.dedup, Δ_list'.nodup_dedup⟩
        exact ⟨l4⟩

  lemma deduction_set : (Γ ∪ Δ) ⊢(Λ) ψ ↔ ∃ φ_list : FiniteChoice Δ, Γ ⊢(Λ) (φ_list.conjunction ⟶ ψ) := by
    apply Iff.intro
    . intro ⟨⟨both_lists, nodup⟩, ⟨l1⟩⟩
      induction both_lists generalizing ψ with
      | nil =>
          exists ⟨[], List.nodup_nil⟩
          exists ⟨[], List.nodup_nil⟩
          exact ⟨Proof.mp (Proof.prop1 _ _) l1⟩
      | cons h t ih =>
          simp at nodup
          simp at l1
          have l2 := export_proof l1
          specialize ih nodup.2 l2
          apply Or.elim $ (Set.mem_union _ _ _).mpr h.2
          . intro h_Γ
            have ⟨Θ', ⟨⟨Θ, nodup⟩, ⟨l1⟩⟩⟩ := ih
            have l2 := import_proof $ imp_com_proof' l1
            let Γ_list := ⟨h, h_Γ⟩ :: Θ
            have : Γ_list.conjunction = Θ.conjunction ⋀ h := by simp [Γ_list]
            rw [←this] at l2
            have l3 := deduction_dedup l2
            let φ_list : FiniteChoice Γ := ⟨Γ_list.dedup, Γ_list.nodup_dedup⟩
            have : Γ_list.dedup.conjunction = φ_list.conjunction := rfl
            rw [this] at l3
            exists Θ'
            exists φ_list
            exact ⟨l3⟩
          . intro h_Δ
            have ⟨⟨Θ, nodup⟩, ⟨Θ', ⟨l1⟩⟩⟩ := ih
            have l2 := import_proof $ imp_com_proof' $ imp_com_proof l1
            let Δ_list := ⟨h, h_Δ⟩ :: Θ
            have : Δ_list.conjunction = Θ.conjunction ⋀ h := rfl
            rw [←this] at l2
            have l3 := deduction_dedup l2
            have l4 := imp_com_proof l3
            let φ_list : FiniteChoice Δ := ⟨Δ_list.dedup, Δ_list.nodup_dedup⟩
            have : Δ_list.dedup.conjunction = φ_list.conjunction := rfl
            rw [this] at l4
            exists φ_list
            exists Θ'
            exact ⟨l4⟩
    . intro ⟨⟨Δ_list, nodup⟩, ⟨⟨Γ_list, nodup'⟩, ⟨pf⟩⟩⟩
      cases Δ_list with
      | nil =>
          have : Γ ⊆ Γ ∪ Δ := Set.subset_union_left
          apply monotonicity this
          have l1 := imp_com_proof pf
          have l2 := mp l1 top_proof
          exists ⟨Γ_list, nodup'⟩
          exact ⟨l2⟩
      | cons hΔ tΔ =>
          simp at pf
          induction Γ_list generalizing ψ with
          | nil =>
              have : Δ ⊆ Γ ∪ Δ := Set.subset_union_right
              apply monotonicity this
              have l1 := mp pf top_proof
              let Δ_list := hΔ :: tΔ
              have : tΔ.conjunction ⋀ ↑hΔ = Δ_list.conjunction := rfl
              rw [this] at l1
              exists ⟨Δ_list, nodup⟩
              exact ⟨l1⟩
          | cons hΓ tΓ ih =>
              simp at nodup'
              simp at pf
              have l1 := imp_com_proof' $ export_proof pf
              specialize ih nodup'.2 l1
              have ⟨⟨both_lists, nodup2⟩, ⟨l2⟩⟩ := ih
              simp only [FiniteChoice.conjunction] at l2
              let hΓΔ : (Γ ∪ Δ).Elem := ⟨hΓ.1, by simp⟩
              have : hΓ.1 = hΓΔ.1 := rfl
              rw [this] at l2
              clear this
              have l3 := import_proof l2
              let ΓΔ_list := hΓΔ :: both_lists
              have : both_lists.conjunction ⋀ hΓΔ = ΓΔ_list.conjunction := rfl
              rw [this] at l3
              clear this
              have l4 := deduction_dedup l3
              exists ⟨ΓΔ_list.dedup, ΓΔ_list.nodup_dedup⟩
              simp only [FiniteChoice.conjunction]
              exact ⟨l4⟩

  lemma deduction_set' : (Γ ∪ Δ) ⊢(Λ) ψ ↔ ∃ φ_list : FiniteChoice Γ, Δ ⊢(Λ) (φ_list.conjunction ⟶ ψ) := by
    rw [Set.union_comm]
    apply deduction_set

  theorem deduction : (Γ ∪ { φ }) ⊢(Λ) ψ ↔ Γ ⊢(Λ) (φ ⟶ ψ) := by
    apply Iff.intro
    . rw [deduction_set]
      intro ⟨⟨ch, nodup⟩, h⟩
      simp at h
      cases ch with
      | nil =>
          simp at h
          have ⟨ch, ⟨l1⟩⟩ := h
          have l2 := mp (imp_com_proof l1) top_proof
          have l3 := Proof.mp (Proof.prop1 _ φ) l2
          have l4 := imp_com_proof l3
          exists ch
          exact ⟨l4⟩
      | cons φ_ φs =>
          cases φs with
          | nil =>
              have h1 := φ_.2
              simp only [Set.mem_singleton_iff] at h1
              simp only [List.conjunction, h1] at h
              have ⟨list, ⟨l1⟩⟩ := h
              have l2 := export_proof $ imp_com_proof l1
              have l3 := mp l2 top_proof
              have l4 := imp_com_proof l3
              exists list
              exact ⟨l4⟩
          | cons a b =>
              have h1 := φ_.2
              have h2 := a.2
              simp only [Set.mem_singleton_iff] at h1 h2
              aesop
    . rw [deduction_set]
      intro ⟨list, ⟨l1⟩⟩
      exists ⟨[⟨φ, by simp⟩], by simp⟩
      exists list
      simp at l1 ⊢
      have l2 := imp_com_proof l1
      have l3 := mp (prop1 _ (ℋ⊤)) l2
      have l4 := import_proof l3
      have l5 := imp_com_proof l4
      exact ⟨l5⟩

end Deduction

section PremiseLemmas

  theorem theorem_empty_premises : ⊢(Λ, s) φ ↔ ∅ ⊢(Λ) φ := by
    apply Iff.intro
    . intro ⟨pf⟩
      exists ⟨[], List.nodup_nil⟩
      apply Nonempty.intro
      exact mp (prop1 _ _) pf
    . intro ⟨⟨ch, _⟩, ⟨pf⟩⟩
      have : ch = [] := by aesop
      simp only [FiniteChoice.conjunction, this, List.conjunction] at pf
      apply Nonempty.intro
      exact mp pf top_proof

  lemma deduction_singleton {φ ψ}  : { φ } ⊢(Λ) ψ ↔ ⊢(Λ, s) (φ ⟶ ψ) := by
    simp only [theorem_empty_premises, ←deduction, Set.union_singleton, insert_empty_eq]

  lemma theorem_premises (h : ⊢(Λ, s) φ) (Γ : PremiseSet symbs s) : Γ ⊢(Λ) φ := by
    rw [theorem_empty_premises] at h
    have : ∅ ⊆ Γ := by simp only [Set.empty_subset]
    exact monotonicity this h

  lemma premise_provable {Γ : PremiseSet symbs s} (h : φ ∈ Γ) : Γ ⊢(Λ) φ := by
    have : Γ ∪ { φ } = Γ := by simp only [Set.union_singleton, h, Set.insert_eq_of_mem]
    rw [←this, deduction]
    apply theorem_premises
    exact ⟨id_proof⟩

  lemma premise_mp : Γ ⊢(Λ) (φ ⟶ ψ) → (Γ ⊢(Λ) φ) → Γ ⊢(Λ) ψ := by
    intro h1 h2
    -- need to concatenate h1's and h2's conjunctions
    admit

  lemma premise_conj_intro : ((Γ ⊢(Λ) φ) ∧ (Γ ⊢(Λ) ψ)) → Γ ⊢(Λ) (φ ⋀ ψ) := by
    intro ⟨h1, h2⟩
    apply premise_mp
    apply premise_mp (theorem_premises ⟨conj_intro_proof⟩ _) h1
    exact h2

  lemma premise_conjunction {φ_list : FiniteChoice Γ} : Γ ⊢(Λ) φ_list.conjunction := by
    simp
    induction φ_list.1 with
    | nil =>
        apply theorem_premises
        exact ⟨top_proof⟩
    | cons φ φ_list ih =>
        apply premise_conj_intro
        exact And.intro ih (premise_provable φ.2)

  lemma pf_not (Λ : AxiomSet symbs) : Γ ⊢(Λ) (φ ⟶ ℋ⊥) ↔ Γ ⊢(Λ) (∼φ) := sorry

  lemma premise_iff_l : Γ ⊢(Λ) (φ ←→ ψ) → (Γ ⊢(Λ) (φ ⟶ ψ)) := sorry

  lemma premise_gen_at {Γ : PremiseSet symbs s} (pf1 : Γ ⊢(Λ) (ℋNom j)) (pf2 : Γ ⊢(Λ) φ) : Γ ⊢(Λ) (ℋ@ j φ) :=
    premise_mp (premise_iff_l $ premise_mp (theorem_premises (.intro (intro j φ)) Γ) pf1) pf2

end PremiseLemmas

section Lindenbaum

  lemma name' {i : symbs.nominal s} (h1 : ¬Λ.occurs i ) (h2 : φ.occurs i = false) : ⊢(Λ, s) (i ⟶ φ) → ⊢(Λ, s) φ := by
    intro (.intro pf)
    apply Nonempty.intro
    exact name'_proof h1 h2 pf

  lemma q2_nom' (h1 : ¬Λ.occurs i) (h2 : φ.occurs i = false) : ⊢(Λ, s) (ℋ@ i (ℋVar x) ⟶ φ) → ⊢(Λ, s) φ := by
    intro (.intro pf)
    apply Nonempty.intro
    exact q2_nom'_proof h1 h2 pf

  lemma exists_lemma {i : symbs.nominal t} (h1 : ¬Λ.occurs i) (h2 : ¬Γ.occurs i) : Γ ⊢(Λ) (ℋ@ j φ[i // x] ⟶ ℋ⊥) → Γ ⊢(Λ) (ℋ@j (ℋ∃x φ) ⟶ ℋ⊥) := by
    intro ⟨ch, .intro pf⟩
    exists ch
    apply Nonempty.intro
    apply exists_lemma_proof h1 _ pf
    simp only [FormL.occurs, Term.occurs, Bool.not_eq_true]
    apply nominal_not_occurs_premise h2

  lemma exists_consistent {s t} {Λ : AxiomSet symbs} {Γ : PremiseSet symbs s}
    {x : symbs.svar t} {i : symbs.nominal t} (h1 : Γ.consistent Λ) (h2 : ℋ@ j (ℋ∃ x φ) ∈ Γ)
    (h3 : ¬Λ.occurs i) (h4 : ¬Γ.occurs i) :
    (Γ ∪ {ℋ@ j (φ[i // x])}).consistent Λ := by
      intro habs
      rw [Proof.deduction_set'] at habs
      match habs with
      | ⟨Γ_list, habs⟩ =>
        rw [Proof.deduction_singleton, Proof.imp_com] at habs
        have l1 : Γ ⊢(Λ) (ℋ@ j φ[i//x] ⟶ ℋ⊥) := ⟨Γ_list, habs⟩
        have l2 : Γ ⊢(Λ) (ℋ@ j(ℋ∃ x φ)) := premise_provable h2
        apply h1
        have l3 := exists_lemma h3 h4 l1
        have l4 := premise_mp l3 l2
        exact l4

  lemma paste_consistent {s} {Λ : AxiomSet symbs} {Γ : PremiseSet symbs s}
    (h1 : Γ.consistent Λ) (h2 : ℋ@ j (ℋ⟨σ⟩ φ) ∈ Γ) {e : φ.Elem}
    {i : symbs.nominal e.1} (h3 : ¬Λ.occurs i) (h4 : ¬Γ.occurs i):
    (Γ ∪ {ℋ@ j (ℋ⟨σ⟩ e.2.2[ℋNom i]) ⋀ ℋ@ i e.2.1}).consistent Λ := by
      rename_i t _ _
      intro habs
      rw [deduction_set'] at habs
      match habs with
      | ⟨Γ_list, habs⟩ =>
        rw [deduction_singleton] at habs
        have ⟨l1⟩ := habs
        let C := (ℋNom i).subst_to_ctx e.2.2
        /- Proving restrictions for Paste rule -/
        have subst_is_φ : C[e.2.1] = φ := e.2.2.subst_in_iso $ (ℋNom i).subst_to_ctx_iso e.2.2
        have neq_nom : i ≠ₛ j := by
          intro heq
          by_cases trivial : e.1 = t
          . subst trivial
            simp only [ne_eq]; intro habs
            subst habs
            apply h4
            exists (ℋ@ i(ℋ⟨σ⟩φ))
            apply And.intro h2
            simp [FormL.occurs, Term.occurs, FormL.nom_occurs]
          . contradiction
        have nocc_conj : (Γ_list.conjunction ⟶ ℋ⊥).occurs i = false := by
          simp only [FormL.occurs_nom_implies, FormL.occurs_nom_bot, Bool.or_false]
          apply nominal_not_occurs_premise h4
        have nocc_φ : C[e.2.1].occurs i = false := by
          rw [subst_is_φ]
          simp at h4
          specialize h4 _ h2
          simp only [FormL.occurs, Term.occurs, FormL.nom_occurs, Bool.or_eq_false_iff] at h4
          exact h4.1
        /- Done, now applying Paste rule  -/
        have l2 := subst_is_φ ▸ paste C neq_nom h3 nocc_conj nocc_φ l1
        have l3 : Γ ⊢(Λ) (_ ⟶ ℋ⊥) := ⟨Γ_list, ⟨imp_com_proof l2⟩⟩
        have l4 : Γ ⊢(Λ) _ := premise_provable h2
        have l4 := premise_mp l3 l4
        apply h1
        exact l4

end Lindenbaum

end Proof
