import Hybrid.Completeness.Lindenbaum.Def

namespace Completeness

open Completeness
open Encodable
open Denumerable

variable {α β : Type u}
variable [DecidableEq α] [β_deq : DecidableEq β]
variable {S : Symbols α}
variable {s : S.signature.S}
variable {Λ : AxiomSet S}
variable {Γ : PremiseSet S s}
variable (ext : @S.nominal_extension α β β_deq β)

omit [DecidableEq α] in
lemma Lindenbaum.incl  : ∀ i, (Γ.Lindenbaum ext Λ i).set ⊆ (Γ.LindenbaumExtension ext Λ) := by
  intro i φ h
  simp only [PremiseSet.LindenbaumExtension, Set.mem_setOf_eq]
  exists i

omit [DecidableEq α] in
lemma Lindenbaum.i_increasing : ∀ {i j}, i ≤ j → (Γ.Lindenbaum ext Λ i).set ⊆ (Γ.Lindenbaum ext Λ j).set := by
  intro i j h φ h_φ
  induction j with
  | zero =>
      simp at h
      rw [←h]
      exact h_φ
  | succ n ih =>
      rw [Nat.le_iff_lt_or_eq] at h
      apply Or.elim h
      . intro h
        rw [←Nat.le_iff_lt_add_one] at h
        specialize ih h
        unfold PremiseSet.Lindenbaum
        -- Annoying
        by_cases h_cons : ((Γ.Lindenbaum ext Λ n).set ∪ {ofNat (Form ext.target (ext.m.m.morph_sort s)) n}).consistent (ext.m+ Λ)
        . have : ((Γ.Lindenbaum ext Λ n).set ∪
            {ofNat (Form ext.target (ext.m.m.morph_sort s)) n}).consistent (ext.m+ Λ) = True :=
              by simp_all only [Set.union_singleton]
          rw [this, if_true]
          cases ofNat (Form ext.target (ext.m.m.morph_sort s)) n with
          | «at» k φ =>
              cases φ with
              | neg φ =>
                  cases φ with
                  | bind x φ =>
                      cases φ with
                      | neg φ => simp [ih]
                      | _ => simp [ih]
                  | _ => simp [ih]
              | appl => simp [ih]
              | _ => simp [ih]
          | _ => simp [ih]
        . have : ((Γ.Lindenbaum ext Λ n).set ∪
              {ofNat (Form ext.target (ext.m.m.morph_sort s)) n}).consistent (ext.m+ Λ) = False :=
                by simp_all only [Set.union_singleton]
          rw [this, if_false]
          exact ih
      . intro i_eq
        rw [←i_eq]
        exact h_φ

lemma Lindenbaum.zero_named_consistent {t} {Λ : AxiomSet S} {Γ : PremiseSet S t} (i : S.nominal t) (h1 : Γ.consistent Λ) (h2 : ¬Λ.occurs i) (h3 : ¬Γ.occurs i) :
  (Γ ∪ {ℋNom i}).consistent Λ := by
    intro habs
    rw [Proof.deduction_set'] at habs
    match habs with
    | ⟨Θ_list, habs⟩ =>
      rw [Proof.deduction_singleton] at habs
      apply h1
      exists Θ_list
      refine Proof.name' h2 ?nocc_pf habs
      . simp only [FormL.occurs_nom_implies, FormL.occurs_nom_bot, Bool.or_false]
        apply nominal_not_occurs_premise h3

lemma Lindenbaum.nominal_nocc_at_witness_vars [DecidableEq γ] {symbs : Symbols γ} {s t : symbs.signature.S} {x : symbs.svar t} {Λ : AxiomSet symbs} {Γ : ExtendiblePremiseSet symbs s Λ} {φ : Γ.at_witness_vars} {L : List (Γ.at_witness_vars)} (h : φ.1 = Γ.at_witness x) : φ ∉ L → L.conjunction.occurs (Γ.odd_nominal t x) = false := by
  intro h2

  have h3 : ∀ ψ ∈ L, ψ ≠ φ := by
    -- aesop'd --
    intro ψ a
    simp_all only [Set.mem_setOf_eq, ne_eq, Set.coe_setOf]
    obtain ⟨val, property⟩ := s
    obtain ⟨val_1, property_1⟩ := t
    obtain ⟨val_2, property_2⟩ := φ
    obtain ⟨val_3, property_3⟩ := ψ
    obtain ⟨val_4, property_4⟩ := x
    subst h
    simp_all only [Set.mem_setOf_eq, Subtype.mk.injEq]
    intro a_1
    subst a_1
    simp_all only [not_true_eq_false]

  rw [nominal_not_occurs_conjunction]
  intro ⟨ψ, ⟨⟨t', x'⟩, h4⟩⟩ ψ_in
  simp only [FormL.occurs, Term.occurs, ←h4, ExtendiblePremiseSet.at_witness, FormL.nom_occurs, Bool.false_or,
    dite_eq_right_iff, beq_eq_false_iff_ne, ne_eq]
  intro h5
  subst h5
  intro habs
  rw [odd_nominal_inj habs] at h
  simp only [←h] at h4
  simp only [←h4] at ψ_in
  contradiction

lemma Lindenbaum.zero_witness_consistent (h : Γ.consistent Λ) : ((Γ.embed ext Λ).set ∪ (Γ.embed ext Λ).at_witness_vars).consistent (ext.m+ Λ) := by
  have Γ_plus_consistent : (ext.m+ Γ).consistent (ext.m+ Λ) := ConsistentLift.mpr h
  intro habs
  rw [Proof.deduction_set'] at habs
  match habs with
  | ⟨Θ_list, ⟨⟨witness_list, nodup⟩, habs⟩⟩ =>
    induction witness_list with
    | nil =>
        apply Γ_plus_consistent
        exists Θ_list
        exact ⟨Proof.mp (Classical.choice habs) Proof.top_proof⟩
    | cons φ φs ih =>
        have := φ.2
        simp only [ExtendiblePremiseSet.at_witness_vars, Sigma.exists, Set.mem_setOf_eq] at this
        have ⟨t, ⟨x, h_x⟩⟩ := this
        clear this
        simp only [FiniteChoice.conjunction, List.conjunction, Proof.impex] at habs
        rw [Proof.imp_com, ←h_x] at habs
        -- We will prove the goal by applying q2_nom' and the induction hypothesis
        apply ih (List.nodup_cons.mp nodup).2
        . refine Proof.q2_nom' ?_ ?_ habs
          . apply odd_nom_nocc_axioms
          . simp only [Set.coe_setOf, FormL.occurs_nom_implies, FormL.occurs_nom_bot, Bool.or_false,
            Bool.or_eq_false_iff]
            apply And.intro
            . rw [List.nodup_cons] at nodup
              simp only [FiniteChoice.conjunction]
              apply nominal_nocc_at_witness_vars h_x.symm nodup.1
            . apply nominal_not_occurs_premise
              apply odd_nom_nocc_premises

lemma Lindenbaum.i_exists_consistent
  (Γ : ExtendiblePremiseSet S s Λ)
  (i : ℕ) (h : Γ.set.consistent Λ)
  (h_mem : ℋ@ j (ℋ∃ x φ) ∈ Γ.set)
  : (Γ.set ∪ { ℋ@ j φ[(Γ.prod_even_nominal _ i 0) // x]} ).consistent Λ := by
  apply Proof.exists_consistent
  . assumption
  . exact h_mem
  . apply prod_even_nom_nocc_axioms
  . apply prod_even_nom_nocc_premises

lemma Lindenbaum.i_paste_consistent
  (Γ : ExtendiblePremiseSet S s Λ)
  (i : ℕ) (h : Γ.set.consistent Λ)
  (h_mem : ℋ@ j (ℋ⟨σ⟩ φ) ∈ Γ.set)
  : (Γ.set ∪ Γ.paste_args j σ φ i ).consistent Λ := by
  intro habs
  rw [Proof.deduction_set] at habs
  match habs with
  | ⟨⟨Θ, nodup⟩, habs⟩ =>
    induction Θ with
    | nil =>
        apply h
        apply Proof.premise_mp habs
        apply Proof.theorem_premises
        exact ⟨Proof.top_proof⟩
    | cons χ_elem Θ ih =>
        -- Obtain χ in a manageable form
        have ⟨χ, χ_mem⟩ := χ_elem
        simp at χ_mem
        have ⟨e, χ_eq⟩ := χ_mem
        clear χ_mem χ_elem
        -- Use the induction hypothesis to show consistency
        -- of previous conjunctions
        simp at nodup
        specialize ih nodup.2
        simp [-Set.union_singleton, ←Proof.deduction] at ih
        -- By paste_consistent lemma, derive a contradiction with habs
        --have : ℋ@ j (ℋ⟨σ⟩ φ) ∈ (PremiseSetLindenbaum Γ Λ i).set ∪ { ℋ@ j (ℋ⟨σ⟩ φ) } ∪ { Θ.conjunction } := by simp
        apply (Proof.paste_consistent ih ?mem ?nocc_ax ?nocc_g)
        . rw [χ_eq, Proof.deduction, Proof.deduction]
          apply Proof.premise_mp _ habs
          apply Proof.theorem_premises
          exact ⟨Proof.export_theorem_proof⟩
        case nocc_ax =>
          apply prod_even_nom_nocc_axioms
        case nocc_g =>
          simp
          apply And.intro
          . rw [nominal_not_occurs_conjunction]
            intro ψ ψ_mem
            have := ψ.2
            simp [-Subtype.coe_prop, ExtendiblePremiseSet.paste_args] at this
            have ⟨e', h_e'⟩ := this
            rw [←h_e'] ; clear this h_e'
            simp [FormL.occurs, Term.occurs, FormL.nom_occurs]
            apply And.intro
            . apply And.intro
              . admit
              . intro heq
                subst heq
                simp only
                admit
            . apply And.intro
              . admit
              . -- Here you should finally reach a contradiction with nodup
                intro heq
                admit
          . have : ¬Γ.set.occurs (Γ.prod_even_nominal e.fst i e ) := by apply Lindenbaum.prod_even_nom_nocc_premises
            simp at this
            exact this
        case mem =>
          simp only [Set.union_singleton, Set.mem_insert_iff, h_mem, or_true]

lemma Lindenbaum.i_consistent (h : Γ.consistent Λ) : ∀ i, (Γ.Lindenbaum ext Λ i).set.consistent (ext.m+ Λ) := by
  intro i
  induction i with
  | zero =>
      unfold PremiseSet.Lindenbaum
      intro habs
      simp [-Set.union_singleton] at habs
      apply zero_named_consistent ?i (zero_witness_consistent ext h) _ _
      . exact habs
      . apply prod_even_nom_nocc_axioms
      . apply prod_even_nom_nocc_premises
  | succ n ih =>
      ---------
      let φ_n : Form ext.target (ext.m+ s) := ofNat _ n
      let Γ' : ExtendiblePremiseSet _ _ (ext.m+ Λ) :=  ⟨(Γ.Lindenbaum ext Λ n).set ∪ { φ_n }, enough_nominals_singleton⟩
      have φ_n_def : ofNat _ n = φ_n := rfl
      have Γ'_def : ⟨(Γ.Lindenbaum ext Λ n).set ∪ { φ_n }, enough_nominals_singleton⟩ = Γ' := rfl
      have Γ'_set_def : (Γ.Lindenbaum ext Λ n).set ∪ { φ_n } = Γ'.set := rfl
      unfold PremiseSet.Lindenbaum
      rw [φ_n_def]
      ---------
      by_cases cons : Γ'.set.consistent (ext.m+ Λ)
      . have : Γ'.set.consistent (ext.m+ Λ) = True := by simp only [cons]
        rw [this, if_true]
        rw [←Γ'_def] at cons
        revert cons Γ'_def Γ'_set_def
        -- Really annoying, had to do matching by hand:
        cases φ_n with
        | «at» k φ =>
            cases φ with
            | neg φ =>
                cases φ with
                | bind x φ =>
                    cases φ with
                    | neg φ =>
                        simp only
                        intro Γ'_def Γ'_set_def cons
                        rw [Γ'_def, Γ'_set_def]
                        apply i_exists_consistent
                        . rw [←Γ'_def] ; exact cons
                        . simp [←Γ'_def, FormL.exists]
                    | _ => simp only ; intros; assumption
                | _ => simp only ; intros; assumption
            | appl =>
                simp only
                intro Γ'_def Γ'_set_def cons
                rw [Γ'_def, Γ'_set_def]
                apply i_paste_consistent
                . rw [←Γ'_def] ; exact cons
                . simp [←Γ'_def]
            | _ => simp only ; intros; assumption
        | _ => simp only ; intros; assumption
      . have : Γ'.set.consistent (ext.m+ Λ) = False := by simp only [cons]
        rw [this, if_false]
        exact ih

omit [DecidableEq α] in
lemma Lindenbaum.elems_mem_at_idx (φ_list : FiniteChoice (Γ.LindenbaumExtension ext Λ)) : ∃ i, ∀ φ ∈ φ_list, φ.1 ∈ (Γ.Lindenbaum ext Λ i).set := by
  simp only [instMembershipElemFormFiniteChoice]
  induction φ_list.1 with
  | nil  =>
      exists 0
      intro _ _
      contradiction
  | cons φ φs ih =>
      simp only [List.mem_cons, forall_eq_or_imp]
      have ⟨i, h_i⟩ := φ.2
      have ⟨j, h_j⟩ := ih
      clear ih
      let m := max i j
      have m_geq : m ≥ i ∧ m ≥ j := by aesop
      exists m
      apply And.intro
      . exact i_increasing ext m_geq.1 h_i
      . intro ψ ψ_in
        specialize h_j ψ ψ_in
        exact i_increasing ext m_geq.2 h_j

lemma Lindenbaum.conj_mem_at_idx (h : Γ.consistent Λ) (φ_list : FiniteChoice (Γ.LindenbaumExtension ext Λ)) : ∃ i, φ_list.conjunction ∈ (Γ.Lindenbaum ext Λ i).set := by
  let i := encode φ_list.conjunction
  exists i + 1
  let Γ_conj := (Γ.Lindenbaum ext Λ i).set ∪ { φ_list.conjunction }
  by_cases h_cons : Γ_conj.consistent (ext.m+ Λ)
  . have h_cons_true : Γ_conj.consistent (ext.m+ Λ) = True := by simp only [h_cons]
    unfold PremiseSet.Lindenbaum
    rw [ofNat_of_decode $ encodek φ_list.conjunction, h_cons_true, if_true]
      -- Really annoying, had to do matching by hand (simp is failing):
    cases φ_list.conjunction with
    | «at» k φ =>
        cases φ with
        | neg φ =>
            cases φ with
            | bind x φ =>
                cases φ with
                | neg φ => simp only [Set.union_singleton, Set.mem_insert_iff, FormL.at.injEq,
                    heq_eq_eq, true_and, true_or, or_true]
                | _ => simp only [Set.union_singleton, Set.mem_insert_iff, true_or]
            | _ => simp only [Set.union_singleton, Set.mem_insert_iff, true_or]
        | appl => simp only [Set.union_singleton, Set.mem_union, Set.mem_insert_iff, true_or,
          Set.mem_setOf_eq]
        | _ => simp only [Set.union_singleton, Set.mem_insert_iff, true_or]
    | _ => simp only [Set.union_singleton, Set.mem_insert_iff, true_or]
  . -- If Γ.Lindenbaum ext Λ i ∪ { φ_list.conjunction } were inconsistent,
    --  then one could prove from Γ.Lindenbaum ext Λ i that φ_list.conjunction ⟶ ⊥.
    -- But all formulas in φ_list occur together at some index j in the family.
    --   (Namely, the index j is the maximum + 1 of the respective formulas' encodings.)
    -- So take index m = max(i, j).
    --   We have  Γ.Lindenbaum ext Λ m ⊢ φ_list.conjunction ⟶ ⊥, by proof monotonicity.
    --   But also Γ.Lindenbaum ext Λ m ⊢ φ_list.conjunction, since m ≥ j.
    -- Hence Γ.Lindenbaum ext Λ m is inconsistent, which contradicts an earlier lemma.
    exfalso
    simp [PremiseSet.consistent] at h_cons
    simp only [Γ_conj, Proof.deduction] at h_cons
    have ⟨j, h_j⟩ := elems_mem_at_idx ext φ_list
    have ⟨φ_list', h'⟩ := choice_swap h_j
    rw [h'] at h_cons
    have h_cons' : (Γ.Lindenbaum ext Λ j).set ⊢(ext.m+ Λ) φ_list'.conjunction := Proof.premise_conjunction
    let m := max i j
    have m_geq : m ≥ i ∧ m ≥ j := by aesop
    have : (Γ.Lindenbaum ext Λ i).set ⊆ (Γ.Lindenbaum ext Λ m).set := i_increasing ext m_geq.1
    have h_cons := Proof.monotonicity this h_cons
    have : (Γ.Lindenbaum ext Λ j).set ⊆ (Γ.Lindenbaum ext Λ m).set := i_increasing ext m_geq.2
    have h_cons' := Proof.monotonicity this h_cons'
    have pf_bot := Proof.premise_mp h_cons h_cons'
    apply i_consistent ext h m
    exact pf_bot

lemma Lindenbaum.consistent (h : Γ.consistent Λ) : (Γ.LindenbaumExtension ext Λ).consistent (ext.m+ Λ) := by
    intro ⟨φ_list, habs⟩
    have ⟨idx, h_mem⟩ := conj_mem_at_idx ext h φ_list
    apply i_consistent ext h idx
    have : (Γ.Lindenbaum ext Λ idx).set = (Γ.Lindenbaum ext Λ idx).set ∪ { φ_list.conjunction } := by
      simp_all only [Set.union_singleton, Set.insert_eq_of_mem]
    rw [this, Proof.deduction]
    apply Proof.theorem_premises habs

lemma Lindenbaum.mcs (h : Γ.consistent Λ) : (Γ.LindenbaumExtension ext Λ).maximal_consistent (ext.m+ Λ) := by
  apply And.intro
  . exact consistent ext h
  . intro Γ'
    intro h2
    simp [PremiseSet.consistent]
    rw [Set.ssubset_iff_exists] at h2
    have ⟨l, ⟨φ, ⟨h21, h22⟩⟩⟩ := h2
    clear h2
    simp [PremiseSet.LindenbaumExtension] at h22
    specialize h22 (encode φ + 1)
    let Γ'' : PremiseSet ext.target (ext.m+ s) := (Γ.Lindenbaum ext Λ (encode φ)).set ∪ { φ };
    by_cases h_cons : Γ''.consistent (ext.m+ Λ)
    . -- Annoying: simp is failing with: "failed to compile definition, consider marking it as 'noncomputable'",
      --  which looks very much like a bug (why try to compile code in a theorem?).
      -- Had to do many manual rewrites.
      have Γ''_def : ((Γ.Lindenbaum ext Λ (encode φ)).set ∪ {φ}) = Γ'' := rfl
      let L := Γ.Lindenbaum ext Λ (encode φ + 1)
      exfalso
      apply h22
      clear h22
      have h_cons_true : Γ''.consistent (ext.m+ Λ) = True := by simp only [h_cons]
      rw [PremiseSet.Lindenbaum, ofNat_of_decode $ encodek φ, h_cons_true, if_true]
      -- Really annoying, had to do matching by hand:
      cases φ with
      | «at» k φ =>
          cases φ with
          | neg φ =>
              cases φ with
              | bind x φ =>
                  cases φ with
                  | neg φ => simp only [Set.union_singleton, Set.mem_insert_iff, FormL.at.injEq,
                      heq_eq_eq, true_and, true_or, or_true]
                  | _ => simp only [Set.union_singleton, Set.mem_insert_iff, true_or]
              | _ => simp only [Set.union_singleton, Set.mem_insert_iff, true_or]
          | appl => simp only [Set.union_singleton, Set.mem_union, Set.mem_insert_iff, true_or,
            Set.mem_setOf_eq]
          | _ => simp only [Set.union_singleton, Set.mem_insert_iff, true_or]
      | _ => simp only [Set.union_singleton, Set.mem_insert_iff, true_or]
    . simp [PremiseSet.consistent] at h_cons
      apply Proof.monotonicity _ h_cons
      simp only [Γ'', Set.union_subset_iff, Set.singleton_subset_iff]
      apply And.intro _ h21
      trans
      . apply incl
      . assumption

lemma Lindenbaum.consistent_union (h : Γ.consistent Λ) (h2 : φ ∈ Γ.LindenbaumExtension ext Λ) : ∀ i, ((Γ.Lindenbaum ext Λ i).set ∪ { φ }).consistent (ext.m+ Λ) := by
    intro i
    by_contra h_not_cons
    have is_mcs := mcs ext h
    apply mcs_em is_mcs
    simp only [PremiseSet.consistent, Classical.not_not] at h_not_cons
    rw [Proof.deduction, Proof.pf_not] at h_not_cons
    exact ⟨h2, (mcs_pf is_mcs).mp $ Proof.monotonicity (incl ext i) h_not_cons⟩

omit [DecidableEq α] in
lemma Lindenbaum.named  : (Γ.LindenbaumExtension ext Λ).named := by
  unfold PremiseSet.named
  simp only [PremiseSet.LindenbaumExtension, Set.mem_setOf_eq]
  rw [exists_swap]
  exists 0
  simp [PremiseSet.Lindenbaum]

lemma Lindenbaum.pasted (h : Γ.consistent Λ) : (Γ.LindenbaumExtension ext Λ).pasted := by
  intro _ _ t σ k χ h2 e
  let sᵢ := e.sort
  let φ  := e.form
  let C  := e.ctx
  let form : Form ext.target (ext.m+ s) := ℋ@ k(ℋ⟨σ⟩χ)
  let j_set : ExtendiblePremiseSet _ _ (ext.m+ Λ) := ⟨(Γ.Lindenbaum ext Λ (encode form)).set ∪ { form }, enough_nominals_singleton⟩
  let j : ext.target.nominal sᵢ := j_set.even_nominal sᵢ $ Prod.mk (encode form) e
  exists j
  have ⟨i, occ_i⟩ := h2
  have is_mcs := mcs ext h
  let Γ' : PremiseSet ext.target (ext.m+ s) := (Γ.Lindenbaum ext Λ (encode form)).set.insert form
  have h_cons : Γ'.consistent (ext.m+ Λ) := by
    have := consistent_union ext h h2 (encode form)
    simp [Γ', form, Set.union_singleton, insert] at this ⊢
    exact this
  apply And.intro
  . -- It suffices to show that
    --  (ℋ@ k(ℋ⟨σ⟩C[ℋNom j]) ⋀ ℋ@ j φ) ∈ Γ.LindenbaumExtension ext Λ,
    -- since by Γ.LindenbaumExtension ext Λ being an MCS, that implies the desired conclusion.
    apply mcs_and_left is_mcs (ℋ@ j φ)
    exists (encode form) + 1
    unfold PremiseSet.Lindenbaum
    simp only [ofNat_of_decode $ encodek form, Set.union_singleton, h_cons, ↓reduceIte,
      Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq, form]
    apply Or.inr
    exists e
    simp only [FormL.and, FormL.neg.injEq, FormL.or.injEq, FormL.at.injEq, heq_eq_eq,
      FormL.appl.injEq, true_and]
    apply And.intro
    . rw [ofNat_encode]
    . apply And.intro
      . simp only [FormL.Elem.sort, sᵢ]
      . apply And.intro
        . rw [ofNat_encode]
        . simp only [FormL.Elem.form, φ]
  . apply mcs_and_right is_mcs (ℋ@ k(ℋ⟨σ⟩C[ℋNom j]))
    -- From this point on, the whole proof is identical to the other And branch
    exists (encode form) + 1
    let Γ' : PremiseSet ext.target (ext.m+ s) := (Γ.Lindenbaum ext Λ (encode form)).set.insert form
    unfold PremiseSet.Lindenbaum
    simp only [ofNat_of_decode $ encodek form, Set.union_singleton, h_cons, ↓reduceIte,
      Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq, form]
    apply Or.inr
    exists e
    simp only [FormL.and, FormL.neg.injEq, FormL.or.injEq, FormL.at.injEq, heq_eq_eq,
      FormL.appl.injEq, true_and]
    apply And.intro
    . rw [ofNat_encode]
    . apply And.intro
      . rw [ofNat_encode]
      . simp only

lemma Lindenbaum.witnessed (h : Γ.consistent Λ) : (Γ.LindenbaumExtension ext Λ).at_witnessed := by
  apply And.intro
  . intro s' t x φ k h2
    simp [PremiseSet.LindenbaumExtension]
    let j_set : ExtendiblePremiseSet _ _ (ext.m+ Λ) := ⟨(Γ.Lindenbaum ext Λ (@encode (Form ext.target (ext.m+ s)) _ (ℋ@ k(ℋ∃ x φ)))).set ∪ { ℋ@ k(ℋ∃ x φ) }, enough_nominals_singleton⟩
    exists j_set.even_nominal _ $ Prod.mk (@encode (Form ext.target (ext.m+ s)) _ (ℋ@ k(ℋ∃ x φ))) 0
    exists (@encode (Form ext.target (ext.m+ s)) _ (ℋ@ k(ℋ∃ x φ)) + 1)
    let Γ' : PremiseSet ext.target (ext.m+ s) := (insert (ℋ@ k(ℋ∃ x φ)) (PremiseSet.Lindenbaum ext Λ Γ (@encode (Form ext.target (ext.m+ s)) _ (ℋ@ k(ℋ∃ x φ)))).set)
    have Γ'_def : (insert (ℋ@ k(ℋ∃ x φ)) (PremiseSet.Lindenbaum ext Λ Γ (encode (ℋ@ k(ℋ∃ x φ)))).set) = Γ' := rfl
    have h_cons : Γ'.consistent (ext.m+ Λ) = True := by
      have := consistent_union ext h h2 (@encode (Form ext.target (ext.m+ s)) _ (ℋ@ k(ℋ∃ x φ)))
      simp [Γ', Set.union_singleton, insert] at this ⊢
      exact this
    unfold PremiseSet.Lindenbaum
    rw [ofNat_encode]
    simp [Γ'_def, h_cons, j_set]
  . intro t x
    exists (Γ.embed ext Λ).odd_nominal _ x
    exists 0
    unfold PremiseSet.Lindenbaum
    simp only [Set.mem_union, Set.mem_setOf_eq]
    apply Or.inl ; apply Or.inr
    exists ⟨t, x⟩

lemma Lindenbaum (h : Γ.consistent Λ) : ∃ Γ' : NamedPastedWitnessedMCS ext.target (ext.m+ s) (ext.m+ Λ), (ext.m+ Γ) ⊆ Γ'.set := by
  exists ⟨Γ.LindenbaumExtension ext Λ, Lindenbaum.named ext, Lindenbaum.pasted ext h, Lindenbaum.witnessed ext h, Lindenbaum.mcs ext h⟩
  simp only
  trans
  . show (ext.m+ Γ) ⊆ (Γ.Lindenbaum ext Λ 0).set
    simp only [PremiseSet.Lindenbaum]
    apply Set.subset_union_of_subset_left
    exact Set.subset_union_left
  . apply Lindenbaum.incl

end Completeness
