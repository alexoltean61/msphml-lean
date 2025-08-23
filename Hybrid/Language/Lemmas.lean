import Hybrid.Language.Form
import Hybrid.Language.Substitution

variable {α : Type u}
variable [DecidableEq α]

lemma choice_swap {φ_list : FiniteChoice Γ} (h : ∀ φ ∈ φ_list, φ.1 ∈ Δ) : ∃ (φ_list' : FiniteChoice Δ), φ_list.conjunction = φ_list'.conjunction := sorry

lemma nominal_occurs_context {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (j : symbs.nominal s) (φ: FormL symbs sorts) :
  φ.occurs j ↔ ∃ (t : symbs.signature.S) (ψ : Form symbs t) (_ : ψ.Context φ), ψ.occurs j := by
  simp only [FormL.occurs, Term.occurs]
  induction φ with
  | cons φ ψ ih1 ih2 =>
      simp only [FormL.nom_occurs, Bool.or_eq_true, exists_const_iff]
      apply Iff.intro
      . intro h
        apply Or.elim h
        . intro h
          simp [h, -Subtype.exists] at ih1
          have ⟨t, ⟨ψ, ⟨ne, h⟩⟩⟩ := ih1
          have C := Classical.choice ne
          cases C
          . rename_i t _ _ _ _
            exists t
            exists φ
            apply And.intro _ h
            apply Nonempty.intro
            exact FormL.Context.head
        . intro h
          simp [h, -Subtype.exists] at ih2
          have ⟨t, ⟨ψ, ⟨ne, h⟩⟩⟩ := ih2
          exists t
          exists ψ
          apply And.intro _ h
          apply Nonempty.intro
          apply FormL.Context.tail
          exact Classical.choice ne
      . intro ⟨s, ⟨ψ, ⟨ne, hocc⟩⟩⟩
        have C := Classical.choice ne
        clear ne
        cases C
        . exact Or.inl hocc
        . rename_i C
          apply Or.inr
          rw [ih2]
          exists s
          exists ψ
          exists C
  | appl σ φ ih =>
      simp only [FormL.nom_occurs]
      rw [ih]
      apply Iff.intro
      . intro ⟨_, ⟨ψ, ⟨C, hocc⟩⟩⟩
        rename_i t _
        exists t
        exists ℋ⟨σ⟩ φ
        exists .refl
        cases C
        . exact hocc
        . simp [FormL.nom_occurs]
          exact Or.inl hocc
        . simp only [FormL.nom_occurs, Bool.or_eq_true] at ih ⊢
          rw [ih]
          rename_i u _ _ _ C _
          exists u
          exists ψ
          exists .tail C
      . intro ⟨_, ⟨ψ, ⟨C, hocc⟩⟩⟩
        rename_i t _
        cases C
        simp only [FormL.nom_occurs, ih] at hocc
        exact hocc
  | or φ ψ ih1 ih2 =>
        simp only [FormL.nom_occurs, Bool.or_eq_true, ih1, ih2]
        apply Iff.intro
        . intro h
          rename_i t
          exists t
          exists φ⋁ψ
          exists .refl
          simp only [FormL.nom_occurs, Bool.or_eq_true]
          apply Or.elim h
          . clear h
            intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
            cases C
            exact Or.inl h
          . clear h
            intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
            cases C
            exact Or.inr h
        . intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
          cases C
          simp only [FormL.nom_occurs, Bool.or_eq_true] at h
          rename_i t
          apply Or.elim h
          . intro h
            apply Or.inl
            exists t
            exists φ
            exists .refl
          . intro h
            apply Or.inr
            exists t
            exists ψ
            exists .refl
  | neg φ ih =>
        simp only [FormL.nom_occurs, ih]
        rename_i t
        apply Iff.intro
        . intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
          cases C
          exists t
          exists ∼φ
          exists .refl
        . intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
          cases C
          exists t
          exists φ
          exists .refl
  | «at» k φ ih =>
        rename_i t _
        by_cases same_sort : s = t
        . subst same_sort
          by_cases heq : j = k
          . subst heq
            simp only [FormL.nom_occurs, ↓reduceDIte, BEq.rfl, Bool.or_true, true_iff]
            rename_i t
            exists t
            exists ℋ@j φ
            exists .refl
            simp [FormL.nom_occurs]
          . simp only [FormL.nom_occurs, ↓reduceDIte, Bool.or_eq_true, ih, beq_iff_eq, heq,
            or_false]
            apply Iff.intro
            . intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
              cases C
              rename_i u
              exists u
              exists ℋ@k φ
              exists .refl
              simp [FormL.nom_occurs, h]
            . intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
              cases C
              exists s
              exists φ
              exists .refl
              simp [FormL.nom_occurs, heq] at h
              exact h
        . simp only [FormL.nom_occurs, same_sort, ↓reduceDIte, Bool.or_false, ih]
          apply Iff.intro
          . intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
            cases C
            rename_i u
            exists u
            exists ℋ@k φ
            exists .refl
            simp [FormL.nom_occurs, h]
          . intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
            cases C
            exists t
            exists φ
            exists .refl
            simp [FormL.nom_occurs, same_sort] at h
            exact h
  | bind x φ ih =>
        simp only [FormL.nom_occurs, ih]
        rename_i t
        apply Iff.intro
        . intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
          cases C
          exists t
          exists ℋ∀ x φ
          exists .refl
        . intro ⟨_, ⟨_, ⟨C, h⟩⟩⟩
          cases C
          exists t
          exists φ
          exists .refl
  | @nom t k =>
        by_cases same_sort : s = t
        . subst same_sort
          by_cases heq : j = k
          . subst heq
            simp only [FormL.nom_occurs, ↓reduceDIte, BEq.rfl, true_iff]
            exists s
            exists j
            exists .refl
            simp [FormL.nom_occurs]
          . simp only [FormL.nom_occurs, ↓reduceDIte, beq_iff_eq, heq, false_iff, not_exists,
            Bool.not_eq_true]
            intro _ _ C
            cases C
            simp [FormL.nom_occurs, heq]
        . simp only [FormL.nom_occurs, same_sort, ↓reduceDIte, Bool.false_eq_true, false_iff,
          not_exists, Bool.not_eq_true]
          intro _ _ C
          cases C
          simp [FormL.nom_occurs, same_sort]
  | _ =>
      simp only [FormL.nom_occurs, Bool.false_eq_true, exists_const_iff, false_iff,
        not_exists, not_and, Bool.not_eq_true, Nonempty.forall]
      intro _ _ C
      cases C
      . simp only [FormL.nom_occurs]

lemma not_nominal_occurs_context {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S}(j : symbs.nominal s) (φ: FormL symbs sorts) :
  φ.occurs j = false ↔ ∀ {t : symbs.signature.S} {ψ : Form symbs t} (_ : ψ.Context φ), ψ.occurs j = false := by
  have : φ.occurs j = false ↔ ¬φ.occurs j := by simp only [Bool.not_eq_true]
  conv =>
    rw [this];
    rhs; simp only [←not_exists_not];
    rhs ; rhs ; intro ; rw [not_not];
    rhs ; intro ; rw [not_not];
    rhs ; intro ; simp only [Bool.not_eq_false]
  apply not_congr
  apply nominal_occurs_context

lemma nominal_occurs_union {symbs : Symbols α} {s : symbs.signature.S} {Γ Δ: PremiseSet symbs s} {i : symbs.nominal s} : (Γ ∪ Δ).occurs i ↔ Γ.occurs i ∨ Δ.occurs i := by
  apply Iff.intro
  -- aesop'd --
  . simp only [PremiseSet.occurs, Set.mem_union, forall_exists_index, and_imp]
    intro x a a_1
    obtain ⟨val, property⟩ := s
    cases a with
    | inl h =>
      apply Or.inl
      apply Exists.intro
      · apply And.intro
        · exact h
        · simp_all only
    | inr h_1 =>
      apply Or.inr
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {exact a_1
        }
        · simp_all only
  . simp only [PremiseSet.occurs, Set.mem_union]
    intro a
    obtain ⟨val, property⟩ := s
    cases a with
    | inl h =>
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {exact right
        }
        · simp_all only [true_or]
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      obtain ⟨left, right⟩ := h
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {exact right
        }
        · simp_all only [or_true]

lemma nominal_not_occurs_premise {symbs : Symbols α} {s t : symbs.signature.S} {Γ: PremiseSet symbs s} {i : symbs.nominal t} (h : ¬Γ.occurs i) : ∀ Θ : FiniteChoice Γ, Θ.conjunction.occurs i = false := by
  intro ⟨Θ, nodup⟩
  simp only [FiniteChoice.conjunction]
  induction Θ with
  | nil => simp only [List.conjunction, FormL.occurs_nom_top]
  | cons head tail ih =>
      simp only [PremiseSet.occurs, not_exists, not_and, Bool.not_eq_true] at h
      simp only [List.conjunction, FormL.occurs_nom_conj, Bool.or_eq_false_iff]
      rw [List.nodup_cons] at nodup
      apply And.intro (ih nodup.2)
      exact h head head.2

lemma nominal_not_occurs_conjunction {symbs : Symbols α} {s t : symbs.signature.S} {Γ: PremiseSet symbs s} {i : symbs.nominal t} {Θ : List Γ} : Θ.conjunction.occurs i = false ↔ ∀ ψ ∈ Θ, ψ.1.occurs i = false := by
  apply Iff.intro
  . intro h ψ ψ_in_T
    induction Θ with
    | nil => contradiction
    | cons head tail ih =>
        simp only [List.mem_cons] at ψ_in_T
        apply Or.elim ψ_in_T
        . intro eq
          subst eq
          aesop
        . intro
          apply ih
          simp only [List.conjunction, FormL.occurs_nom_conj, Bool.or_eq_false_iff] at h
          exact h.1
          assumption
  . intro h
    induction Θ with
    | nil => simp only [List.conjunction, FormL.occurs_nom_top]
    | cons head tail ih =>
        simp only [List.conjunction, FormL.occurs_nom_conj, Bool.or_eq_false_iff]
        apply And.intro
        . apply ih
          intros
          apply h
          simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp]
        . apply h head _
          simp only [List.mem_cons, true_or]
