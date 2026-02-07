import Hybrid.Language.Variables.Instance

set_option maxHeartbeats 400000

namespace FormL

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}

lemma removeComm (l : VarList symbs) : (l.remove x).remove y = (l.remove y).remove x := by
  simp [VarList.remove]
  grind

lemma FVNodup {φ : FormL symbs ss} : φ.FV.Nodup := by
  induction φ <;> (
    unfold FV
    try simp_all
  )
  case bind =>
    apply List.Nodup.filter
    assumption
  case or =>
    apply List.nodup_dedup
  case cons =>
    apply List.nodup_dedup

lemma FVisFV {φ : FormL symbs ss} {s : symbs.signature.S} {x : symbs.svar s} :
  φ.FV.elem ⟨s, x⟩ ↔ φ.occurs_free x := by
  apply Iff.intro
  . intro h
    induction φ with
    | svar =>
        simp [FV, var_occurs] at h ⊢
        obtain ⟨eqS, heqX⟩ := h
        subst eqS
        simp only [↓reduceDIte, beq_iff_eq]
        cases heqX
        rfl
    | bind y φ ih =>
        simp [FV, VarList.remove] at h ⊢
        obtain ⟨hElem, hOr⟩ := h
        aesop
    | prop => simp [FV] at h
    | nom  => simp [FV] at h
    | appl σ φ ih =>
        simp [FV] at h ih ⊢
        exact ih h
    | or φ ψ ih1 ih2 =>
        simp [FV] at h ih1 ih2 ⊢
        apply Or.elim h <;> aesop
    | neg φ ih =>
        simp [FV] at h ih
        exact ih h
    | «at» k φ ih =>
        simp [FV] at h ih
        exact ih h
    | cons φ ψ ih1 ih2 =>
        simp [FV] at h ih1 ih2 ⊢
        apply Or.elim h <;> aesop
  . intro h
    induction φ with
    | svar =>
        simp [FV, var_occurs] at h ⊢
        split at h <;> aesop
    | bind y φ ih =>
        simp [FV, VarList.remove] at h ⊢
        split at h <;> aesop
    | prop => simp [var_occurs] at h
    | nom  => simp [var_occurs] at h
    | appl σ φ ih =>
        simp [FV] at h ih ⊢
        exact ih h
    | or φ ψ ih1 ih2 =>
        simp [FV] at h ih1 ih2 ⊢
        apply Or.elim h <;> aesop
    | neg φ ih =>
        simp at h ih ⊢
        aesop
    | «at» k φ ih =>
        simp at h ih ⊢
        aesop
    | cons φ ψ ih1 ih2 =>
        simp [FV] at h ih1 ih2 ⊢
        apply Or.elim h
        . intro hL
          apply Or.inl
          repeat apply_assumption
        . intro hR
          apply Or.inr
          repeat apply_assumption

lemma FVsubst {φ : FormL symbs ss} {s : symbs.signature.S} {x : symbs.svar s} {k : symbs.nominal s}
  (h : φ.FV.elem ⟨s, x⟩) : φ[k // x].FV = (φ.FV.remove ⟨s, x⟩) := by
  rw [FVisFV] at h
  induction φ with
    | svar =>
        simp [occurs_free, var_occurs] at h
        split_ifs at h with hEq
        . rename_i a
          subst hEq
          simp at h
          have : x = a := by exact SetCoe.ext h
          simp [FV, Term.subst, nom_subst, VarList.remove, this]
    | bind y φ ih =>
        simp [occurs_free] at h
        split_ifs at h with hEq
        . subst hEq
          simp at h
          obtain ⟨xEqY, nFree⟩ := h
          simp [Term.subst, nom_subst, xEqY] at ih ⊢
          specialize ih nFree
          simp [FV, ih, removeComm]
        . specialize ih h
          simp [Term.subst, nom_subst, hEq, FV] at ih ⊢
          rw [ih, removeComm]
    | prop =>
        simp [occurs_free, var_occurs] at h
    | nom  =>
        simp [occurs_free, var_occurs] at h
    | appl σ φ ih =>
        simp [Term.subst] at ih h
        repeat apply_assumption
    | or φ ψ ih1 ih2 =>
        simp [Term.subst, nom_subst, FV] at ih1 ih2 h ⊢
        apply Or.elim h
        . intro hL
          specialize ih1 hL
          rw [ih1]
          admit
        . intro hR
          specialize ih2 hR
          rw [ih2]
          admit
    | neg φ ih =>
        simp [Term.subst, nom_subst, FV] at ih h ⊢
        repeat apply_assumption
    | «at» k φ ih =>
        simp [Term.subst, nom_subst, FV] at ih h ⊢
        repeat apply_assumption
    | cons φ ψ ih1 ih2 =>
        simp [Term.subst, nom_subst, FV] at ih1 ih2 h ⊢
        apply Or.elim h
        . intro hL
          specialize ih1 hL
          rw [ih1]
          admit
        . intro hR
          specialize ih2 hR
          rw [ih2]
          admit

@[simp]
lemma Instance.distribAnd {i : Instantiation symbs} :
  i.apply (φ ⋀ ψ) = (i.apply φ ⋀ i.apply ψ) := sorry

@[simp]
lemma Instance.distribCons {i : Instantiation symbs} :
  i.apply (φ, φs) = (i.apply φ, i.apply φs) := sorry

@[simp]
lemma Instance.distribAt {i : Instantiation symbs} :
  i.apply ((ℋ@ k φ) : Form symbs t) = ℋ@ k (i.apply φ) := sorry


@[simp]
lemma Instance.distribAppl {i : Instantiation symbs} {σ : symbs.signature.«Σ» (s::ss) rng} {φs : FormL symbs (s::ss)} :
  i.apply (ℋ⟨σ⟩ φs) = ℋ⟨σ⟩ (i.apply φs) := sorry

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
