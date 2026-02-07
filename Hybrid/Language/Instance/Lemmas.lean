import Hybrid.Language.Instance.Def

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
