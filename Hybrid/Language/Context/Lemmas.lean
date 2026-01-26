import Hybrid.Language.Context.Def

namespace FormL

namespace Context

@[refl]
lemma iso_refl {φ : Form symbs s} {a : FormL symbs sorts} {C : φ.Context a} : C.iso C := by
  induction C
  . simp only [iso]
  . simp only [iso]
  . simp only [iso]
    apply_assumption

@[trans]
lemma iso_trans {φ : Form symbs s} {ψ : Form symbs s'} {χ : Form symbs s''} {a b c : FormL symbs sorts} {C₁ : φ.Context a} {C₂ : ψ.Context b} {C₃ : χ.Context c} : C₁.iso C₂ → C₂.iso C₃ → C₁.iso C₃ := by
  intro h1 h2
  induction C₁
  . cases C₂
    . cases C₃
      . simp only [iso]
  . cases C₂
    . cases C₃
      . simp only [iso]
      . simp only [iso] at h2
    . cases C₃
      . simp only [iso]
      . simp only [iso] at h1
  . cases C₂
    . cases C₃
      . simp only [iso] at h1
      . simp only [iso] at h2
    . cases C₃
      . simp only [iso] at h2
      . simp only [iso] at h2 h1 ⊢
        apply_assumption
        repeat assumption

@[symm]
lemma iso_symm {φ : Form symbs s} {ψ : Form symbs s'} {a b : FormL symbs sorts} {C₁ : φ.Context a} {C₂ : ψ.Context b} : C₁.iso C₂ → C₂.iso C₁ := by
  intro h
  induction C₁
  . cases C₂
    . simp only [iso]
  . cases C₂
    . simp only [iso]
    . simp only [iso] at h
  . cases C₂
    . simp only [iso] at h
    . simp only [iso] at h ⊢
      apply_assumption
      exact h

lemma iso_trans' {φ : Form symbs s} {ψ : Form symbs s'} {χ : Form symbs s''} {a b c : FormL symbs sorts} {C₁ : φ.Context a} {C₂ : ψ.Context b} {C₃ : χ.Context c} : C₁.iso C₂ → C₁.iso C₃ → C₂.iso C₃ := by
  intro h1 h2
  apply iso_symm
  apply iso_trans (iso_symm h2)
  exact h1

lemma if_iso {φ ψ : Form symbs s} {τ : FormL symbs sorts} (C₁ : φ.Context τ) (C₂ : ψ.Context τ) (h : C₁.iso C₂) : φ = ψ := by
  induction τ with
  | cons _ _ _ ih =>
      cases C₁
      . cases C₂
        . rfl
        . simp [iso] at h
      . cases C₂
        . simp [iso] at h
        . rename_i ctx ctx'
          apply ih ctx ctx'
          exact h
  | _ =>
      cases C₁ with
      | _ => cases C₂ with
             | _ => rfl

lemma subst_as_id {φ : Form symbs s} {τ : FormL symbs sorts} {C : φ.Context τ} : C[φ] = τ := by
  induction τ with
  | cons _ _ _ ih =>
      cases C
      . rfl
      . simp [subst, ih]
  | _ =>
      cases C
      . rfl

lemma subst_in_iso_helper {φ χ : Form symbs s} {τ : FormL symbs sorts} {C₁ : φ.Context τ} {C₂ : χ.Context C₁[χ]} (h : C₂.iso C₁) : C₂[φ] = C₁[φ] := by
  induction τ with
  | cons _ _ _ ih =>
      cases C₁
      . cases C₂
        . rfl
        . simp [iso] at h
      . cases C₂
        . simp [iso] at h
        . simp [iso] at h
          simp [subst]
          exact ih h
  | _ =>
      cases C₁ with
      | _ => cases C₂ with
             | _ => rfl

lemma subst_in_iso {φ χ : Form symbs s} {τ : FormL symbs sorts} {C₁ : φ.Context τ} {C₂ : χ.Context C₁[χ]} (h : C₂.iso C₁) : C₂[φ] = τ := by
  rw [subst_in_iso_helper h, subst_as_id]

lemma if_iso_sorts {φ : Form symbs s} {ψ : Form symbs s'} {τ : FormL symbs sorts} (C₁ : φ.Context τ) (C₂ : ψ.Context τ) (h : C₁.iso C₂) : s = s' := by
  induction τ with
  | cons _ _ _ ih =>
      cases C₁
      . cases C₂
        . rfl
        . simp [iso] at h
      . cases C₂
        . simp [iso] at h
        . rename_i ctx ctx'
          apply ih ctx ctx'
          exact h
  | _ =>
      cases C₁ with
      | _ => cases C₂ with
             | _ => rfl

lemma iso_subst {φ ψ χ : Form symbs s} {τ : FormL symbs sorts} {C₁ : φ.Context τ} {C₂ : ψ.Context C₁[χ]} (h : C₁.iso C₂) : ψ = χ := by
  induction C₁
  . cases C₂
    . simp only [subst, id]
  . cases C₂
    . rfl
    . simp only [iso] at h
  . cases C₂
    . simp only [iso] at h
    . simp only [iso] at h
      apply_assumption
      exact h

lemma iso_subst_sorts {φ χ : Form symbs s} {ψ : Form symbs s'} {τ : FormL symbs sorts} {C₁ : φ.Context τ} {C₂ : ψ.Context C₁[χ]} (h : C₁.iso C₂) : s = s' := by
  induction C₁
  . cases C₂
    . simp only
  . cases C₂
    . rfl
    . simp only [iso] at h
  . cases C₂
    . simp only [iso] at h
    . simp only [iso] at h
      apply_assumption
      exact h

def subst_iso {φ ψ : Form symbs s} {χ : FormL symbs sorts} {C₁ : φ.Context χ} (C₂ : ψ.Context C₁[ψ]) (h : C₁.iso C₂) : (τ : Form symbs s) → Σ' C₃ : τ.Context C₁[τ], C₂.iso C₃ := λ τ => by
  cases C₁
  . cases C₂
    . apply PSigma.mk
      case fst =>
        simp only [subst, id_eq]
        exact refl
      case snd =>
        simp only [iso, id_eq]
  . cases C₂
    . apply PSigma.mk
      case fst =>
        simp only [subst]
        exact head
      case snd =>
        simp only [iso, id_eq]
    . simp only [iso] at h
  . cases C₂
    . simp only [iso] at h
    case tail C' =>
      simp only [iso] at h
      have ⟨C'', iso⟩ := subst_iso C' h τ
      apply PSigma.mk
      case fst =>
        simp only [subst]
        exact tail C''
      case snd =>
        exact iso

def subst_not_iso {φ : Form symbs s} {ψ : Form symbs s'} {τ : FormL symbs sorts} {C₁ : φ.Context τ} (C₂ : ψ.Context τ) (h : ¬C₁.iso C₂) : (δ : Form symbs s) → Σ' C₃ : ψ.Context C₁[δ], C₂.iso C₃ := λ δ => by
  cases C₁
  . cases C₂
    . simp only [iso, not_true_eq_false] at h
  . cases C₂
    . simp only [iso, not_true_eq_false] at h
    case tail C' =>
      apply PSigma.mk
      case fst =>
        simp only [subst]
        exact tail C'
      case snd =>
        simp only [iso, id_eq, iso_refl]
  case tail C' =>
    cases C₂
    . simp only [subst]
      apply PSigma.mk
      case fst =>
        exact head
      case snd =>
        simp only [iso]
    case tail C'' =>
      simp only [iso] at h
      have ⟨C''', iso⟩ := subst_not_iso C'' h δ
      apply PSigma.mk
      case fst =>
        simp only [subst]
        exact tail C'''
      case snd =>
        exact iso

def subst_not_iso' {φ χ : Form symbs s} {ψ : Form symbs s'} {τ : FormL symbs sorts} {C₁ : φ.Context τ} (C₂ : ψ.Context C₁[χ]) (h : ¬C₁.iso C₂) : (δ : Form symbs s) → Σ' C₃ : ψ.Context C₁[δ], C₂.iso C₃ := λ δ => by
  cases C₁
  . cases C₂
    . simp only [iso, not_true_eq_false] at h
  . cases C₂
    . simp only [iso, not_true_eq_false] at h
    case tail C' =>
      apply PSigma.mk
      case fst =>
        simp only [subst]
        exact tail C'
      case snd =>
        simp only [iso, id_eq, iso_refl]
  case tail C' =>
    cases C₂
    . simp only [subst]
      apply PSigma.mk
      case fst =>
        exact head
      case snd =>
        simp only [iso]
    case tail C'' =>
      simp only [iso] at h
      have ⟨C''', iso⟩ := subst_not_iso' C'' h δ
      apply PSigma.mk
      case fst =>
        simp only [subst]
        exact tail C'''
      case snd =>
        exact iso

def subst_not_iso'' {φ χ : Form symbs s} {ψ : Form symbs s'} {τ : FormL symbs sorts} {C₁ : φ.Context τ} {C₂ : ψ.Context C₁[χ]} (h : ¬C₁.iso C₂) : Σ' C₃ : ψ.Context τ, C₂.iso C₃ := by
  cases C₁
  . cases C₂
    . simp only [iso, not_true_eq_false] at h
  . cases C₂
    . simp only [iso, not_true_eq_false] at h
    case tail C' =>
      apply PSigma.mk
      case fst =>
        exact tail C'
      case snd =>
        simp only [iso, iso_refl]
  case tail C' =>
    cases C₂
    . simp only [subst]
      apply PSigma.mk
      case fst =>
        exact head
      case snd =>
        simp only [iso]
    case tail C'' =>
      simp only [iso] at h
      have ⟨C''', iso⟩ := subst_not_iso'' h
      apply PSigma.mk
      case fst =>
        exact tail C'''
      case snd =>
        exact iso

end Context

lemma subst_to_ctx_iso {χ : Form sig s}
          {φ : Form sig s}
          {ψ : FormL sig sorts}
          (C : Context φ ψ) :
          (χ.subst_to_ctx C).iso C := by
  induction ψ with
  | cons χ χs =>
      cases C
      . unfold subst_to_ctx
        simp only [id_eq, Context.iso]
      . unfold subst_to_ctx
        simp only [id_eq, Context.iso]
        apply_assumption
  | _ =>
      cases C
      . unfold subst_to_ctx
        simp only [id_eq, Context.iso]

end FormL
