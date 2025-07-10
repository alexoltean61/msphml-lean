import Hybrid.Language.Form
import Hybrid.Language.Context

variable {α : Type u}
variable [DecidableEq α]

class Term (symbs : Symbols α) (β: symbs.signature.S → Type v) where
  -- Checks if a term occurs in a formula
  occurs : β s → FormL symbs sorts → Bool
  -- Substitutes a term for a variable in a formula
  subst  : β s → symbs.svar s → FormL symbs sorts → FormL symbs sorts

namespace FormL

def nomOccurs {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (i : symbs.nominal s): FormL symbs sorts → Bool
  | @FormL.nom  _ _ s' j   =>
      if h : s = s' then
        i == (h ▸ j)
      else false
  | @FormL.at _ _ s' _ j φ =>
      nomOccurs i φ ||
        if h : s = s' then
          i == (h ▸ j)
        else false
  | (φ, ψ)   => nomOccurs i φ || nomOccurs i ψ
  | ℋ⟨_⟩ φ    => nomOccurs i φ
  | φ ⋁ ψ    => nomOccurs i φ || nomOccurs i ψ
  | ∼ φ      => nomOccurs i φ
  | ℋ∀ _ φ  => nomOccurs i φ
  | _        => false

def varOccurs {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (x : symbs.svar s): FormL symbs sorts → Bool
  | @FormL.svar  _ _ s' j   =>
      if h : s = s' then
        x == (h ▸ j)
      else false
  | @FormL.bind _ _ s' _ y φ =>
      varOccurs y φ ||
        if h : s = s' then
          x == (h ▸ y)
        else false
  | (φ, ψ)   => varOccurs x φ || varOccurs x ψ
  | ℋ⟨_⟩ φ    => varOccurs x φ
  | φ ⋁ ψ    => varOccurs x φ || varOccurs x ψ
  | ∼ φ      => varOccurs x φ
  | ℋ@ _ φ  => varOccurs x φ
  | _        => false


-- x occurs in φ, and x is free in φ
@[simp]
def varOccursFree {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (x : symbs.svar s): FormL symbs sorts → Bool
  | @FormL.bind _ _ s' _ y φ =>
      if h : s = s' then
        if x = (h ▸ y) then
          false
        else varOccursFree x φ
      else varOccursFree x φ
  | (φ, ψ)   => varOccursFree x φ || varOccursFree x ψ
  | ℋ⟨_⟩ φ    => varOccursFree x φ
  | φ ⋁ ψ    => varOccursFree x φ || varOccursFree x ψ
  | ∼ φ      => varOccursFree x φ
  | ℋ@ _ φ  => varOccursFree x φ
  | φ        => varOccurs x φ

abbrev Context.all_else_not_free {symbs : Symbols α} {s s' : symbs.signature.S} {sorts : List symbs.signature.S} {φ : Form symbs s} {ψ : FormL symbs sorts} (x : symbs.svar s') (C : φ.Context ψ) : Bool :=
  C.all_else_bool (λ φ => !φ.varOccursFree x)


-- x occurs in φ, and x is bound in φ
def varOccursBound {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (x : symbs.svar s): FormL symbs sorts → Bool
  | @FormL.bind _ _ s' _ y φ =>
      if h : s = s' then
        if x = (h ▸ y) then
          true
        else varOccursBound x φ
      else varOccursBound x φ
  | (φ, ψ)   => varOccursBound x φ || varOccursBound x ψ
  | ℋ⟨_⟩ φ    => varOccursBound x φ
  | φ ⋁ ψ    => varOccursBound x φ || varOccursBound x ψ
  | ∼ φ      => varOccursBound x φ
  | ℋ@ _ φ   => varOccursBound x φ
  | _        => false

-- x is substitutable for y in φ
def varSubstableFor {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (x y : symbs.svar s): FormL symbs sorts → Bool
  | @FormL.bind _ _ s' _ z φ =>
    if !φ.varOccursFree y then
      true
    else varSubstableFor x y φ &&
      if h : s = s' then
        x != (h ▸ z)
      else true
  | (φ, ψ)   => varSubstableFor x y φ && varSubstableFor x y ψ
  | ℋ⟨_⟩ φ    => varSubstableFor x y φ
  | φ ⋁ ψ   => varSubstableFor x y φ && varSubstableFor x y ψ
  | ∼ φ      => varSubstableFor x y φ
  | ℋ@ _ φ   => varSubstableFor x y φ
  | _        => true

def varSubst {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (x y : symbs.svar s): FormL symbs sorts → FormL symbs sorts
  | @FormL.svar _ _ s' z   =>
      if h : s = s' then
        if (y = h ▸ z) then
          h ▸ .svar x
        else .svar z
      else .svar z
  | @FormL.bind _ _ s' _ z φ =>
      if h : s = s' then
        if (y = h ▸ z) then
          ℋ∀z φ
        -- This function is NOT capture aware!
        --  If z = x and y is free in φ, this function will capture
        --  y in (∀ z. φ)[x / y]
        -- Safety is guaranteed only if a proof of (y is free for x in φ) is also given in the context.
        else ℋ∀z (varSubst x y φ)
      else ℋ∀z (varSubst x y φ)
  | (φ, ψ)   => (varSubst x y φ, varSubst x y ψ)
  | ℋ⟨σ⟩ φ    => ℋ⟨σ⟩ (varSubst x y φ)
  | φ ⋁ ψ    => (varSubst x y φ) ⋁ (varSubst x y ψ)
  | ∼ φ      => ∼ (varSubst x y φ)
  | ℋ@k φ   => ℋ@k (varSubst x y φ)
  | φ => φ

def nomSubst {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (i : symbs.nominal s) (y : symbs.svar s): FormL symbs sorts → FormL symbs sorts
  | @FormL.svar _ _ s' z   =>
      if h : s = s' then
        if (y = h ▸ z) then
          h ▸ .nom i
        else .svar z
      else .svar z
  | @FormL.bind _ _ s' _ z φ =>
      if h : s = s' then
        if (y = h ▸ z) then
          ℋ∀z φ
        else ℋ∀z (nomSubst i y φ)
      else ℋ∀z (nomSubst i y φ)
  | (φ, ψ)   => (nomSubst i y φ, nomSubst i y ψ)
  | ℋ⟨σ⟩ φ    => ℋ⟨σ⟩ (nomSubst i y φ)
  | φ ⋁ ψ    => (nomSubst i y φ) ⋁ (nomSubst i y ψ)
  | ∼ φ      => ∼ (nomSubst i y φ)
  | ℋ@k φ   => ℋ@k (nomSubst i y φ)
  | φ => φ


instance {symbs : Symbols α} : Term symbs symbs.nominal where
  occurs := FormL.nomOccurs
  subst  := FormL.nomSubst

instance {symbs : Symbols α} : @Term α symbs symbs.svarType where
  occurs := FormL.varOccurs
  subst  := FormL.varSubst

notation:max φ:lead "[" x:arg "//" y:arg "]" => Term.subst x y φ

-- Checks if a term occurs in a formula
abbrev occurs {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} {β : symbs.signature.S → Type v} [Term symbs β] (x : β s) (φ: FormL symbs sorts) := Term.occurs x φ

section CongrLemmas

variable {symbs : Symbols α}
variable {s t u : symbs.signature.S}
variable {sorts : List symbs.signature.S}
variable {x y : symbs.svarType s}
variable {i j : symbs.nominal s}
variable {σ : symbs.signature.Sig (t :: sorts) u}

@[simp]
lemma subst_var_appl : (ℋ⟨σ⟩ φ)[y // x] = ℋ⟨σ⟩ (φ[y // x]) := by
  simp only [Term.subst, varSubst]

@[simp]
lemma subst_nom_appl : (ℋ⟨σ⟩ φ)[i // x] = ℋ⟨σ⟩ (φ[i // x]) := by
  simp only [Term.subst, nomSubst]

@[simp]
lemma subst_var_or : (φ ⋁ ψ)[y // x] = φ[y // x] ⋁ ψ[y // x] := by
  simp only [Term.subst, varSubst]

@[simp]
lemma subst_nom_or : (φ ⋁ ψ)[i // x] = φ[i // x] ⋁ ψ[i // x] := by
  simp only [Term.subst, nomSubst]

@[simp]
lemma subst_var_neg : (∼φ)[y // x] = ∼(φ[y // x]) := by
  simp only [Term.subst, varSubst]

@[simp]
lemma subst_nom_neg : (∼φ)[i // x] = ∼(φ[i // x]) := by
  simp only [Term.subst, nomSubst]

@[simp]
lemma subst_var_at {φ : Form symbs t} {k : symbs.nominal t} : (@FormL.at α symbs t u k φ)[y // x] = (ℋ@ k (φ[y // x])) := by
  simp only [Term.subst, varSubst]

@[simp]
lemma subst_nom_at {φ : Form symbs t} {k : symbs.nominal t} : (@FormL.at α symbs t u k φ)[j // x] = (ℋ@ k (φ[j // x])) := by
  simp only [Term.subst, nomSubst]

@[simp]
lemma subst_var_cons {φ : Form symbs t} : (φ, ψ)[y // x] = (φ[y // x], ψ[y // x]) := by
  simp only [Term.subst, varSubst]

@[simp]
lemma subst_nom_cons {φ : Form symbs t} : (φ, ψ)[i // x] = (φ[i // x], ψ[i // x]) := by
  simp only [Term.subst, nomSubst]

@[simp]
lemma subst_var_bind_neq_sorts {z : symbs.svar t} (h : ¬s = t) : (ℋ∀ z φ)[y // x] = ℋ∀ z (φ[y // x]) := by
  simp only [Term.subst, varSubst, h, ↓reduceDIte]

@[simp]
lemma subst_var_bind_neq_vars {z : symbs.svar s} (h : ¬x = z) : (ℋ∀ z φ)[y // x] = ℋ∀ z (φ[y // x]) := by
  simp only [Term.subst, varSubst, ↓reduceDIte, h, ↓reduceIte]

@[simp]
lemma subst_var_bind : (ℋ∀ x φ)[y // x] = ℋ∀ x φ := by
  simp only [Term.subst, varSubst, ↓reduceDIte, ↓reduceIte]

end CongrLemmas

lemma notFreeBound {symbs : Symbols α} {s t u : symbs.signature.S} {x : symbs.svarType s} {y : symbs.svarType t} {φ : Form symbs u} (h : φ.varOccursFree x = false): (ℋ∀ y φ).varOccursFree x = false := by
  simp only [varOccursFree, h, ite_self, dite_eq_ite]

lemma notFreeBound' {symbs : Symbols α} {s t : symbs.signature.S} {x : symbs.svarType s} {φ : Form symbs t}: (ℋ∀ x φ).varOccursFree x = false := by
  simp only [varOccursFree, ↓reduceDIte, ↓reduceIte]

lemma notFreeVarSubst {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} {x y : symbs.svarType s} {φ : FormL symbs sorts} (h : φ.varOccursFree x = false): φ[y // x] = φ := by
  induction φ with
  | bind z φ ih =>
      rename_i t _
      by_cases eq_sorts : s = t
      . subst eq_sorts
        simp [Term.subst, varSubst] at ih ⊢
        simp [varOccursFree] at h
        intro h2
        apply ih
        apply h
        exact h2
      . simp only [eq_sorts, not_false_eq_true, subst_var_bind_neq_sorts, bind.injEq, heq_eq_eq,
        true_and]
        simp only [varOccursFree, eq_sorts, ↓reduceDIte] at h
        exact ih h
  | svar z =>
      simp [varOccursFree, varOccurs] at h
      simp [Term.subst, varSubst]
      intro h2
      specialize h h2
      intro v
      subst v
      contradiction
  | appl σ ψ ih =>
      simp [Term.subst, varSubst]
      apply ih
      exact h
  | or φ ψ ih1 ih2 =>
      simp [Term.subst, varSubst]
      simp at h
      apply And.intro
      . apply ih1
        exact h.1
      . apply ih2
        exact h.2
  | neg φ ih =>
      simp [Term.subst, varSubst]
      apply ih
      exact h
  | cons φ ψs ih1 ih2 =>
      simp [Term.subst, varSubst]
      simp at h
      apply And.intro
      . apply ih1
        exact h.1
      . apply ih2
        exact h.2
  | «at» k _ ih =>
      simp [Term.subst, varSubst]
      apply ih
      exact h
  | _ => simp [Term.subst, varSubst] at h ⊢

lemma notFreeVarSubst' {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} {x y : symbs.svarType s} {φ : FormL symbs sorts} (h : φ.varOccursFree x = false): φ.varSubst y x = φ := by
  apply notFreeVarSubst
  exact h

end FormL
