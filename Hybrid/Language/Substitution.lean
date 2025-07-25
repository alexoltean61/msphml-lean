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

def nom_occurs {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (i : symbs.nominal s): FormL symbs sorts → Bool
  | @FormL.nom  _ _ s' j   =>
      if h : s = s' then
        i == (h ▸ j)
      else false
  | @FormL.at _ _ s' _ j φ =>
      nom_occurs i φ ||
        if h : s = s' then
          i == (h ▸ j)
        else false
  | (φ, ψ)   => nom_occurs i φ || nom_occurs i ψ
  | ℋ⟨_⟩ φ    => nom_occurs i φ
  | φ ⋁ ψ    => nom_occurs i φ || nom_occurs i ψ
  | ∼ φ      => nom_occurs i φ
  | ℋ∀ _ φ  => nom_occurs i φ
  | _        => false

def var_occurs {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (x : symbs.svar s): FormL symbs sorts → Bool
  | @FormL.svar  _ _ s' j   =>
      if h : s = s' then
        x == (h ▸ j)
      else false
  | @FormL.bind _ _ s' _ y φ =>
      var_occurs y φ ||
        if h : s = s' then
          x == (h ▸ y)
        else false
  | (φ, ψ)   => var_occurs x φ || var_occurs x ψ
  | ℋ⟨_⟩ φ    => var_occurs x φ
  | φ ⋁ ψ    => var_occurs x φ || var_occurs x ψ
  | ∼ φ      => var_occurs x φ
  | ℋ@ _ φ  => var_occurs x φ
  | _        => false


-- x occurs in φ, and x is free in φ
@[simp]
def occurs_free {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (x : symbs.svar s): FormL symbs sorts → Bool
  | @FormL.bind _ _ s' _ y φ =>
      if h : s = s' then
        if x = (h ▸ y) then
          false
        else occurs_free x φ
      else occurs_free x φ
  | (φ, ψ)   => occurs_free x φ || occurs_free x ψ
  | ℋ⟨_⟩ φ    => occurs_free x φ
  | φ ⋁ ψ    => occurs_free x φ || occurs_free x ψ
  | ∼ φ      => occurs_free x φ
  | ℋ@ _ φ  => occurs_free x φ
  | φ        => var_occurs x φ

abbrev Context.all_else_not_free {symbs : Symbols α} {s s' : symbs.signature.S} {sorts : List symbs.signature.S} {φ : Form symbs s} {ψ : FormL symbs sorts} (x : symbs.svar s') (C : φ.Context ψ) : Bool :=
  C.all_else_bool (λ φ => !φ.occurs_free x)


-- x occurs in φ, and x is bound in φ
def occurs_bound {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (x : symbs.svar s): FormL symbs sorts → Bool
  | @FormL.bind _ _ s' _ y φ =>
      if h : s = s' then
        if x = (h ▸ y) then
          true
        else occurs_bound x φ
      else occurs_bound x φ
  | (φ, ψ)   => occurs_bound x φ || occurs_bound x ψ
  | ℋ⟨_⟩ φ    => occurs_bound x φ
  | φ ⋁ ψ    => occurs_bound x φ || occurs_bound x ψ
  | ∼ φ      => occurs_bound x φ
  | ℋ@ _ φ   => occurs_bound x φ
  | _        => false

-- x is substitutable for y in φ
def free_for {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (x y : symbs.svar s): FormL symbs sorts → Bool
  | @FormL.bind _ _ s' _ z φ =>
    if !φ.occurs_free y then
      true
    else free_for x y φ &&
      if h : s = s' then
        x != (h ▸ z)
      else true
  | (φ, ψ)   => free_for x y φ && free_for x y ψ
  | ℋ⟨_⟩ φ    => free_for x y φ
  | φ ⋁ ψ   => free_for x y φ && free_for x y ψ
  | ∼ φ      => free_for x y φ
  | ℋ@ _ φ   => free_for x y φ
  | _        => true

def var_subst {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (x y : symbs.svar s): FormL symbs sorts → FormL symbs sorts
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
        else ℋ∀z (var_subst x y φ)
      else ℋ∀z (var_subst x y φ)
  | (φ, ψ)   => (var_subst x y φ, var_subst x y ψ)
  | ℋ⟨σ⟩ φ    => ℋ⟨σ⟩ (var_subst x y φ)
  | φ ⋁ ψ    => (var_subst x y φ) ⋁ (var_subst x y ψ)
  | ∼ φ      => ∼ (var_subst x y φ)
  | ℋ@k φ   => ℋ@k (var_subst x y φ)
  | φ => φ

def nom_subst {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} (i : symbs.nominal s) (y : symbs.svar s): FormL symbs sorts → FormL symbs sorts
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
        else ℋ∀z (nom_subst i y φ)
      else ℋ∀z (nom_subst i y φ)
  | (φ, ψ)   => (nom_subst i y φ, nom_subst i y ψ)
  | ℋ⟨σ⟩ φ    => ℋ⟨σ⟩ (nom_subst i y φ)
  | φ ⋁ ψ    => (nom_subst i y φ) ⋁ (nom_subst i y ψ)
  | ∼ φ      => ∼ (nom_subst i y φ)
  | ℋ@k φ   => ℋ@k (nom_subst i y φ)
  | φ => φ


instance {symbs : Symbols α} : Term symbs symbs.nominal where
  occurs := nom_occurs
  subst  := nom_subst

instance {symbs : Symbols α} : @Term α symbs symbs.svarType where
  occurs := var_occurs
  subst  := var_subst

notation:max φ:lead "[" x:arg "//" y:arg "]" => Term.subst x y φ

/--
  Checks if a term occurs in a formula
-/
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
  simp only [Term.subst, var_subst]

@[simp]
lemma subst_nom_appl : (ℋ⟨σ⟩ φ)[i // x] = ℋ⟨σ⟩ (φ[i // x]) := by
  simp only [Term.subst, nom_subst]

@[simp]
lemma subst_var_or : (φ ⋁ ψ)[y // x] = φ[y // x] ⋁ ψ[y // x] := by
  simp only [Term.subst, var_subst]

@[simp]
lemma subst_nom_or : (φ ⋁ ψ)[i // x] = φ[i // x] ⋁ ψ[i // x] := by
  simp only [Term.subst, nom_subst]

@[simp]
lemma subst_var_neg : (∼φ)[y // x] = ∼(φ[y // x]) := by
  simp only [Term.subst, var_subst]

@[simp]
lemma subst_nom_neg : (∼φ)[i // x] = ∼(φ[i // x]) := by
  simp only [Term.subst, nom_subst]

@[simp]
lemma subst_var_at {φ : Form symbs t} {k : symbs.nominal t} : (@FormL.at α symbs t u k φ)[y // x] = (ℋ@ k (φ[y // x])) := by
  simp only [Term.subst, var_subst]

@[simp]
lemma subst_nom_at {φ : Form symbs t} {k : symbs.nominal t} : (@FormL.at α symbs t u k φ)[j // x] = (ℋ@ k (φ[j // x])) := by
  simp only [Term.subst, nom_subst]

@[simp]
lemma subst_var_cons {φ : Form symbs t} : (φ, ψ)[y // x] = (φ[y // x], ψ[y // x]) := by
  simp only [Term.subst, var_subst]

@[simp]
lemma subst_nom_cons {φ : Form symbs t} : (φ, ψ)[i // x] = (φ[i // x], ψ[i // x]) := by
  simp only [Term.subst, nom_subst]

@[simp]
lemma subst_var_bind_neq_sorts {z : symbs.svar t} (h : ¬s = t) : (ℋ∀ z φ)[y // x] = ℋ∀ z (φ[y // x]) := by
  simp only [Term.subst, var_subst, h, ↓reduceDIte]

@[simp]
lemma subst_nom_bind_neq_sorts {z : symbs.svar t} (h : ¬s = t) : (ℋ∀ z φ)[i // x] = ℋ∀ z (φ[i // x]) := by
  simp only [Term.subst, nom_subst, h, ↓reduceDIte]

@[simp]
lemma subst_var_bind_neq_vars {z : symbs.svar s} (h : ¬x = z) : (ℋ∀ z φ)[y // x] = ℋ∀ z (φ[y // x]) := by
  simp only [Term.subst, var_subst, ↓reduceDIte, h, ↓reduceIte]

@[simp]
lemma subst_nom_bind_neq_vars {z : symbs.svar s} (h : ¬x = z) : (ℋ∀ z φ)[i // x] = ℋ∀ z (φ[i // x]) := by
  simp only [Term.subst, nom_subst, ↓reduceDIte, h, ↓reduceIte]

@[simp]
lemma subst_var_bind : (ℋ∀ x φ)[y // x] = ℋ∀ x φ := by
  simp only [Term.subst, var_subst, ↓reduceDIte, ↓reduceIte]

@[simp]
lemma subst_nom_bind : (ℋ∀ x φ)[i // x] = ℋ∀ x φ := by
  simp only [Term.subst, nom_subst, ↓reduceDIte, ↓reduceIte]

@[simp]
lemma subst_var_var : (ℋVar x)[y // x] = (ℋVar y) := by
  simp only [Term.subst, var_subst, ↓reduceDIte, ↓reduceIte]

@[simp]
lemma subst_nom_var : (ℋVar x)[i // x] = (ℋNom i) := by
  simp only [Term.subst, nom_subst, ↓reduceDIte, ↓reduceIte]

@[simp]
lemma subst_var_neq_var (h : ¬x = z) : (ℋVar z)[y // x] = (ℋVar z) := by
  simp only [Term.subst, var_subst, ↓reduceDIte, h, ↓reduceIte]

@[simp]
lemma subst_nom_neq_var (h : ¬x = y) : (ℋVar y)[i // x] = (ℋVar y) := by
  simp only [Term.subst, nom_subst, ↓reduceDIte, h, ↓reduceIte]

@[simp]
lemma subst_var_neq_var_sorts {z : symbs.svar t} (h : ¬s = t) : (ℋVar z)[y // x] = (ℋVar z) := by
  simp only [Term.subst, var_subst, h, ↓reduceDIte]

@[simp]
lemma subst_nom_neq_var_sorts {z : symbs.svar t} (h : ¬s = t) : (ℋVar z)[i // x] = (ℋVar z) := by
  simp only [Term.subst, nom_subst, h, ↓reduceDIte]

end CongrLemmas

lemma not_free_bound {symbs : Symbols α} {s t u : symbs.signature.S} {x : symbs.svarType s} {y : symbs.svarType t} {φ : Form symbs u} (h : φ.occurs_free x = false): (ℋ∀ y φ).occurs_free x = false := by
  simp only [occurs_free, h, ite_self, dite_eq_ite]

lemma not_free_bound' {symbs : Symbols α} {s t : symbs.signature.S} {x : symbs.svarType s} {φ : Form symbs t}: (ℋ∀ x φ).occurs_free x = false := by
  simp only [occurs_free, ↓reduceDIte, ↓reduceIte]

lemma not_free_var_subst {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} {x y : symbs.svarType s} {φ : FormL symbs sorts} (h : φ.occurs_free x = false): φ[y // x] = φ := by
  induction φ with
  | bind z φ ih =>
      rename_i t _
      by_cases eq_sorts : s = t
      . subst eq_sorts
        simp [Term.subst, var_subst] at ih ⊢
        simp [occurs_free] at h
        intro h2
        apply ih
        apply h
        exact h2
      . simp only [eq_sorts, not_false_eq_true, subst_var_bind_neq_sorts, bind.injEq, heq_eq_eq,
        true_and]
        simp only [occurs_free, eq_sorts, ↓reduceDIte] at h
        exact ih h
  | svar z =>
      simp [occurs_free, var_occurs] at h
      simp [Term.subst, var_subst]
      intro h2
      specialize h h2
      intro v
      subst v
      contradiction
  | appl σ ψ ih =>
      simp [Term.subst, var_subst]
      apply ih
      exact h
  | or φ ψ ih1 ih2 =>
      simp [Term.subst, var_subst]
      simp at h
      apply And.intro
      . apply ih1
        exact h.1
      . apply ih2
        exact h.2
  | neg φ ih =>
      simp [Term.subst, var_subst]
      apply ih
      exact h
  | cons φ ψs ih1 ih2 =>
      simp [Term.subst, var_subst]
      simp at h
      apply And.intro
      . apply ih1
        exact h.1
      . apply ih2
        exact h.2
  | «at» k _ ih =>
      simp [Term.subst, var_subst]
      apply ih
      exact h
  | _ => simp [Term.subst, var_subst] at h ⊢

lemma not_free_var_subst' {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} {x y : symbs.svarType s} {φ : FormL symbs sorts} (h : φ.occurs_free x = false): φ.var_subst y x = φ := by
  apply not_free_var_subst
  exact h

end FormL

def AxiomSet.occurs {symbs : Symbols α} {s : symbs.signature.S} {β : symbs.signature.S → Type v} [Term symbs β] (x : β s) (Λ: AxiomSet symbs) := ∃ s, ∃ φ : Λ s, φ.1.occurs x


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
