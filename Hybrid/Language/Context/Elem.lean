import Hybrid.Language.Context.Def

namespace FormL

/--
  Given a formula (list) `χ`, a term of type `χ.Elem` can be constructed only from a formula
    `φ : Form symbs s` which *occurs* in `χ` (i.e., a term of type `φ.Context χ` can be given).
  Thus, `φ` is an element of `χ`.
  Note that different occurences of `φ` in `χ` correspond to different `χ.Elem` terms.
-/
def Elem {symbs : Symbols α} {sorts : List symbs.signature.S} (χ : FormL symbs sorts) :=
  (s : symbs.signature.S) × (φ : Form symbs s) × (φ.Context χ)

@[simp]
abbrev Elem.sort {symbs : Symbols α} {sorts : List symbs.signature.S} {χ : FormL symbs sorts} (e : χ.Elem) :=
  e.1

@[simp]
abbrev Elem.form {symbs : Symbols α} {sorts : List symbs.signature.S} {χ : FormL symbs sorts} (e : χ.Elem) :=
  e.2.1

@[simp]
abbrev Elem.ctx {symbs : Symbols α} {sorts : List symbs.signature.S} {χ : FormL symbs sorts} (e : χ.Elem) :=
  e.2.2

@[simp]
abbrev num_forms : FormL symbs sorts → ℕ := λ _ => sorts.length

/--
  Given a formula (list) `χ` and a natural number, will try to return the element in `χ` at the
    index corresponding to the number.
  Returns `none` if index is out of bounds.
-/
def index {symbs : Symbols α} {sorts : List symbs.signature.S} (χ : FormL symbs sorts) : ℕ → Option (χ.Elem)
  | 0 =>
      match χ with
      | @FormL.cons _ _ s _ _ ψ _ => some ⟨s, ψ, .head⟩
      | @FormL.prop _ _ s p       => some ⟨s, .prop p, .refl⟩
      | @FormL.nom _ _ s n        => some ⟨s, .nom n, .refl⟩
      | @FormL.svar _ _ s x       => some ⟨s, .svar x, .refl⟩
      | @FormL.appl _ _ _ _ rng σ φ => some ⟨rng, .appl σ φ, .refl⟩
      | @FormL.or _ _ s φ ψ       => some ⟨s, .or φ ψ, .refl⟩
      | @FormL.neg _ _ s φ        => some ⟨s, .neg φ, .refl⟩
      | @FormL.at _ _ _ s k φ     => some ⟨s, .at k φ, .refl⟩
      | @FormL.bind _ _ _ s x φ   => some ⟨s, .bind x φ, .refl⟩
  | n+1 =>
      match χ with
      | @FormL.cons _ _ _ s' ss _ ψ =>
          @index α symbs (s' :: ss) ψ n >>= λ ⟨s, φ, C⟩ => return ⟨s, φ, .tail C⟩
      | _ => none

/--
  Turns an occurence of `φ` within `χ` (i.e., a term of type `φ.Context χ`) into the index where `φ` occurs.
-/
def Context.toNat {φ : Form sig s} {χ : FormL sig sorts} : Context φ χ → ℕ
  | .refl => 0
  | .head => 0
  | .tail C' => C'.toNat + 1

/--
  Any formula `χ` has a finite number of elements, so we can encode them to natural numbers.
-/
instance Elem.elem_encodable (χ : FormL symbs sorts) : Encodable χ.Elem where
  encode  := λ ⟨_, _, C⟩ => C.toNat
  decode  := χ.index
  encodek := by
    intro ⟨s, φ, C⟩
    induction C with
    | refl =>
        simp [Context.toNat]
        cases φ
        repeat simp [FormL.index]
    | head =>
        simp [Context.toNat, FormL.index]
    | tail C' ih =>
        rename_i ψ _ _
        simp [Context.toNat]
        simp [FormL.index, ih]

lemma Elem.encode_wf {χ : FormL symbs sorts} : ∀ {e : χ.Elem}, Encodable.encode e < χ.num_forms := by
  intro ⟨_, _, ctx⟩
  induction χ with
  | cons _ ψ _ ih =>
      cases ctx with
      | head => simp [Encodable.encode, num_forms, Context.toNat]
      | tail ctx' =>
          simp [Encodable.encode, num_forms, Context.toNat] at ih ⊢
          apply ih
  | _ =>
      cases ctx
      . simp [Encodable.encode, num_forms, Context.toNat]

def get_elem (χ : FormL symbs sorts) : Fin χ.num_forms → χ.Elem
  | ⟨0, _⟩ =>
      match χ with
      | @FormL.cons _ _ s _ _ ψ _ => ⟨s, ψ, .head⟩
      | @FormL.prop _ _ s p       => ⟨s, .prop p, .refl⟩
      | @FormL.nom _ _ s n        => ⟨s, .nom n, .refl⟩
      | @FormL.svar _ _ s x       => ⟨s, .svar x, .refl⟩
      | @FormL.appl _ _ _ _ rng σ φ => ⟨rng, .appl σ φ, .refl⟩
      | @FormL.or _ _ s φ ψ       => ⟨s, .or φ ψ, .refl⟩
      | @FormL.neg _ _ s φ        => ⟨s, .neg φ, .refl⟩
      | @FormL.at _ _ _ s k φ     => ⟨s, .at k φ, .refl⟩
      | @FormL.bind _ _ _ s x φ   => ⟨s, .bind x φ, .refl⟩
  | ⟨n+1, lt⟩ =>
        match χ with
      | .cons _ ψ =>
          let e := ψ.get_elem ⟨n, Nat.add_lt_add_iff_right.mp lt⟩
          ⟨e.sort, e.form, .tail e.ctx⟩
      | .prop _       => Nat.noConfusion $ Nat.lt_one_iff.mp lt
      | .nom _        => Nat.noConfusion $ Nat.lt_one_iff.mp lt
      | .svar _       => Nat.noConfusion $ Nat.lt_one_iff.mp lt
      | .appl _ _     => Nat.noConfusion $ Nat.lt_one_iff.mp lt
      | .or _ _       => Nat.noConfusion $ Nat.lt_one_iff.mp lt
      | .neg _        => Nat.noConfusion $ Nat.lt_one_iff.mp lt
      | .at _ _       => Nat.noConfusion $ Nat.lt_one_iff.mp lt
      | .bind _ _     => Nat.noConfusion $ Nat.lt_one_iff.mp lt

lemma get_elem_surj {χ : FormL symbs sorts} : χ.get_elem.Surjective := by
  intro ⟨st, form, ctx⟩
  let e : χ.Elem := ⟨st, form, ctx⟩
  exists ⟨Encodable.encode e, Elem.encode_wf⟩
  unfold e
  clear e
  induction χ with
  | cons φ ψ _ ih =>
      simp only [Encodable.encode]
      cases ctx with
      | head => simp only [Context.toNat, get_elem]
      | tail ctx' =>
          specialize ih ctx'
          simp only [Encodable.encode] at ih
          simp only [Context.toNat, get_elem, Elem.sort, Elem.form, Elem.ctx]
          rw [ih]
  | _ =>
      simp only [Encodable.encode]
      cases ctx
      . simp! only [Fin.isValue, FormL.get_elem.eq_def]

theorem Elem.enumerate {χ : FormL symbs sorts} {p : χ.Elem → Prop} : (∀ i : Fin χ.num_forms, p (χ.get_elem i)) ↔ (∀ e : χ.Elem, p e) := by
  apply Iff.intro
  . intro h e
    have ⟨i, h_i⟩ := get_elem_surj e
    rw [←h_i]
    exact h i
  . intro h i
    exact h (χ.get_elem i)

theorem Elem.enumerate' {χ : FormL symbs sorts} {p : {s : symbs.signature.S} → (φ : Form symbs s) → (φ.Context χ) → Prop} : (∀ i : Fin χ.num_forms, p (χ.get_elem i).form (χ.get_elem i).ctx) ↔ (∀ e : χ.Elem, p e.form e.ctx) := by
  apply Iff.intro
  . intro h e
    have ⟨i, h_i⟩ := get_elem_surj e
    rw [←h_i]
    exact h i
  . intro h i
    exact h (χ.get_elem i)

lemma Elem.sort_as_idx {ψ : FormL symbs sorts} {i : Fin ψ.num_forms} : (ψ.get_elem i).sort = sorts[i] := by
  revert i
  induction ψ with
  | cons φ χ _ ih =>
      simp only [List.length_cons, sort, Fin.getElem_fin]
      rw [Fin.forall_fin_succ]
      apply And.intro
      . rename_i s₁ s₂ t a_ih
        simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd, sort, Fin.getElem_fin, Fin.val_eq_zero,
          List.getElem_cons_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
        obtain ⟨val, property⟩ := s₁
        obtain ⟨val_1, property_1⟩ := s₂
        rfl
      . intro i
        rename_i s₁ s₂ t a_ih
        simp_all only [List.length_cons, List.length_nil, Nat.reduceAdd, sort, Fin.getElem_fin, Fin.val_eq_zero,
          List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
        obtain ⟨val, property⟩ := s₁
        obtain ⟨val_1, property_1⟩ := s₂
        apply @ih
  | _ =>
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, sort, Fin.getElem_fin,
        Fin.val_eq_zero, List.getElem_cons_zero]
      intro i
      cases i with
      | mk val lt =>
          simp only [Nat.lt_one_iff] at lt
          subst lt
          simp only [get_elem]
