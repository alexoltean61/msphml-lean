import Hybrid.Language.Form

/--
  As opposed to matching logic, here contexts have no "holes".

  A context for `φ` represents one ocurrence of `φ` within an argument list.

  Note also that we do not yet apply any modal operator to said argument list.
-/
inductive FormL.Context {symbs : Symbols α} {s : symbs.signature.S} (φ : Form symbs s) : FormL symbs sorts → Type u
  | refl : Context φ φ
  | head : Context φ (.cons φ ψ)
  | tail : Context φ ψ → Context φ (.cons χ ψ)
/--
  Given a `Context φ ψ`, returns the `FormL` obtained by substituting `φ` in `ψ` by a plug.
-/
def FormL.Context.subst {φ : Form sig s}
          {ψ : FormL sig sorts}
          (ctx : Context φ ψ) :
    Form sig s → FormL sig sorts :=

  match ψ with
  | .prop _ =>
      match φ with
      | .prop _ =>
        match ctx with
          | .refl => id
  | .nom  n   =>
      match φ with
      | .nom _ =>
        match ctx with
          | .refl => id
  | .svar x   =>
      match φ with
      | .svar _ =>
        match ctx with
          | .refl => id
  | .appl _ _ =>
      match φ with
        | .appl _ _ =>
          match ctx with
          | .refl => id
  | .or _ _ =>
      match φ with
      | .or _ _ =>
        match ctx with
          | .refl => id
  | .neg _ =>
      match φ with
      | .neg _ =>
        match ctx with
          | .refl => id
  | .at _ _   =>
      match φ with
      | .at _ _ =>
        match ctx with
          | .refl => id
  | .bind _ _ =>
      match φ with
      | .bind _ _ =>
        match ctx with
          | .refl => id
  | .cons h t =>
      match ctx with
      | .head => λ plug => .cons plug t
      | .tail inner_ctx => λ plug => .cons h (subst inner_ctx plug)

notation:max C:49 "[" φ:50 "]" => FormL.Context.subst C φ


/--
  TODO: Working with contexts directly gets very technical.
  Consider refactoring contexts to something more intuitive, perhaps by use of an
  equivalent alternative definition and lemmas to translate between the two.
-/

/-
def FormL.Context.index {φ : Form symbs s} {ψ : FormL symbs sorts}: φ.Context ψ → Fin (sorts.length)
  | .refl => Fin.mk 0 (by simp only [List.length_singleton, Nat.lt_succ_self])
  | .head => Fin.mk 0 (by simp only [List.length_cons, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ])
  | @FormL.Context.tail _ _ _ _ _ sorts' ψ' _ _ ctx' => Fin.mk (1 + ctx'.index.val) (by
          have := ctx'.index.isLt
          simp only [List.length_cons, Nat.lt_succ] at this ⊢
          rw [Nat.add_comm]
          exact Nat.add_le_add_right this 1
      )

def FormL.Context.from_index {φ : Form symbs s} {ψ : FormL symbs sorts} : Fin (sorts.length) → Option (φ.Context ψ)
  | ⟨0, h⟩ => sorry
  | ⟨n+1, h⟩ => sorry
-/

def FormL.Context.index {φ : Form symbs s} {ψ : FormL symbs sorts}: φ.Context ψ → Nat
  | .refl => 0
  | .head => 0
  | .tail ctx' => 1 + ctx'.index

def FormL.Context.from_index {φ : Form symbs s} {ψ : FormL symbs sorts} : Nat → Option (φ.Context ψ)
  | 0   => sorry
  | n+1 => sorry

def FormL.Context.iso {φ : Form symbs s} {ψ : Form symbs s'} {χ τ : FormL symbs sorts} (C₁ : φ.Context χ) (C₂ : ψ.Context τ) : Prop :=
  match C₁ with
  | .refl =>
      match C₂ with
      | .refl => True
  | .head =>
      match C₂ with
      | .head => True
      | _ => False
  | .tail ctx =>
      match C₂ with
      | .tail ctx' => ctx.iso ctx'
      | _ => False

def FormL.subst_to_ctx (χ : Form sig s)
          {φ : Form sig s}
          {ψ : FormL sig sorts}
          (C : Context φ ψ) :
          χ.Context C[χ] := sorry

lemma FormL.Context.iso_trans {φ : Form symbs s} {ψ : Form symbs s'} {χ : Form symbs s''} {a b c : FormL symbs sorts} {C₁ : φ.Context a} {C₂ : ψ.Context b} {C₃ : χ.Context c} : C₁.iso C₂ → C₁.iso C₃ → C₂.iso C₃ := sorry

lemma FormL.Context.if_iso {φ ψ : Form symbs s} {τ : FormL symbs sorts} (C₁ : φ.Context τ) (C₂ : ψ.Context τ) (h : C₁.iso C₂) : φ = ψ := sorry

lemma FormL.Context.if_iso_sorts {φ : Form symbs s} {ψ : Form symbs s'} {τ : FormL symbs sorts} (C₁ : φ.Context τ) (C₂ : ψ.Context τ) (h : C₁.iso C₂) : s = s' := sorry

lemma FormL.Context.iso_subst {φ ψ χ : Form symbs s} {τ : FormL symbs sorts} {C₁ : φ.Context τ} {C₂ : ψ.Context C₁[χ]} (h : C₁.iso C₂) : ψ = χ := sorry

def FormL.Context.subst_iso {φ ψ : Form symbs s} {χ : FormL symbs sorts} {C₁ : φ.Context χ} (C₂ : ψ.Context C₁[ψ]) (h : C₁.iso C₂) : (τ : Form symbs s) → Σ' C₃ : τ.Context C₁[τ], C₂.iso C₃ := sorry

def FormL.Context.subst_not_iso {φ ψ χ : Form symbs s} {τ : FormL symbs sorts} {C₁ : φ.Context τ} (C₂ : ψ.Context C₁[χ]) (h : ¬C₁.iso C₂) : (δ : Form symbs s) → Σ' C₃ : ψ.Context C₁[δ], C₂.iso C₃ := sorry

def FormL.Context.subst_not_iso' {φ : Form symbs s} {ψ : Form symbs s'} {τ : FormL symbs sorts} {C₁ : φ.Context τ} (C₂ : ψ.Context τ) (h : ¬C₁.iso C₂) : (δ : Form symbs s) → Σ' C₃ : ψ.Context C₁[δ], C₂.iso C₃ := sorry
