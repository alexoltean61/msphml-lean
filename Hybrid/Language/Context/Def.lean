import Hybrid.Language.Form

namespace FormL

/--
  As opposed to matching logic, here contexts have no "holes".

  A context for `φ` represents one ocurrence of `φ` within an argument list.

  Note also that we do not yet apply any modal operator to said argument list.
-/
inductive Context {symbs : Symbols α} {s : symbs.signature.S} (φ : Form symbs s) : FormL symbs sorts → Type u
  | refl : Context φ φ
  | head : Context φ (.cons φ ψ)
  | tail : Context φ ψ → Context φ (.cons χ ψ)

namespace Context

/--
  Given a `Context φ ψ`, returns the `FormL` obtained by substituting `φ` in `ψ` by a plug.
-/
def subst {φ : Form sig s}
          {ψ : FormL sig sorts} :
    Context φ ψ → Form sig s → FormL sig sorts
  | .refl => id
  | @Context.head _ _ _ _ _ _ t =>
        λ plug => plug.cons t
  | @Context.tail _ _ _ _ _ _ _  _ h inner_ctx =>
        λ plug => h.cons (inner_ctx.subst plug)

notation:max C:49 "[" φ:50 "]" => subst C φ

def iso {φ : Form symbs s} {ψ : Form symbs s'} {χ : FormL symbs sorts} {τ : FormL symbs sorts'} (C₁ : φ.Context χ) (C₂ : ψ.Context τ) : Prop :=
  match C₁ with
  | .refl =>
      match C₂ with
      | .refl => True
      | _ => False
  | .head =>
      match C₂ with
      | .head => True
      | _ => False
  | .tail ctx =>
      match C₂ with
      | .tail ctx' => ctx.iso ctx'
      | _ => False

/--
  Will be true if P is true for all other formulas in a FormL, with the exception of the one highlighted by the context.
-/
@[simp]
def all_else_bool {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} {φ : Form symbs s} {ψ : FormL symbs sorts} (P : {sorts : List symbs.signature.S} → FormL symbs sorts → Bool) : φ.Context ψ → Bool
  | .refl => true
  | @FormL.Context.head _ _ _ _ _ _ rest => P rest
  | @FormL.Context.tail _ _ _ _ _ _ rest₁ _ rest₂ _ => P rest₁ && P rest₂

/--
  Will be true if P is true for all other formulas in a FormL, with the exception of the one highlighted by the context.
-/
@[simp]
def all_else_prop {symbs : Symbols α} {s : symbs.signature.S} {sorts : List symbs.signature.S} {φ : Form symbs s} {ψ : FormL symbs sorts} (P : {sorts : List symbs.signature.S} → FormL symbs sorts → Prop) : φ.Context ψ → Prop
  | .refl => True
  | @FormL.Context.head _ _ _ _ _ _ rest => P rest
  | @FormL.Context.tail _ _ _ _ _ _ rest₁ _ rest₂ _ => P rest₁ ∧ P rest₂

end Context

def subst_to_ctx (χ : Form sig s)
          {φ : Form sig s}
          {ψ : FormL sig sorts}
          (C : Context φ ψ) :
          χ.Context C[χ] := by
  cases ψ with
  | cons χ χs =>
      cases C
      . exact Context.head
      . apply Context.tail
        apply subst_to_ctx
  | _ =>
      cases C
      . exact Context.refl

end FormL
