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
