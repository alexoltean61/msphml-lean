import Hybrid.Language.Context

namespace FormL

/--
  Given a formula (list) `χ`, a term of type `χ.Elem` can be constructed only from a formula
    `φ : Form symbs s` which *occurs* in `χ` (i.e., a term of type `φ.Context χ` can be given).
  Thus, `φ` is an element of `χ`.
  Note that different occurences of `φ` in `χ` correspond to different `χ.Elem` terms.
-/
def Elem {symbs : Symbols α} {sorts : List symbs.signature.S} (χ : FormL symbs sorts) :=
  (s : symbs.signature.S) × (φ : Form symbs s) × (φ.Context χ)

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
instance elem_encodable (χ : FormL symbs sorts) : Encodable χ.Elem where
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
