import Hybrid.Language.Signature

inductive FormL (symbs : Symbols α) : List symbs.signature.S → Type u
  | prop : symbs.prop s → FormL symbs [s]
  | nom  : symbs.nominal s → FormL symbs [s]
  | svar : symbs.svar s → FormL symbs [s]
  | appl : symbs.signature.Sig (h :: t) s → FormL symbs (h :: t) → FormL symbs [s]
--  | ct   : symbs.signature.Sig [] s → FormL symbs [s]
  | or   : FormL symbs [s] → FormL symbs [s] → FormL symbs [s]
  | neg  : FormL symbs [s] → FormL symbs [s]
  | at   : symbs.nominal t → FormL symbs [t] → FormL symbs [s]
  | bind : symbs.svar t → FormL symbs [s] → FormL symbs [s]
  | cons : FormL symbs [s₁] → FormL symbs (s₂ :: t) → FormL symbs (s₁ :: s₂ :: t)

@[reducible] def Form (symbs : Symbols α) (s : symbs.signature.S) := FormL symbs [s]

def FormL.negAll : FormL sig sorts → FormL sig sorts
  | .prop p   => .neg (.prop p)
  | .nom n    => .neg (.nom n)
  | .svar x   => .neg (.svar x)
  | .cons φ ψ => .cons (.neg φ) ψ.negAll
  | .appl σ φ => .neg (.appl σ φ)
  | .or φ ψ   => .neg (.or φ ψ)
  | .neg φ    => .neg (.neg φ)
  | .at k φ   => .neg (.at k φ)
  | .bind x φ => .neg (.bind x φ)

def FormL.applDual {symbs : Symbols α}
                   {s h : symbs.signature.S}
                   {t : List symbs.signature.S}
                   (σ : symbs.signature.Sig (h :: t) s)
                   (φ : FormL symbs (h :: t)) : FormL symbs [s] :=
  .neg (.appl σ φ.negAll)

def FormL.implies (φ ψ : FormL symbs [s]) : FormL symbs [s] := φ.neg.or ψ
def FormL.and (φ ψ : FormL symbs [s]) : FormL symbs [s] := (φ.neg.or ψ.neg).neg
def FormL.iff (φ ψ : FormL symbs [s]) : FormL symbs [s] := (φ.implies ψ).and (ψ.implies φ)

prefix:65 "ℋNom "   => FormL.nom
prefix:65 "ℋProp "  => FormL.prop
prefix:65 "ℋVar "   => FormL.svar

syntax (priority := high) "(" term,+ ")" : term
macro_rules
  | `(($x)) => `($x)
  | `(($x, $xs:term,*)) => `(FormL.cons $x ($xs,*))
notation:65 "ℋ⟨" σ:lead "⟩" φ:arg => FormL.appl σ φ
notation:65 "ℋ⟨" σ:lead "⟩ᵈ" φ:arg => FormL.applDual σ φ

notation:63 "ℋ@ " j:arg φ:arg => FormL.at j φ
notation:63 "ℋ∀ " x:arg φ:arg => FormL.bind x φ
notation:62 "ℋ∃ " x:arg φ:arg => FormL.neg (FormL.bind x (FormL.neg φ))

prefix:60 "∼ "  => FormL.neg

infixr:55 " ⋁ "  => FormL.or
notation:57 φ:40 " ⋀ " ψ:57  => FormL.and φ ψ
notation:53 φ:40 " ⟶ " ψ:53  => FormL.implies φ ψ
notation:51 φ:40 " ←→ " ψ:51  => FormL.iff φ ψ

/-
section Coercions

  variable (symbs : Symbols α)
  variable (s : symbs.signature.S)
  instance : Coe (symbs.svar s) (Form symbs s) where
    coe := FormL.svar

end Coercions

--/

-- Define H(@), the fragment of H(@, ∀) without binders, as a subtype of Form
def HAt : FormL symbs s → Prop
| ℋ∀ _ _        => ⊥
| ℋProp _       => ⊤
| ℋNom  _       => ⊤
| ℋVar _        => ⊤
| ℋ⟨_⟩ args      => HAt args
| φ ⋁ ψ        => HAt φ ∧ HAt ψ
| ∼ φ          => HAt φ
| ℋ@ _ φ       => HAt φ
| (h, t)       => HAt h ∧ HAt t

def FormHAt (symbs: Symbols α) s := {φ : Form symbs s // HAt φ}


-- Premise set is the type of premises Γₛ which may be used for deduction.
-- Note that we will be defining a *local* deduction relation, which in this
-- many-sorted setting involves sets of premises of the same sort.
@[reducible] def PremiseSet (symbs : Symbols α) (s: symbs.signature.S): Type u := Set (Form symbs s)

@[reducible] def FiniteChoice (Γ : PremiseSet symbs s): Type u := List Γ
@[reducible] def FiniteChoice.conjunction {Γ: PremiseSet symbs s}: FiniteChoice Γ → Form symbs s
  | []      =>
      let p := FormL.prop ((symbs.propNonEmpty s).default)
      p ⋁ ∼p
  | [φ]     => φ
  | φ :: ψs =>
      let ψs_as_premiseSet : FiniteChoice Γ := ψs -- annoying
      ψs_as_premiseSet.conjunction ⋀ φ


-- Do we need a DecidableEq instance for FormL?

@[reducible] def AxiomSet (symbs : Symbols α) := (s: symbs.signature.S) → Set (Form symbs s)
