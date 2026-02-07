import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable

structure Signature (α : Type u) where
  -- α: the carrier set of sorts
  --  e.g., if α is String, S may be {"nat", "bool"}
  S    : Set α
  «Σ»  : List S → S → Set α
  N    : S → Set α

structure Symbols (α : Type u) where
  signature  : Signature α

  prop : (s : signature.S) → Set α
  nom  : (s : signature.S) → Set α
  svar : (s : signature.S) → Set α

  svarCtbl (s) : Denumerable (svar s)

-- Often when dealing with syntax, we treat constant nominals and regular nominals uniformly.
-- It helps to have their disjoint union defined as a standalone type.
variable {symbs : Symbols α}
variable {s : symbs.signature.S}

inductive Symbols.nominal (s : symbs.signature.S)
  | nom   : symbs.nom s → Symbols.nominal s
  | ctNom : symbs.signature.N s → Symbols.nominal s

instance : Coe (symbs.nom s) (symbs.nominal s) where
  coe := .nom
instance : Coe (symbs.signature.N s) (symbs.nominal s) where
  coe := .ctNom

-- The `prop` and `svar` fields of the `Symbols` structure are defined as Sets.
-- Usually Lean is able to coerce a Set to a Type, but not always.
-- For such cases, we define the explicit (many-sorted families of) types below.
abbrev Symbols.propType (symbs : Symbols α) := λ s => Set.Elem (symbs.prop s)
abbrev Symbols.svarType (symbs : Symbols α) := λ s => Set.Elem (symbs.svar s)
abbrev Symbols.nomType (symbs : Symbols α)  := λ s => Set.Elem (symbs.nom s)
abbrev Symbols.ctNomType (symbs : Symbols α):= λ s => Set.Elem (symbs.signature.N s)

@[coe]
abbrev coerceNomTypeNominal : symbs.nomType s → symbs.nominal s := .nom
@[coe]
abbrev coerceCtNomTypeNominal : symbs.ctNomType s → symbs.nominal s := .ctNom
instance : Coe (symbs.nomType s) (symbs.nominal s) where
  coe := coerceNomTypeNominal
instance : Coe (symbs.ctNomType s) (symbs.nominal s) where
  coe := coerceCtNomTypeNominal

instance : Denumerable (symbs.svarType s) where
  encode := (symbs.svarCtbl s).encode
  decode := (symbs.svarCtbl s).decode
  encodek := (symbs.svarCtbl s).encodek
  decode_inv := (symbs.svarCtbl s).decode_inv

instance : OfNat (symbs.svarType s) (n : Nat) where
  ofNat := Denumerable.ofNat (symbs.svarType s) n

instance : HAdd (symbs.svarType s) Nat (symbs.svarType s) where
  hAdd := λ x n => OfNat.ofNat ((symbs.svarCtbl s).encode x + n)

instance : HAdd Nat (symbs.svarType s)  (symbs.svarType s) where
  hAdd := λ n x => OfNat.ofNat (n + (symbs.svarCtbl s).encode x)

instance [DecidableEq α] {symbs : Symbols α} {s : symbs.signature.S} : DecidableEq (symbs.signature.N s) := λ i j =>
  if h : (i.1 = j.1) then
    isTrue (Subtype.ext h)
  else isFalse (λ habs => h (congrArg Subtype.val habs))

instance [DecidableEq α] {symbs : Symbols α} {s : symbs.signature.S} : DecidableEq (symbs.prop s) := λ i j =>
  if h : (i.1 = j.1) then
    isTrue (Subtype.ext h)
  else isFalse (λ habs => h (congrArg Subtype.val habs))

instance [DecidableEq α] {symbs : Symbols α} {s : symbs.signature.S} : DecidableEq (symbs.nom s) := λ i j =>
  if h : (i.1 = j.1) then
    isTrue (Subtype.ext h)
  else isFalse (λ habs => h (congrArg Subtype.val habs))

instance [DecidableEq α] {symbs : Symbols α} {s : symbs.signature.S} : DecidableEq (symbs.svar s) := λ i j =>
  if h : (i.1 = j.1) then
    isTrue (Subtype.ext h)
  else isFalse (λ habs => h (congrArg Subtype.val habs))

instance [DecidableEq α] {symbs : Symbols α} {s : symbs.signature.S} : DecidableEq (symbs.nominal s) := λ i j =>
  match i with
  | .nom i => match j with
            | .nom j => if h : i = j then isTrue (congrArg Symbols.nominal.nom h) else isFalse (λ habs => h $ Symbols.nominal.nom.inj habs)
            | .ctNom _ => isFalse (λ habs => by simp only [reduceCtorEq] at habs)
  | .ctNom i => match j with
            | .nom _ => isFalse (λ habs => by simp only [reduceCtorEq] at habs)
            | .ctNom j => if h : i = j then isTrue (congrArg Symbols.nominal.ctNom h) else isFalse (λ habs => h $ Symbols.nominal.ctNom.inj habs)

def Symbols.nominal.ne {symbs : Symbols α} [DecidableEq α] {s₁ s₂ : symbs.signature.S} (i : symbs.nominal s₁) (j : symbs.nominal s₂) : Prop := (h : s₁ = s₂) → h ▸ i ≠ j

infix:50 "≠ₛ" => Symbols.nominal.ne
