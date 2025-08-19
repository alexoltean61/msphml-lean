import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable

structure Signature (α : Type u) where
  -- α: the carrier set of sorts
  --  e.g., if α is String, S may be {"nat", "bool"}
  S    : Set α
  Sig  : List S → S → Set α
  N    : S → Set α

  sortsCtbl : Encodable S
  opsCtbl (dom range) : Encodable (Sig dom range)
  nomCtbl (s)         : Encodable (N s)

  sNonEmpty : Inhabited S
  nNonEmpty (s) : Inhabited (N s)
  -- Should you add further inhabitance constraints?
  -- Should you add disjointness constraints?

structure Symbols (α : Type u) where
  signature  : Signature α

  prop : (s : signature.S) → Set α
  nom  : (s : signature.S) → Set α
  svar : (s : signature.S) → Set α

  propCtbl (s) : Encodable (prop s)
  nomCtbl  (s) : Encodable (nom s)
  svarCtbl (s) : Denumerable (svar s)

  -- Should you add disjointness constraints?

-- Often when dealing with syntax, we treat constant nominals and regular nominals uniformly.
-- It helps to have their disjoint union defined as a standalone type.
variable {symbs : Symbols α}
variable {s : symbs.signature.S}
def Symbols.nominal := λ s => symbs.signature.N s ⊕ symbs.nom s

instance : Coe (symbs.signature.N s) (symbs.nominal s) where
  coe := Sum.inl
instance : Coe (symbs.nom s) (symbs.nominal s) where
  coe := Sum.inr

-- The `prop` and `svar` fields of the `Symbols` structure are defined as Sets.
-- Usually Lean is able to coerce a Set to a Type, but not always.
-- For such cases, we define the explicit (many-sorted families of) types below.
abbrev Symbols.propType (symbs : Symbols α) := λ s => Set.Elem (symbs.prop s)
abbrev Symbols.svarType (symbs : Symbols α) := λ s => Set.Elem (symbs.svar s)

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
    isTrue (Subtype.eq h)
  else isFalse (λ habs => h (congrArg Subtype.val habs))

instance [DecidableEq α] {symbs : Symbols α} {s : symbs.signature.S} : DecidableEq (symbs.prop s) := λ i j =>
  if h : (i.1 = j.1) then
    isTrue (Subtype.eq h)
  else isFalse (λ habs => h (congrArg Subtype.val habs))

instance [DecidableEq α] {symbs : Symbols α} {s : symbs.signature.S} : DecidableEq (symbs.nom s) := λ i j =>
  if h : (i.1 = j.1) then
    isTrue (Subtype.eq h)
  else isFalse (λ habs => h (congrArg Subtype.val habs))

instance [DecidableEq α] {symbs : Symbols α} {s : symbs.signature.S} : DecidableEq (symbs.svar s) := λ i j =>
  if h : (i.1 = j.1) then
    isTrue (Subtype.eq h)
  else isFalse (λ habs => h (congrArg Subtype.val habs))

instance [DecidableEq α] {symbs : Symbols α} {s : symbs.signature.S} : DecidableEq (symbs.nominal s) := λ i j =>
  match i with
  | .inl i => match j with
            | .inl j => if h : i = j then isTrue (congrArg Sum.inl h) else isFalse (λ habs => h $ Sum.inl.inj habs)
            | .inr _ => isFalse (λ habs => Sum.noConfusion habs)
  | .inr i => match j with
            | .inl _ => isFalse (λ habs => Sum.noConfusion habs)
            | .inr j => if h : i = j then isTrue (congrArg Sum.inr h) else isFalse (λ habs => h $ Sum.inr.inj habs)

def Symbols.nominal.ne {symbs : Symbols α} [DecidableEq α] {s₁ s₂ : symbs.signature.S} (i : symbs.nominal s₁) (j : symbs.nominal s₂) : Prop := (h : s₁ = s₂) → h ▸ i ≠ j

infix:50 "≠ₛ" => Symbols.nominal.ne
