import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable

structure Signature (α : Type u) where
  -- α: the carrier set of sorts
  --  e.g., if α is String, S may be {"nat", "bool"}
  S    : Set α
  Sig  : List S → S → Set α
  N    : S → Set α

  sortsCtbl : S.Countable
  opsCtbl   : ∀ dom range, (Sig dom range).Countable
  nomCtbl   : ∀ s, (N s).Countable

  sNonEmpty : Inhabited S
  -- Should you add further inhabitance constraints?
  -- Should you add disjointness constraints?

structure Symbols (α : Type u) where
  signature  : Signature α

  prop : (s : signature.S) → Set α
  nom  : (s : signature.S) → Set α
  svar : (s : signature.S) → Set α

  propCtbl : ∀ s, (prop s).Countable
  nomCtbl  : ∀ s, (nom s).Countable
  svarCtbl : ∀ s, (svar s).Countable
  -- ^ actually, this should be Denumerable: not just countable ("cel mult numarabil") but infinite

  propNonEmpty : ∀ s, Inhabited (prop s)
  -- Should you add further inhabitance constraints?
  -- Should you add disjointness constraints?

-- Often when dealing with syntax, we treat constant nominals and regular nominals uniformly.
-- It helps to have their disjoint union defined as a standalone type.
def Symbols.nominal (symbs : Symbols α) := λ s => symbs.signature.N s ⊕ symbs.nom s

-- The `prop` and `svar` fields of the `Symbols` structure are defined as Sets.
-- Usually Lean is able to coerce a Set to a Type, but not always.
-- For such cases, we define the explicit (many-sorted families of) types below.
def Symbols.propType (symbs : Symbols α) := λ s => Set.Elem (symbs.prop s)
def Symbols.svarType (symbs : Symbols α) := λ s => Set.Elem (symbs.svar s)

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
