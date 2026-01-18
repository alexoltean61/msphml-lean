import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Algebra.Ring.Parity

abbrev Set.CountablyInfinite (set : Set α) := Nonempty (set ≃ ℕ)

structure Set.CountablyInfinitePartition {set : Set α} where
  s₁ : Set α
  s₂ : Set α
  hunion : s₁ ∪ s₂ = set
  hinter : s₁ ∩ s₂ = ∅
  cInfOne : s₁.CountablyInfinite
  cInfTwo : s₂.CountablyInfinite

noncomputable def Set.partition {set : Set α} (h : set.CountablyInfinite) : set.CountablyInfinitePartition :=
  have iso := Classical.choice h
  ⟨
    {iso.symm (2 * n) | n : ℕ}, {iso.symm (2 * n + 1) | n : ℕ},
    by
      simp [Set.union_def]
      have : set = {↑(iso.symm n) | n : ℕ } := by
        apply ext ; intro x ; apply Iff.intro
        . intro hin
          simp only [mem_setOf_eq]
          have ⟨a, _⟩ := iso.symm.surjective ⟨x, hin⟩
          exists a
          simp_all only
        . simp only [mem_setOf_eq, forall_exists_index]
          intro n h
          subst h
          simp_all only [Subtype.coe_prop]
      simp only [this] ; clear this
      apply ext ; intro x ; apply Iff.intro
      . intro h
        simp at h
        apply Or.elim h
        . intro ⟨n, hn⟩
          exists (2 * n)
        . intro ⟨n, hn⟩
          exists (2 * n + 1)
      . simp only [mem_setOf_eq, forall_exists_index]
        intro n h
        subst h
        apply Or.elim n.even_or_odd
        . intro ⟨m, heven⟩
          subst heven
          apply Or.inl
          exists m
          rw [Nat.two_mul m]
        . intro ⟨m, hodd⟩
          subst hodd
          apply Or.inr
          simp_all only [exists_apply_eq_apply],
    by
      simp only [inter_def, mem_setOf_eq, eq_empty_iff_forall_notMem, not_and, not_exists,
        forall_exists_index, forall_apply_eq_imp_iff, ←Subtype.eq_iff]
      intro a b habs
      apply Nat.two_mul_ne_two_mul_add_one
      exact (iso.symm.injective habs).symm,
    by
      apply Nonempty.intro
      apply (Equiv.ofBijective (λ n => ⟨iso.symm (2 * n), by simp only [mem_setOf_eq, exists_apply_eq_apply]⟩) ?is_bijective).symm
      case is_bijective =>
        apply And.intro
        . intro a b; intro heq
          simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq, ←
          Subtype.eq_iff, EmbeddingLike.apply_eq_iff_eq, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero,
          or_false] at heq
          exact heq
        . intro ⟨x, ⟨n, hn⟩⟩
          exists n
          simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
          exact hn,
    by
      apply Nonempty.intro
      apply (Equiv.ofBijective (λ n => ⟨iso.symm (2 * n + 1), by simp only [mem_setOf_eq, exists_apply_eq_apply]⟩) ?is_bijective).symm
      case is_bijective =>
        apply And.intro
        . intro a b; intro heq
          simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq, ← Subtype.eq_iff,
            EmbeddingLike.apply_eq_iff_eq, Nat.add_right_cancel_iff, mul_eq_mul_left_iff,
            OfNat.ofNat_ne_zero, or_false] at heq
          exact heq
        . intro ⟨x, ⟨n, hn⟩⟩
          exists n
          simp only [coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
          exact hn
  ⟩

structure Signature (α : Type u) where
  -- α: the carrier set of sorts
  --  e.g., if α is String, S may be {"nat", "bool"}
  S    : Set α
  «Σ»  : List S → S → Set α
  N    : S → Set α

  sortsCtbl : Encodable S
  opsCtbl (dom range) : Encodable («Σ» dom range)
  nomCtbl (s)         : Encodable (N s)

  -- sigDisjS : S ∩ ⋃ ss, ⋃ s, «Σ» ss s = ∅
  -- sigDisjRange : ⋃ ss, ⋂ s, «Σ» ss s = ∅
  -- sigDisjDom   : ⋂ ss, ⋃ s, «Σ» ss s = ∅
  -- nDisjS : (⋃ s, N s) ∩ S = ∅

  sNonEmpty : Inhabited S
  nNonEmpty (s) : Inhabited (N s)

structure Symbols (α : Type u) where
  signature  : Signature α

  prop : (s : signature.S) → Set α
  nom  : (s : signature.S) → Set α
  svar : (s : signature.S) → Set α

  propCtbl (s) : Encodable (prop s)
  nomCtbl  (s) : Encodable (nom s)
  svarCtbl (s) : Denumerable (svar s)
  -- pDisjS : ⋂ s, prop s = ∅
  -- pDisjSorts : (⋃ s, prop s) ∩ signature.S = ∅
  -- pDisjSig   : (⋃ s, prop s) ∩ (⋃ ss, ⋃ s, signature.«Σ» ss s) = ∅
  -- pDisjN     : (⋃ s, prop s) ∩ (⋃ s, signature.N s) = ∅
  -- pDisjNom   : (⋃ s, prop s) ∩ (⋃ s, nom s) = ∅
  -- pDisjSvar  : (⋃ s, prop s) ∩ (⋃ s, svar s) = ∅

  -- nDisjS : ⋂ s, nom  s = ∅
  -- sDisjS : ⋂ s, svar s = ∅

  nomExt : (s : signature.S) → Set α
  hExtInf  : ∀ (s : signature.S), (nomExt s).CountablyInfinite
  hExtDisj : ∀ (s : signature.S), (nom s) ∩ (nomExt s) = ∅


inductive Test (n : ℕ) where
  | ct : Test n

def Test' := Test 5

lemma induction (a : Test') : False := by
  induction a with
  | ct => sorry


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

instance : Coe (symbs.nomType s) (symbs.nominal s) where
  coe := .nom
instance : Coe (symbs.ctNomType s) (symbs.nominal s) where
  coe := .ctNom

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
  | .nom i => match j with
            | .nom j => if h : i = j then isTrue (congrArg Symbols.nominal.nom h) else isFalse (λ habs => h $ Symbols.nominal.nom.inj habs)
            | .ctNom _ => isFalse (λ habs => Symbols.nominal.noConfusion habs)
  | .ctNom i => match j with
            | .nom _ => isFalse (λ habs => Symbols.nominal.noConfusion habs)
            | .ctNom j => if h : i = j then isTrue (congrArg Symbols.nominal.ctNom h) else isFalse (λ habs => h $ Symbols.nominal.ctNom.inj habs)

def Symbols.nominal.ne {symbs : Symbols α} [DecidableEq α] {s₁ s₂ : symbs.signature.S} (i : symbs.nominal s₁) (j : symbs.nominal s₂) : Prop := (h : s₁ = s₂) → h ▸ i ≠ j

infix:50 "≠ₛ" => Symbols.nominal.ne
