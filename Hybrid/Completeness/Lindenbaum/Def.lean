import Hybrid.Language
import Hybrid.Semantics
import Hybrid.Proof.Hilbert

section ExperimentalRemoveMe

variable {α: Type u}
variable [DecidableEq α]
variable {S : Symbols α}
variable {s : S.signature.S}

noncomputable def Symbols.extend (S : Symbols α): Symbols α where
  signature := S.signature
  prop := S.prop
  nom  := λ s => S.nom s ∪ (Set.partition $ S.hExtInf s).s₁
  svar := S.svar
  propCtbl := S.propCtbl
  nomCtbl  := λ s =>
    by
      apply Classical.choice
      rw [←Set.countable_iff_nonempty_encodable, Set.countable_union]
      apply And.intro $ Set.countable_iff_nonempty_encodable.mpr ⟨S.nomCtbl s⟩
      rw [Set.countable_iff_nonempty_encodable]
      apply Nonempty.intro
      have := Denumerable.mk' $ Classical.choice (Set.partition $ S.hExtInf s).cInfOne
      apply Encodable.ofCountable
  svarCtbl := S.svarCtbl
  nomExt   := λ s => (Set.partition $ S.hExtInf s).s₂
  hExtInf  := by
    intro s
    exact (Set.partition $ S.hExtInf s).cInfTwo
  hExtDisj := by
    intro s
    refine Disjoint.inter_eq ?_
    simp only [Set.disjoint_union_left]
    apply And.intro
    . apply Set.disjoint_of_subset
      . intro h1 h2
        exact h2
      . intro h1 h2
        have : h1 ∈ (Set.partition $ S.hExtInf s).s₁ ∪ (Set.partition $ S.hExtInf s).s₂ := by simp_all only [Set.mem_union,
          or_true]
        rw [(Set.partition $ S.hExtInf s).hunion] at this
        exact this
      . simp only [Set.disjoint_iff, Set.subset_empty_iff]
        exact S.hExtDisj s
    . simp [Set.disjoint_iff]
      exact (Set.partition $ S.hExtInf s).hinter

noncomputable instance : Inhabited (S.extend.nomType t) where
  default := by
    simp [Symbols.extend, Symbols.nomType, Set.partition, Set.Elem]
    exact ⟨(Classical.choice (S.hExtInf t)).symm 0, by apply Or.inr; exists 0⟩

@[simp]
def extendNom (n : S.nom s) : S.extend.nom s := ⟨n, by simp only [Symbols.extend, Set.mem_union, Subtype.coe_prop, true_or]⟩

@[simp]
def Symbols.nominal.extend : S.nominal s → S.extend.nominal s
  | .nom n   => .nom $ extendNom n
  | .ctNom k => .ctNom k

@[simp]
def FormL.extend : FormL S ss → FormL S.extend ss
  | .nom n    => .nom n.extend
  | .prop p   => .prop p
  | .svar x   => .svar x
  | .cons φ ψ => .cons φ.extend ψ.extend
  | .appl σ φ => .appl σ φ.extend
  | .or φ ψ   => .or φ.extend ψ.extend
  | .neg φ    => .neg φ.extend
  | .at k φ   => .at k.extend φ.extend
  | .bind x φ => .bind x φ.extend

@[simp]
def PremiseSet.extend (Γ : PremiseSet S s) : PremiseSet S.extend s := Γ.image FormL.extend

@[simp]
def AxiomSet.extend (Λ : AxiomSet S) : AxiomSet S.extend := λ s => (Λ s).image FormL.extend

@[simp]
def Model.restrict (mExt : Model S.extend) : Model S where
  «Fr» := mExt.Fr
  Vₚ   := mExt.Vₚ
  Vₙ   := mExt.Vₙ ∘ extendNom

theorem satExtend {φ : FormL S ss} :(⟨M, g, w⟩ ⊨ φ.extend) ↔ ⟨M.restrict, g, w⟩ ⊨ φ := by
    induction φ generalizing g with
    | nom n =>
        apply Iff.intro
        . intro h
          cases n
          repeat {
          . simp only [FormL.extend, Symbols.nominal.extend, extendNom, Sat.nom] at h
            subst h
            simp [Model.VNom]
          }
        . intro h
          cases n
          repeat {
          . simp [Model.VNom] at h ⊢
            subst h
            rfl
          }
    | cons φ ψ ih1 ih2 =>
        apply Iff.intro
        repeat {
        . intro h
          simp [ih1, ih2] at h ⊢
          exact And.intro h.1 h.2
        }
    | appl σ φ ih =>
        apply Iff.intro
        . intro h
          simp at h ⊢
          match h with
          | ⟨w', h⟩ =>
            exists w'
            exact And.intro (ih.mp h.1) h.2
        . intro h
          simp at h ⊢
          match h with
          | ⟨w', h⟩ =>
            exists w'
            exact And.intro (ih.mpr h.1) h.2
    | or φ ψ ih1 ih2  =>
        apply Iff.intro
        repeat {
        . intro h
          simp [ih1, ih2] at h ⊢
          apply Or.elim h
          . intro h; apply Or.inl
            exact h
          . intro h; apply Or.inr
            exact h
        }
    | neg φ ih =>
        apply Iff.intro
        repeat {
        . intro h
          simp [ih] at h ⊢
          intro habs
          apply h
          exact habs
        }
    | «at» k φ ih =>
        apply Iff.intro
        . intro h
          cases k
          repeat {
            simp at h ⊢
            exact ih.mp h
          }
        . intro h
          cases k
          repeat {
            simp at h ⊢
            exact ih.mpr h
          }
    | bind x φ ih =>
        apply Iff.intro
        repeat {
        . intro h
          simp [ih] at h ⊢; intro g' hg'
          specialize h g' hg'
          exact h
        }
    | _ =>
      apply Iff.intro
      repeat {
      . intro h
        simp at h ⊢ ; exact h
      }

@[simp]
lemma FormL.extendDual {φ : FormL S (s :: ss)} {σ : S.signature.«Σ» (s :: ss) s'} : (ℋ⟨σ⟩ᵈ φ).extend = (ℋ⟨σ⟩ᵈ φ.extend : Form S.extend s') := sorry

def FormL.Context.extend {φ : Form S s} : φ.Context ψ → φ.extend.Context ψ.extend := sorry

@[simp]
lemma extendCtxSubst {φ : Form S s} {C : φ.Context ψ} : C[χ].extend = C.extend[χ.extend] := sorry

def Proof.extend {s : S.signature.S} {φ : Form S s} : Proof Λ s φ → Proof Λ.extend s φ.extend
  | .ax φ        => .ax ⟨φ.1.extend, by aesop⟩
  | .prop1 φ ψ   => .prop1 φ.extend ψ.extend
  | .prop2 φ ψ χ => .prop2 φ.extend ψ.extend χ.extend
  | .prop3 φ ψ   => .prop3 φ.extend ψ.extend
  | .k φ ψ χ σ C => by
      simp only [FormL.extend, FormL.extendDual, extendCtxSubst]
      exact .k φ.extend ψ.extend χ.extend σ C.extend
  | .mp h1 h2    => .mp h1.extend h2.extend
  | .ug C h      => by
      simp only [FormL.extendDual]
      exact ug C.extend h.extend
  | _ => sorry

def Proof.restrict {Λ : AxiomSet S} {φ : Form S s} : Proof Λ.extend s φ.extend → Proof Λ s φ := sorry

end ExperimentalRemoveMe

section ExperimentalLindebaumDef

variable {α: Type u}
variable [DecidableEq α]
variable {S : Symbols α}
variable {s : S.signature.S}

open Classical

/-
structure ExtendiblePremiseSet (S : Symbols α) (s: S.signature.S) where
  set : PremiseSet S s
  unused_nominals : { n : S.nomType t | ¬set.occurs n }.CountablyInfinite
-/

abbrev Symbols.nominalFamily {S : Symbols α} := {t : S.signature.S} → Set (S.nomType t)
def singleton (k : S.nomType t) : S.nominalFamily :=
  λ {s} => if h : s = t then { h ▸ k } else { }
instance : Union S.nominalFamily where
  union s₁ s₂ t := @s₁ t ∪ @s₂ t
instance : SDiff S.nominalFamily where
  sdiff s₁ s₂ t := @s₁ t \ @s₂ t
instance : Membership S.nominalFamily (S.nomType t) where
  mem k s := k ∈ @s t

def PremiseSet.nominals (Γ : PremiseSet S s) : S.nominalFamily :=
  { k | ∃ φ ∈ Γ, FormL.occurs k φ }

structure LindenbaumState (S : Symbols α) where
  unused_nominals : S.extend.nominalFamily

abbrev LindenbaumM (S : Symbols α) := StateM (LindenbaumState S)

noncomputable def get_nominal : LindenbaumM S (S.extend.nom t) := do
  let ⟨unused_nominals⟩ <- StateT.get
  pure $
  if h : ∃ k, k ∈ unused_nominals then
    h.choose
  else default

def add_nominal (k : S.extend.nom t) : LindenbaumM S PUnit := do
  let ⟨unused_nominals⟩ <- StateT.get
  StateT.set ( { unused_nominals := unused_nominals \ singleton k } )

def add_nominals (noms : S.extend.nominalFamily) : LindenbaumM S PUnit := do
  let ⟨unused_nominals⟩ <- StateT.get
  StateT.set ({ unused_nominals := unused_nominals \ noms } : LindenbaumState S)

def empty : LindenbaumM S (PremiseSet S.extend s) := pure { }

def add_set (Γ : PremiseSet S s): LindenbaumM S (PremiseSet S.extend s) := do
  let Γ₁ := Γ.extend
  add_nominals Γ₁.nominals
  pure Γ₁

noncomputable def witness_var_sort_idx (t : S.extend.signature.S) (idx : ℕ) : LindenbaumM S (Form S.extend s) := do
  let x : S.extend.svar t := Denumerable.ofNat _ idx
  let jₓ <- get_nominal
  add_nominal jₓ
  pure $ ℋ@ (.nom jₓ) (.svar x)

noncomputable def witness_var_sort (t : S.extend.signature.S) : LindenbaumM S (PremiseSet S.extend s) := do
  
  sorry

/-
noncomputable def fresh_nominal (idx : ℕ): LindenbaumM S (Option $ S.extend.nomType t) := do
  let ⟨state⟩ <- StateT.get
  pure $ do
    let k <- (S.extend.nomCtbl t).decode idx
    if k ∈ state then
      pure k
    else none
-/

noncomputable def PremiseSet.Lindenbaum (Λ : AxiomSet S) (Γ : PremiseSet S s) : ℕ → LindenbaumM S (PremiseSet S.extend s)
| 0       => do
    let Γ' <- add_set Γ
    let kₛ : S.extend.nomType s <- get_nominal

    pure $ Γ' ∪ { FormL.nom kₛ }
| .succ i => sorry


/-
noncomputable def PremiseSet.Lindenbaum (Λ : AxiomSet S) (Γ : PremiseSet S s) : ℕ → ExtendiblePremiseSet S.extend s
| 0       =>
    let Γ' : ExtendiblePremiseSet _ _ (ext.m+ Λ) := ⟨(Γ.embed ext Λ).set ∪ (Γ.embed ext Λ).at_witness_vars, enough_nominals_at_witness⟩
    ⟨Γ'.set ∪ { ℋNom (.nom $ Γ'.prod_even_nominal _ 0 0) }, enough_nominals_singleton⟩
| .succ i =>
    let φ_i : Form ext.target (ext.m+ s) := ofNat _ i
    let Γ' : ExtendiblePremiseSet ext.target (ext.m+ s) (ext.m+ Λ) := ⟨(PremiseSet.Lindenbaum Λ Γ i).set ∪ { φ_i }, enough_nominals_singleton⟩
    if ((PremiseSet.Lindenbaum Λ Γ i).set ∪ { ofNat _ i }).consistent (ext.m+ Λ) then
      match φ_i with
      -- note that the sort of new nominal k is the sort of x, and may differ from (ext.m+ s)
      | ℋ@ j (ℋ∃ x φ) => ⟨Γ'.set ∪ { ℋ@ j φ[(Γ'.prod_even_nominal _ i 0) // x]}, enough_nominals_singleton⟩
      -- note that the sort of new nominal k is the sort s' of φ, and may differ from (ext.m+ s)
      | ℋ@ j (ℋ⟨σ⟩ χ) => ⟨Γ'.set ∪ Γ'.paste_args j σ χ i, enough_nominals_paste⟩
      | _ => Γ'
    else PremiseSet.Lindenbaum Λ Γ i

end ExperimentalLindebaumDef
-/

/-
import Hybrid.Completeness.Lindenbaum.Sets
import Hybrid.Completeness.Lindenbaum.Enumeration

namespace Completeness

open Completeness
open Encodable
open Denumerable

variable {α β : Type u}
variable [DecidableEq α] [β_deq : DecidableEq β]
variable {S : Symbols α}
variable {s : S.signature.S}
variable (ext : @S.nominal_extension α β β_deq β)

abbrev PremiseSet.embed (Γ : PremiseSet S s) (Λ : AxiomSet S) : ExtendiblePremiseSet ext.target (ext.m+ s) (ext.m+ Λ) :=
  ⟨ext.m+ Γ, enough_nominals_embed⟩

open Classical

noncomputable def PremiseSet.Lindenbaum (Λ : AxiomSet S) (Γ : PremiseSet S s) : ℕ → ExtendiblePremiseSet ext.target (ext.m+ s) (ext.m+ Λ)
| 0       =>
    let Γ' : ExtendiblePremiseSet _ _ (ext.m+ Λ) := ⟨(Γ.embed ext Λ).set ∪ (Γ.embed ext Λ).at_witness_vars, enough_nominals_at_witness⟩
    ⟨Γ'.set ∪ { ℋNom (.nom $ Γ'.prod_even_nominal _ 0 0) }, enough_nominals_singleton⟩
| .succ i =>
    let φ_i : Form ext.target (ext.m+ s) := ofNat _ i
    let Γ' : ExtendiblePremiseSet ext.target (ext.m+ s) (ext.m+ Λ) := ⟨(PremiseSet.Lindenbaum Λ Γ i).set ∪ { φ_i }, enough_nominals_singleton⟩
    if ((PremiseSet.Lindenbaum Λ Γ i).set ∪ { ofNat _ i }).consistent (ext.m+ Λ) then
      match φ_i with
      -- note that the sort of new nominal k is the sort of x, and may differ from (ext.m+ s)
      | ℋ@ j (ℋ∃ x φ) => ⟨Γ'.set ∪ { ℋ@ j φ[(Γ'.prod_even_nominal _ i 0) // x]}, enough_nominals_singleton⟩
      -- note that the sort of new nominal k is the sort s' of φ, and may differ from (ext.m+ s)
      | ℋ@ j (ℋ⟨σ⟩ χ) => ⟨Γ'.set ∪ Γ'.paste_args j σ χ i, enough_nominals_paste⟩
      | _ => Γ'
    else PremiseSet.Lindenbaum Λ Γ i

def PremiseSet.LindenbaumExtension (Λ : AxiomSet S) (Γ : PremiseSet S s) : PremiseSet ext.target (ext.m+ s) :=
  { φ | ∃ i : ℕ, φ ∈ (Γ.Lindenbaum ext Λ i).set }

end Completeness
-/
