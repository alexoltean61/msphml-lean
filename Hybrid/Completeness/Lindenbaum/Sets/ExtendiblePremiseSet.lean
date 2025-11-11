import Hybrid.Language
import Hybrid.Language.Context.Elem

namespace Completeness

open Completeness
open Classical
open Encodable
open Denumerable

variable {α : Type u}
variable [DecidableEq α]
variable {S : Symbols α}
variable {s : S.signature.S}

/--
  In order to formalize Lindenbaum's Lemma, we need to ensure we deal only with sets
    of formulas (`PremiseSet`) which maintain a particular invariant:

    · There exist a countable infinity of nominals which occur neither in the `PremiseSet`,
      nor in the set of axioms by which we extend the proof system (`AxiomSet`).

  `ExtendiblePremiseSet` is the structure used to represent such sets.

  Check the definitions of `Lindenbaum` and `LindenbaumExtension` in `Def.lean` to see how we
    define and use an infinite chain of `ExtendiblePremiseSet`s.
-/
structure ExtendiblePremiseSet (S : Symbols α) (s: S.signature.S) (Λ : AxiomSet S) where
  set : PremiseSet S s
  unused_nominals : { n : S.nomType t | ¬Λ.occurs n ∧ ¬set.occurs n } ≃ ℕ

/--
  Given an index `idx : ℕ`, returns the `idx`-th unused nominal gien by an `ExtendiblePremiseSet`.
-/
abbrev ExtendiblePremiseSet.unused_nominal (Γ : ExtendiblePremiseSet S s Λ) (t : S.signature.S) (idx : ℕ) : S.nomType t :=
  ((@Γ.unused_nominals t).invFun idx).1

/--
  Given an index of an arbitrary encodable type `β`, `idx : β`, returns the `idx`-th unused nominal given by
  an `ExtendiblePremiseSet`, considering only nominals with odd indices.
-/
abbrev ExtendiblePremiseSet.odd_nominal [Encodable β] (Γ : ExtendiblePremiseSet S s Λ) (t : S.signature.S) (idx : β) : S.nomType t :=
  Γ.unused_nominal t ((encode idx) * 2 + 1)

/--
  Given an index of an arbitrary encodable type `β`, `idx : β`, returns the `idx`-th unused nominal given by
  an `ExtendiblePremiseSet`, considering only nominals with even indices.
-/
abbrev ExtendiblePremiseSet.even_nominal [Encodable β] (Γ : ExtendiblePremiseSet S s Λ) (t : S.signature.S) (idx : β) : S.nomType t :=
  Γ.unused_nominal t ((encode idx) * 2)

/--
  Given two indices of arbitrary encodable types `β` and `γ`, uses them both to address an `ExtendiblePremiseSet` (injectively),
  considering only nominals with even indices.
-/
abbrev ExtendiblePremiseSet.prod_even_nominal
    [Encodable β] [Encodable γ] (Γ : ExtendiblePremiseSet S s Λ)
    (t : S.signature.S) (idx₁ : β) (idx₂ : γ) : S.nomType t :=
  Γ.even_nominal t $ Prod.mk idx₁ idx₂

/--
  Helper for Lindenbaum's lemma, used in the completeness proof.
-/
abbrev ExtendiblePremiseSet.at_witness {t : S.signature.S} (Γ : ExtendiblePremiseSet S s Λ) : (S.svar t) → Form S s :=
  λ x => ℋ@ (.nom $ Γ.odd_nominal _ x) (ℋVar x)
/--
  Helper for Lindenbaum's lemma, used in the completeness proof.
-/
abbrev ExtendiblePremiseSet.at_witness_vars (Γ : ExtendiblePremiseSet S s Λ) : PremiseSet S s :=
  {Γ.at_witness var.2 | var : (t : S.signature.S) × S.svar t}
/--
  Helper for Lindenbaum's lemma, used in the completeness proof.
-/
abbrev ExtendiblePremiseSet.paste_args
    {t t' : S.signature.S}
    (Γ : ExtendiblePremiseSet S s Λ)
    (j : S.nominal t)
    (σ : S.signature.«Σ» (t' :: ss) t)
    (χ : FormL S (t' :: ss)) : ℕ → PremiseSet S s :=
  λ i => { ℋ@ j (ℋ⟨σ⟩ e.2.2[ℋNom (.nom $ Γ.prod_even_nominal _ i e)]) ⋀ ℋ@ (.nom $ Γ.prod_even_nominal _ i e) e.2.1 | e : χ.Elem }

end Completeness
