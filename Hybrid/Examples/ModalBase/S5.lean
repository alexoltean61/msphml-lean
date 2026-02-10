/-
  This module declares the S5 proof system for the base modal language.

  It extends the proof system with schemas (T) and (5). Axiom K is already
  part of the proof system, so no need to be mentioned in the extension.

  Any derivation *must* only reference formulas in the base fragment (no state vars, binders).
  This is represented by the `S5Pf` type. It contains all proofs from the S5 axioms, where
  the formulas referenced are strictly in the base modal fragment.

  It's clunky to construct `S5Pf` terms directly, because we're always forced to provide not just
  the proof, but also the guarantee that it stays within its fragment.

  That's why we defined the lemmas `ax_k`, `ax_t`, `ax_a5`, `modusPonens` and `necessitation`,
  which expose the S5 axioms and proof rules directly, and allow us to forget that we're actually
  reasoning inside a fragment of many-sorted polyadic hybrid logic.
-/

import Hybrid.Examples.ModalBase.Signature

inductive S5Schema : Modal → Type where
  | AxT : S5Schema (□ φ ⟶ φ)
  | Ax5 : S5Schema (◇ φ ⟶ □◇φ)

def S5 : AxiomSet ModalBase :=
  λ _ => setOf ( λ form => ∃ (φ : Modal) (_ : S5Schema φ), φ.toForm ≍ form )

def S5Pf (φ : Modal) := Proof.fragment IsBase S5 φ.1

namespace S5
open Proof

def ax_k : S5Pf (□ (φ ⟶ ψ) ⟶ □ φ ⟶ □ ψ) := by
  simp only [Modal.boxIsLL]
  apply Proof.fragment.mk (k _ _ (φ.toForm ⟶ ψ.toForm) ModalBase.poss .refl)
  -- Below, we prove the base modal fragment is closed under K axiom formatoin
  -- TODO: Should be less of a headache to prove this!
  -- IsBase is a boolean after all
  simp [inFragment, IsBase, FormL.Context.subst]
  apply And.intro
  . apply baseApplDual
    simp [IsBase]
    apply And.intro
    . exact φ.2
    . exact ψ.2
  . apply And.intro
    . exact baseApplDual φ.2
    . exact baseApplDual ψ.2

def ax_t : S5Pf (□ φ ⟶ φ) := by
  apply Proof.fragment.mk (.ax ⟨_, by simp [S5]; exists (□ φ ⟶ φ); exact And.intro ⟨.AxT⟩ rfl⟩)
  simp [inFragment, Modal.imp]
  exact And.intro modalIsBase modalIsBase

def ax_a5 : S5Pf (◇ φ ⟶ □◇φ) := by
  apply Proof.fragment.mk (.ax ⟨_, by simp [S5]; exists (◇ φ ⟶ □◇φ); exact And.intro ⟨.Ax5⟩ rfl⟩)
  simp [inFragment, Modal.imp]
  exact And.intro modalIsBase modalIsBase

def modusPonens (maj : S5Pf (φ ⟶ ψ)) (min : S5Pf φ) : S5Pf ψ := mp_frag maj min modalIsBase

def necessitation (pf : S5Pf φ) : S5Pf (□ φ) := by
  let l1 : Proof _ _ (φ.boxLL).1 := ug .refl pf.pf
  rw [Modal.boxIsLL]
  apply Proof.fragment.mk l1
  simp [l1, inFragment, pf.inFrag]
  apply modalIsBase
