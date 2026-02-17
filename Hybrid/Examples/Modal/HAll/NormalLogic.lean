import Hybrid.Examples.Modal.HAll.HAll

inductive NormalSchema : HAll → Type where
  -- Axiom Nom needs to be added as its own schema, even though Nom
  -- is an axiom in the underlying proof system.
  -- That's because Nom is introduced using the @ operator in the proof system,
  -- which we lack in this fragment.
  | AxNom : NormalSchema ((∀ x . ◇^n (x ⋀ φ) ~> □^m (x ~> φ)))

def NormalL : AxiomSet ModalBase :=
  λ _ => setOf ( λ form => ∃ (φ : HAll) (_ : NormalSchema φ), φ.toForm ≍ form )

def PfHAll (φ : HAll) := Proof.fragment IsHAll NormalL φ.1

namespace PfHAll
open Proof

def ax_k : PfHAll (□ (φ ⟶ ψ) ⟶ □ φ ⟶ □ ψ) := by
  simp only [HAll.boxIsLL]
  apply Proof.fragment.mk (k _ _ (φ.toForm ⟶ ψ.toForm) ModalBase.poss .refl)
  simp [inFragment, IsHAll, FormL.Context.subst]
  apply And.intro
  . apply hallApplDual
    simp [IsHAll]
    apply And.intro
    . exact φ.2
    . exact ψ.2
  . apply And.intro
    . exact hallApplDual φ.2
    . exact hallApplDual ψ.2

def ax_nom : PfHAll (∀ x . ◇^n (x ⋀ φ) ~> □^m (x ~> φ)) := by
  apply Proof.fragment.mk (.ax ⟨_, by simp [NormalL]; exists (∀ x . ◇^n (x ⋀ φ) ~> □^m (x ~> φ)); exact And.intro ⟨.AxNom⟩ rfl⟩)
  simp [inFragment]
  apply hallIsHAll

def modusPonens (maj : PfHAll (φ ⟶ ψ)) (min : PfHAll φ) : PfHAll ψ :=
  mp_frag maj min hallIsHAll

def necessitation (pf : PfHAll φ) : PfHAll (□ φ) := by
  let l1 : Proof _ _ (φ.boxLL).1 := ug .refl pf.pf
  rw [HAll.boxIsLL]
  apply Proof.fragment.mk l1
  simp [l1, inFragment, pf.inFrag]
  apply hallIsHAll

def generalization (pf : PfHAll φ) : PfHAll (∀ x . φ) := by
  let l1 := gen x pf.pf
  apply Proof.fragment.mk l1
  simp [l1, inFragment, pf.inFrag]
  apply hallIsHAll
