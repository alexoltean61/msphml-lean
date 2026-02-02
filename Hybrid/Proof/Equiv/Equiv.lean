import Hybrid.Proof.Proofs

namespace Proof

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s : symbs.signature.S}
variable {φ ψ : Form symbs s}
variable {Λ : AxiomSet symbs}

def impNeg (imp : Proof Λ _ (ψ ⟶ φ)) : Proof Λ _ (∼φ ⟶ ∼ψ) := by
  have l1 := Proof.mp .contraposition imp
  exact l1

def impImplL  (h : Proof Λ _ (φ ⟶ ψ)): Proof Λ _ ((χ ⟶ φ) ⟶ (χ ⟶ ψ)) := by
  have l1 := Proof.mp (.prop1 _ χ) h
  have l2 := Proof.mp (.prop2 _ _ _) l1
  exact l2

def impDualAppl
               (C : φ.Context args)
               (imp : Proof Λ s (φ ⟶ ψ))
            : Proof Λ rng ((ℋ⟨σ⟩ᵈ args) ⟶ (ℋ⟨σ⟩ᵈ C[ψ])) := by
    let χ := C[φ ⟶ ψ]
    let C' : (φ ⟶ ψ).Context χ := (φ ⟶ ψ).subst_to_ctx C
    have l1 : Proof Λ rng (ℋ⟨σ⟩ᵈ χ) := .ug C' imp
    have l2 : Proof Λ rng (ℋ⟨σ⟩ᵈ C'[φ] ⟶ ℋ⟨σ⟩ᵈ C'[ψ])
      := .mp (.k _ _ _ _ C') l1
    have isIso : C'.iso C := FormL.subst_to_ctx_iso C
    have := FormL.Context.subst_in_iso isIso
    rw [this] at l2 ; clear this
    rw [←FormL.Context.subst_in_iso_helper isIso]
    exact l2

-- From this point in the file
-- we will make the assumption that we have a proof
-- of φ ←→ ψ:
variable (iffAssumption : Proof Λ s (φ ←→ ψ))

def simpNeg : Proof Λ _ (∼φ ←→ ∼ψ) := by
  apply Proof.mp (Proof.mp .conj_intro_proof _) _
  . apply impNeg
    exact .mp .conj_elimR_proof iffAssumption
  . apply impNeg
    exact .mp .conj_elimL_proof iffAssumption

def simpImplL : Proof Λ _ ((χ ⟶ φ) ←→ (χ ⟶ ψ)) := by
    have := iffAssumption
    apply Proof.mp (Proof.mp .conj_intro_proof _) _
    . apply impImplL
      exact .mp .conj_elimL_proof iffAssumption
    . apply impImplL
      exact .mp .conj_elimR_proof iffAssumption

def simpDualAppl
               (C : φ.Context args)
            : Proof Λ _ ((ℋ⟨σ⟩ᵈ args) ←→ (ℋ⟨σ⟩ᵈ C[ψ])) := by
    apply Proof.mp (Proof.mp .conj_intro_proof _) _
    . apply impDualAppl
      exact .mp .conj_elimL_proof iffAssumption
    . -- This reduces to the other case by taking
      -- C[ψ] as primitive (χ), and writing args in terms
      -- of χ:
      ----------
      let χ := C[ψ] ; have : C[ψ] = χ := rfl
      rw [this] ; clear this
      let C' : ψ.Context χ := ψ.subst_to_ctx C
      have : args = C'[φ] := C.subst_back
      rw [this] ; clear this
      ----------
      apply impDualAppl
      exact .mp .conj_elimR_proof iffAssumption
