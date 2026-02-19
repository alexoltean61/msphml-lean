import Hybrid.Proof.Tautologies

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

def impAppl
               (C : φ.Context args)
               (imp : Proof Λ s (φ ⟶ ψ))
            : Proof Λ _ ((ℋ⟨σ⟩ args) ⟶ (ℋ⟨σ⟩ C[ψ])) := by
    apply imp_trans_proof
    . apply mp conj_elimL_proof dual
    . apply imp_trans_proof _ (mp conj_elimR_proof dual)
      apply mp contraposition
      let ⟨χ, C', eq, iso', substNegAll⟩ := C.to_negAll
      rw [substNegAll]
      subst eq
      have l1 := mp contraposition imp
      have l2 := @impDualAppl _ _ _ _ _ _ _ _ _ _ _ σ ((∼ψ).subst_to_ctx C') l1
      have : args.negAll = ((∼ψ).subst_to_ctx C')[∼φ] := FormL.Context.subst_back _
      rw [←this] at l2
      exact l2

def impAt {k : symbs.nominal s} (imp : Proof Λ s (φ ⟶ ψ)):
      Proof Λ t (ℋ@ k φ ⟶ ℋ@ k ψ) := by
    apply mp (kAt _ _ _)
    apply genAt
    exact imp

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

def simpAppl
               (C : φ.Context args)
            : Proof Λ _ ((ℋ⟨σ⟩ args) ←→ (ℋ⟨σ⟩ C[ψ])) := by
    apply Proof.mp (Proof.mp .conj_intro_proof _) _
    . apply impAppl
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
      apply impAppl
      exact .mp .conj_elimR_proof iffAssumption

def simpAt {k : symbs.nominal s}:
      Proof Λ t (ℋ@ k φ ←→ ℋ@ k ψ) := by
    apply Proof.mp (Proof.mp .conj_intro_proof _) _
    . apply mp (kAt _ _ _)
      apply genAt
      exact .mp .conj_elimL_proof iffAssumption
    . apply mp (kAt _ _ _)
      apply genAt
      exact .mp .conj_elimR_proof iffAssumption
