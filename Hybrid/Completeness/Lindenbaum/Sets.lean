import Hybrid.Proof

namespace Completeness

open Completeness

section Basic
  variable {α : Type u}
  variable [DecidableEq α]
  variable {symbs : Symbols α}
  variable {s : symbs.signature.S}
  variable {Γ : PremiseSet symbs s}

  /--
    `Γₛ` is maximal consistent if it is consistent, and any `Γ'ₛ` that properly extends it
      is inconsistent.
  -/
  def PremiseSet.maximal_consistent (Λ : AxiomSet symbs) := Γ.consistent Λ ∧ ∀ Γ', Γ ⊂ Γ' → ¬ Γ'.consistent Λ

  /--
    `Γₛ` is named if one of its elements is a nominal or a constant nominal.
  -/
  def PremiseSet.named := ∃ i : symbs.nominal s, ℋNom i ∈ Γ

  /--
    `Γₛ` is pasted iff
      if `@k σ(φ₁, ... φ, ..., φₙ) ∈ Γₛ`, then
      there exists `j` s.t.
        `@k σ(φ₁, ... j, ..., φₙ) ∈ Γₛ` and
        `@j φ ∈ Γₛ`.
  -/
  def PremiseSet.pasted := ∀ {s₁ ss sᵢ} {σ : symbs.signature.Sig (s₁ :: ss) s} {k : symbs.nominal s} {χ : FormL symbs (s₁ :: ss)} {φ : Form symbs sᵢ} (C : φ.Context χ),
    ℋ@k (ℋ⟨σ⟩ χ) ∈ Γ → ∃ j : symbs.nominal sᵢ, ℋ@k (ℋ⟨σ⟩ C[j]) ∈ Γ ∧ ℋ@j φ ∈ Γ

  /--
    `Γₛ` is @-witnessed
  -/
  def PremiseSet.at_witnessed := ∀ {s' t} {φ : Form symbs s'} {k : symbs.nominal s'} {x : symbs.svar t},
    (ℋ@k (ℋ∃ x φ) ∈ Γ → ∃ j : symbs.nominal t, ℋ@k φ[j // x] ∈ Γ) ∧
    (∃ jₓ : symbs.nominal t, ℋ@jₓ x ∈ Γ)

  section Lemmas
    lemma gen_at_closed (h : Γ.maximal_consistent Λ) (φ : ↑Γ) (j : symbs.nominal s) : ℋ@j φ ∈ Γ := sorry
  end Lemmas

end Basic

structure NamedPastedWitnessedMCS {α : Type u} [DecidableEq α] (S : Symbols α) (t : S.signature.S) (Λ : AxiomSet S) where
    set : PremiseSet S t
    named  : set.named
    pasted : set.pasted
    witnessed : set.at_witnessed
    mcs : set.maximal_consistent Λ

end Completeness
