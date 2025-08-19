import Hybrid.Completeness.Lindenbaum.Expansion.Helpers

variable {α β : Type u}
variable {S₁ : Symbols α}
variable {s : S₁.signature.S}
variable {Λ : AxiomSet S₁}
variable {S₂ : Symbols β}
variable {m : S₁ ↪ S₂}

open Completeness

lemma SatFormLift {φ : Form S₁ s} {M : Model S₁} {g : Assignment M} {w : M.Fr.W s} :
  (⟨M, g, w⟩ ⊨ φ) ↔ ⟨m+ M, m+ g, m.m.morph_world w⟩ ⊨ (m+ φ) := by
  sorry

lemma ClassLift {M : Model S₁} : (m+ M) ∈ (m+ Λ).Models ↔ M ∈ Λ.Models := sorry

lemma SatLift {Γ : PremiseSet S₁ s} :
  (m+ Γ).satisfiable (m+ Λ).Models ↔ Γ.satisfiable Λ.Models := by
  apply Iff.intro
  . intro ⟨M_plus, ⟨g_plus, ⟨w_plus, h⟩⟩⟩
    admit
  . intro ⟨M, ⟨g, ⟨w, h⟩⟩⟩
    exists ⟨m+ M, ClassLift.mpr M.2⟩
    exists (m+ g)
    exists (m.m.morph_world w)
    intro φ_plus
    let φ := φ_plus.2.choose
    let mem := φ_plus.2.choose_spec.1
    have := φ_plus.2.choose_spec.2
    have eq : φ = φ_plus.2.choose := rfl
    rw [←eq] at this
    have : φ_plus.1 = (m+ φ) := by rw [←this]
    rw [this]
    simp [Symbols.embedding.morph_formula]
    rw [←SatFormLift]
    exact h ⟨φ, mem⟩

lemma ProvableLift [DecidableEq α] [DecidableEq β] {φ : Form S₁ s} :
  ⊢(m+ Λ, m+ s) (m+ φ) ↔ ⊢(Λ, s) φ := by

    admit

lemma AxiomConsistentLift [DecidableEq α] [DecidableEq β]:
  (m+ Λ).consistent ↔ Λ.consistent := by

    admit

lemma ConsistentLift [DecidableEq α] [DecidableEq β] {Γ : PremiseSet S₁ s} :
  (m+ Γ).consistent (m+ Λ) ↔ Γ.consistent Λ := by

    admit
