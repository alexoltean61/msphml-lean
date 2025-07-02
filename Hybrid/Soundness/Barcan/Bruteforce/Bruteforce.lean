import Hybrid.Soundness.Barcan.Countermodel

theorem Barcan1Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∀ x φ]) := sorry
theorem Barcan1Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∀ x φ]) := sorry

theorem Barcan2Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∀ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ ψ)) := sorry
theorem Barcan2Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∀ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ ψ)) := sorry

theorem Barcan3Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∀ x φ]) := sorry
theorem Barcan3Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∀ x φ]) := sorry

theorem Barcan4Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∀ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ ψ)) := sorry
theorem Barcan4Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∀ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ ψ)) := sorry

theorem Barcan5Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∃ x φ]) := sorry
theorem Barcan5Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∃ x φ]) := sorry

theorem Barcan6Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∃ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ ψ)) := sorry
theorem Barcan6Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∃ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ ψ)) := sorry

theorem Barcan7Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∃ x φ]) := sorry
theorem Barcan7Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∃ x φ]) := sorry

theorem Barcan8Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∃ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ ψ)) := sorry
theorem Barcan8Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∃ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ ψ)) := sorry

theorem Barcan9Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∀ x φ]) := sorry
theorem Barcan9Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∀ x φ]) := sorry

theorem Barcan10Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∀ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ᵈ ψ)) := sorry
theorem Barcan10Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∀ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ᵈ ψ)) := sorry

namespace B11_12

theorem Barcan11Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∀ x φ]) := by
  exists String
  exists symbs
  exists sortS
  exists sortS
  exists sortS
  exists sortS
  exists [sortS]
  exists (ℋ@ j (.svar x), ℋ@ k (.svar x))
  exists ℋ@ j (.svar x)
  exists x
  exists FormL.Context.head
  exists sig
  exists (λ _ => { })
  simp only [Models.AxValid, FormL.validClass, Models.Ax, Set.coe_setOf, Set.mem_setOf_eq,
    Subtype.forall, Set.mem_empty_iff_false, false_implies, implies_true, true_implies, not_forall, FormL.Context.subst]
  exists countermodel
  simp only [Model.valid, not_forall]
  exists g
  exists w₀
  simp only [Sat.implies, Classical.not_imp]
  apply And.intro
  . exact BarcanAntecedentTrue
  . exact BarcanConsequentFalse

theorem Barcan12Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∀ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ᵈ ψ)) := by
  exists String
  exists symbs
  exists sortS
  exists sortS
  exists sortS
  exists sortS
  exists [sortS]
  exists (.svar x, ℋ@j (.svar x))
  exists (.svar x)
  exists x
  exists FormL.Context.head
  exists sig
  exists (λ _ => { })
  simp only [Models.AxValid, FormL.validClass, Models.Ax, Set.coe_setOf, Set.mem_setOf_eq,
    Subtype.forall, Set.mem_empty_iff_false, false_implies, implies_true, true_implies, not_forall, FormL.Context.subst]
  exists countermodel
  simp only [Model.valid, not_forall]
  exists g
  exists w₀
  simp only [Sat.implies, Classical.not_imp]
  apply And.intro
  . exact BarcanConverseAntecedentTrue
  . exact BarcanConverseConsequentFalse

end B11_12

theorem Barcan13Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∃ x φ]) := sorry
theorem Barcan13Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∃ x φ]) := sorry

theorem Barcan14Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∃ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ᵈ ψ)) := sorry
theorem Barcan14Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∃ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ᵈ ψ)) := sorry

theorem Barcan15Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∃ x φ]) := sorry
theorem Barcan15Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∀ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∃ x φ]) := sorry

theorem Barcan16Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∃ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ᵈ ψ)) := sorry
theorem Barcan16Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∃ x φ] ⟶ ℋ∀ x (ℋ⟨σ⟩ᵈ ψ)) := sorry

theorem Barcan17Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∀ x φ]) := sorry
theorem Barcan17Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∀ x φ]) := sorry

theorem Barcan18Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∀ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ ψ)) := sorry
theorem Barcan18Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∀ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ ψ)) := sorry

theorem Barcan19Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∀ x φ]) := sorry
theorem Barcan19Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∀ x φ]) := sorry

theorem Barcan20Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∀ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ ψ)) := sorry
theorem Barcan20Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∀ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ ψ)) := sorry

theorem Barcan21Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∃ x φ]) := sorry
theorem Barcan21Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∃ x φ]) := sorry

namespace B11_12

-- Barcan11 can be obtained from the contrapositive of Barcan22, so 22 should be provably unsound
theorem Barcan22Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∃ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ ψ)) :=  by

    /-
      ⟨M, g, w₀⟩ ⊨ σ (∃ x ∼ (@ⱼ x), ∼ @ₖ x) ⟶ ∃ x σ(∼ @ⱼ x, ∼ @ₖ x)               iff    (DNI)

      ⟨M, g, w₀⟩ ⊨ ∼ ∼ σ (∃ x ∼ (@ⱼ x), ∼ @ₖ x) ⟶ ∼ ∼ ∃ x σ(∼ @ⱼ x, ∼ @ₖ x)       iff (Contrap)

      ⟨M, g, w₀⟩ ⊨ ∼ ∃ x σ(∼ @ⱼ x, ∼ @ₖ x) ⟶ ∼ σ (∃ x ∼ (@ⱼ x), ∼ @ₖ x)           iff (∃ definition)

      ⟨M, g, w₀⟩ ⊨ ∼ ∼ ∀ x ∼ σ(∼ @ⱼ x, ∼ @ₖ x) ⟶ ∼ σ (∼ ∀ x ∼ ∼ (@ⱼ x), ∼ @ₖ x)   iff (DNE)

      ⟨M, g, w₀⟩ ⊨ ∀ x ∼ σ(∼ @ⱼ x, ∼ @ₖ x) ⟶ ∼ σ (∼ ∀ x ∼ ∼ (@ⱼ x), ∼ @ₖ x)       iff (σᵈ definition)

      ⟨M, g, w₀⟩ ⊨ ∀ x σᵈ ( @ⱼ x,  @ₖ x) ⟶ σᵈ (∀ x ∼ ∼ (@ⱼ x), @ₖ x)              iff (DNE inside ∀ x)

      ⟨M, g, w₀⟩ ⊨ ∀ x σᵈ ( @ⱼ x,  @ₖ x) ⟶ σᵈ (∀ x (@ⱼ x), @ₖ x)

      But we proved already that ⟨M, g, w₀⟩ ⊭ ∀ x σᵈ(@ⱼ x, @ₖ x) → σᵈ(∀ x (@ⱼ x), @ₖ x)!
    -/

  by_contra h
  simp only [not_exists] at h
  specialize h String symbs sortS sortS sortS sortS
  specialize h [sortS]
  specialize h (∼ ℋ@ j (.svar x), ∼ ℋ@ k (.svar x))
  specialize h (∼ ℋ@ j (.svar x)) x .head sig
  specialize h (λ _ => { })
  simp only [Classical.not_not] at h
  specialize h ⟨countermodel, by simp [Models.Ax]⟩ g w₀
  simp only [FormL.Context.subst, Sat.implies] at h
  rw [←not_imp_not, ←FormL.negAll] at h -- contrapose
  admit

-- Barcan12 can be obtained from the contrapositive of Barcan23, so 23 should be provably unsound
theorem Barcan23Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∃ x φ]) := sorry

end B11_12

theorem Barcan24Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∃ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ ψ)) := sorry
theorem Barcan24Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∃ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ ψ)) := sorry

theorem Barcan25Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∀ x φ]) := sorry
theorem Barcan25Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∀ x φ]) := sorry

theorem Barcan26Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∀ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ᵈ ψ)) := sorry
theorem Barcan26Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∀ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ᵈ ψ)) := sorry

theorem Barcan27Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∀ x φ]) := sorry
theorem Barcan27Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∀ x φ]) := sorry

theorem Barcan28Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∀ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ᵈ ψ)) := sorry
theorem Barcan28Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∀ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ᵈ ψ)) := sorry

theorem Barcan29Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∃ x φ]) := sorry
theorem Barcan29Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ C[ℋ∃ x φ]) := sorry

theorem Barcan30Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∃ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ᵈ ψ)) := sorry
theorem Barcan30Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ C[ℋ∃ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ᵈ ψ)) := sorry

theorem Barcan31Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∃ x φ]) := sorry
theorem Barcan31Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ∃ x (ℋ⟨σ⟩ᵈ ψ) ⟶ ℋ⟨σ⟩ᵈ C[ℋ∃ x φ]) := sorry

theorem Barcan32Sound {Λ : AxiomSet symbs} (φ : Form symbs s) (ψ : FormL symbs (s₁ :: t)) (σ : symbs.signature.Sig _ s) (C : φ.Context ψ) :
 ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∃ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ᵈ ψ)) := sorry
theorem Barcan32Unsound : ∃ (α : Type 0) (symbs : Symbols α) (sₕ s s' s'' : symbs.signature.S) (sₜ : List symbs.signature.S) (ψ: FormL symbs (sₕ :: sₜ)) (φ : Form symbs s) (x : symbs.svar s') (C : φ.Context ψ) (σ : symbs.signature.Sig (sₕ :: sₜ) s'') (Λ : AxiomSet symbs),
 ¬ ⊨Mod(Λ) (ℋ⟨σ⟩ᵈ C[ℋ∃ x φ] ⟶ ℋ∃ x (ℋ⟨σ⟩ᵈ ψ)) := sorry
