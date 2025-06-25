import Hybrid.Language
import Hybrid.Language.Substitution

variable {α : Type u}
variable [DecidableEq α]

inductive Proof {symbs : Symbols α} (Λ : AxiomSet symbs) : (s : symbs.signature.S) → Form symbs s → Type u
  -- Λ:
  | ax    : (φ : Λ s) → Proof Λ s φ
  -- K:
  | prop1 φ ψ   : Proof Λ s (φ ⟶ (ψ ⟶ φ))
  | prop2 φ ψ χ : Proof Λ s ((φ ⟶ (ψ ⟶ χ)) ⟶ (φ ⟶ ψ) ⟶ (φ ⟶ χ))
  | prop3 φ ψ   : Proof Λ s ((∼ψ ⟶ ∼φ) ⟶ (φ ⟶ ψ))
  | k φ ψ χ
      (σ : symbs.signature.Sig _ s)
      (C : (φ ⟶ ψ).Context χ):
            Proof Λ s (ℋ⟨σ⟩ᵈ χ ⟶ (ℋ⟨σ⟩ᵈ C[φ] ⟶ ℋ⟨σ⟩ᵈ C[ψ]))
  | mp    : Proof Λ s (φ ⟶ ψ) → Proof Λ s φ → Proof Λ s ψ
  | ug {φ : Form symbs s₁}
       (C : φ.Context ψ):
            Proof Λ s₁ φ → Proof Λ s₂ (ℋ⟨σ⟩ᵈ ψ)
  -- H(@, ∀):
  -- 1. Axioms about @
  | kAt j φ ψ    : Proof Λ s (ℋ@j (φ ⟶ ψ) ⟶ (ℋ@j φ ⟶ ℋ@j ψ))
  | agree j k φ  : Proof Λ s (ℋ@k (ℋ@j φ) ←→ ℋ@j φ)
  | selfDual j φ : Proof Λ s (ℋ@j φ ←→ ∼ ℋ@j (∼φ))
  | intro j φ    : Proof Λ s (ℋNom j ⟶ (φ ←→ ℋ@j φ))
  | back j φ ψ
         (σ : symbs.signature.Sig _ s)
         (C : (@FormL.at α symbs t sᵢ j ψ).Context φ):
      Proof Λ s (ℋ⟨σ⟩ φ ⟶ ℋ@j ψ)
  -- 2. Axioms about svars and binders
  | q1 x φ ψ
        (_: φ.varOccursFree x = false):
      Proof Λ s (ℋ∀x (φ ⟶ ψ) ⟶ (φ ⟶ ℋ∀x ψ))
  | q2 (x y: symbs.svarType s') φ:
      φ.varSubstableFor y x → Proof Λ s ((ℋ∀x φ) ⟶ φ[y // x])
  | name x : Proof Λ s (ℋ∃x (ℋVar x))
  -- 3. Barcan axioms
  | barcan x (φ ψ : Form symbs s)
      (σ : symbs.signature.Sig _ s)
      (C : φ.Context ψ):
            Proof Λ s (ℋ∀x (ℋ⟨σ⟩ᵈ ψ) ⟶ (ℋ⟨σ⟩ᵈ C[ℋ∀x φ]))
  | barcanAt x j φ:
            Proof Λ s (ℋ∀x (ℋ@j φ) ⟶ ℋ@j (ℋ∀x φ))
  -- 4. Axiom Nom, linking svars and nominals together:
  | nom x j k:
            Proof Λ s (ℋ@k (ℋVar x) ⋀ ℋ@j (ℋVar x) ⟶ ℋ@k (ℋNom j))
  -- Hybrid proof rules
  | broadcastS s₂ : Proof Λ s₁ (ℋ@j φ) → Proof Λ s₂ (ℋ@j φ)
  | genAt s₂ j : Proof Λ s₁ φ → Proof Λ s₂ (ℋ@j φ)
  | nameAt s₂ {j : symbs.nominal s₂} {φ : Form symbs s₂} :
            (φ.occurs j = false) → Proof Λ s₁ (ℋ@j φ) → Proof Λ s₂ φ
  | paste (C : (ℋNom k).Context χ):
        k ≠ j → φ.occurs k = false → ψ.occurs k = false →
          Proof Λ s (ℋ@j (ℋ⟨σ⟩ χ) ⋀ ℋ@k φ ⟶ ψ) → Proof Λ s (ℋ@j (ℋ⟨σ⟩ C[φ]) ⟶ ψ)
  | gen x : Proof Λ s φ → Proof Λ s (ℋ∀x φ)

notation:25 "⊢" "(" Λ:25 ", " s:26")" φ:arg => Proof Λ s φ

-- The local consequence relation
def SyntacticConsequence {symbs : Symbols α} {s : symbs.signature.S} (Γ : PremiseSet symbs s) (Λ : AxiomSet symbs) (φ : Form symbs s): Type u :=
    Σ ch : FiniteChoice Γ, ⊢(Λ, s) (ch.conjunction ⟶ φ)

notation:25 Γ:arg "⊢" "(" Λ:25 ")" φ:arg => SyntacticConsequence Γ Λ φ
