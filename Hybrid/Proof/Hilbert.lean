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
  | ref j s₂ : Proof Λ s₂ (ℋ@j (ℋNom j))
  -- 2. Axioms about svars and binders
  | q1 x φ ψ
        (_: φ.occurs_free x = false):
      Proof Λ s (ℋ∀x (φ ⟶ ψ) ⟶ (φ ⟶ ℋ∀x ψ))
  | q2_var (x y: symbs.svarType s') φ:
      φ.free_for y x → Proof Λ s ((ℋ∀x φ) ⟶ φ[y // x])
  | q2_nom (i : symbs.nominal s') (x: symbs.svarType s') φ:
      Proof Λ s ((ℋ∀x φ) ⟶ φ[i // x])
  | name x : Proof Λ s (ℋ∃x (ℋVar x))
  -- 3. Barcan axioms
  | barcan x (φ : Form symbs s)
      (σ : symbs.signature.Sig _ s)
      (C : φ.Context ψ)
      (h : C.all_else_not_free x):
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
            Λ.occurs j = false → φ.occurs j = false →
            Proof Λ s₁ (ℋ@j φ) → Proof Λ s₂ φ
  | paste (C : (ℋNom k).Context χ):
          k ≠ₛ j → Λ.occurs k = false → φ.occurs k = false → ψ.occurs k = false → χ.occurs k = false →
          Proof Λ s (ℋ@j (ℋ⟨σ⟩ χ) ⋀ ℋ@k φ ⟶ ψ) → Proof Λ s ((ℋ@j (ℋ⟨σ⟩ C[φ]) ⟶ ψ))
  | gen x : Proof Λ s φ → Proof Λ s (ℋ∀x φ)

def Provable {symbs : Symbols α} (Λ : AxiomSet symbs) (s : symbs.signature.S) (φ : Form symbs s) : Prop := Nonempty (Proof Λ s φ)

notation:25 "⊢" "(" Λ:25 ", " s:26")" φ:75  => Provable Λ s φ

-- The local consequence relation
def SyntacticConsequence {symbs : Symbols α} {s : symbs.signature.S} (Γ : PremiseSet symbs s) (Λ : AxiomSet symbs) (φ : Form symbs s): Prop :=
    ∃ ch : FiniteChoice Γ, ⊢(Λ, s) (ch.conjunction ⟶ φ)

notation:25 Γ:arg "⊢" "(" Λ:25 ")" φ:75 => SyntacticConsequence Γ Λ φ

omit [DecidableEq α] in
def AxiomSet.consistent {symbs : Symbols α} (Λ : AxiomSet symbs) := ∀ s : symbs.signature.S, ¬ (⊢(Λ, s) ℋ⊥)

-- IMPORTANT!
--  If we don't add the Λ.consistent assumption to this definition,
--  then we may be able to derive a contradiction on a sort s' ≠ s!
def PremiseSet.consistent {symbs : Symbols α} {s : symbs.signature.S} {Γ : PremiseSet symbs s} (Λ : AxiomSet symbs) := Λ.consistent ∧ ¬(Γ ⊢(Λ) ℋ⊥)
