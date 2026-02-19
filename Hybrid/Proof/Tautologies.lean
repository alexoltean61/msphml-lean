import Hybrid.Proof.Hilbert

namespace Proof

variable {α : Type u}
variable {symbs : Symbols α}
variable {Λ : AxiomSet symbs}

@[simp, grind]
lemma tautOr {φ : Form symbs s} : ∀ e [Morphism e], e (φ ⋁ ψ) ↔ e φ ∨ e ψ := by
  intro _ m
  simp [m.m_or]
@[simp, grind]
lemma tautNeg {φ : Form symbs s} : ∀ e [Morphism e], e (∼φ) ↔ ¬e φ := by
  intro _ m
  simp [m.m_neg]
@[simp, grind]
lemma tautImp {φ : Form symbs s} : ∀ e [Morphism e], e (φ ⟶ ψ) ↔ ¬e φ ∨ e ψ := by
  intro e m
  unfold FormL.implies
  grind
@[simp, grind]
lemma tautAnd {φ : Form symbs s} : ∀ e [Morphism e], e (φ ⋀ ψ) ↔ e φ ∧ e ψ := by
  intro _ m
  unfold FormL.and
  grind
@[simp]
lemma tautTop  : ∀ {e : Eval symbs s} [Morphism e], e (@FormL.top _ _ s) := by
  unfold FormL.top
  grind
@[simp]
lemma tautBot  : ∀ {e : Eval symbs s} [Morphism e], e (@FormL.bot _ _ s) ↔ ⊥ := by
  unfold FormL.bot
  conv =>
    intro e m
    simp [@tautNeg _ _ _ _ e m, @tautTop _ _ _ e m]
  intros
  simp only
@[simp]
lemma tautExclMiddle : ∀ {e : Eval symbs s} [Morphism e], ¬e φ ∨ e φ := by
  intro e m
  grind

-- All syntactic proofs that depend on excluded middle will be classical
-- In the future, we shall move to fully syntactic embedding of propositional logic
-- (Lukasiewicz axioms instead of morphisms)

variable [DecidableEq α]

def prop1 φ ψ : (Proof Λ s (φ ⟶ ψ ⟶ φ)) := by
  apply taut
  intro e m
  grind

def prop2 φ ψ χ : (Proof Λ s ((φ ⟶ (ψ ⟶ χ)) ⟶ (φ ⟶ ψ) ⟶ (φ ⟶ χ))) := by
  apply taut
  intro e m
  grind

def prop3 φ ψ : (Proof Λ s ((∼ψ ⟶ ∼φ) ⟶ (φ ⟶ ψ))) := by
  apply taut
  intro e m
  grind

def dni : (Proof Λ s (φ ⟶ ∼∼φ)) := by
  apply taut
  intro e m
  grind

def dni' : (Proof Λ s (φ ⟶ ∼φ ⟶ ℋ⊥)) := by
  apply taut
  intro e m
  grind

def top_proof : Proof Λ s (ℋ⊤) := by
  apply taut
  intro _ _
  simp

def id_proof : Proof Λ s (φ ⟶ φ) := by
  apply taut
  intro e m
  grind

def export_theorem_proof : Proof Λ s ((φ ⋀ ψ ⟶ χ) ⟶ (φ ⟶ ψ ⟶ χ)) := by
  -- Theorem pm3.3 in Metamath
  apply taut
  intro e m
  grind

def export_proof : Proof Λ s (φ ⋀ ψ ⟶ χ) → Proof Λ s (φ ⟶ ψ ⟶ χ) :=
  λ l1 => mp export_theorem_proof l1

def import_theorem_proof : Proof Λ s ((φ ⟶ ψ ⟶ χ) ⟶ (φ ⋀ ψ ⟶ χ)) := by
  apply taut
  intro e m
  grind

def import_proof : Proof Λ s (φ ⟶ ψ ⟶ χ) → Proof Λ s (φ ⋀ ψ ⟶ χ) :=
  λ l1 => mp import_theorem_proof l1

def exfalso : Proof Λ s (ℋ⊥ ⟶ φ) := by
  apply taut
  intro e m
  simp

def tertium_non_datur_proof : Proof Λ s (φ ⋁ ∼φ) := by
  apply taut
  intro e m
  grind

def conj_intro_proof : Proof Λ s (φ ⟶ ψ ⟶ (φ ⋀ ψ)) := by
  apply taut
  intro e m
  grind

def conj_intro_hyp_proof : Proof Λ s ((φ ⟶ ψ) ⟶ (φ ⟶ χ) ⟶ (φ ⟶ ψ ⋀ χ)) := by
  apply taut
  intro e m
  grind

def conj_intro_hyp (h1 : Proof Λ s (φ ⟶ ψ))
            (h2 : Proof Λ s (φ ⟶ χ)):
      Proof Λ s (φ ⟶ ψ ⋀ χ) := mp (mp conj_intro_hyp_proof h1) h2

def conj_elimL_proof : Proof Λ s ((φ ⋀ ψ) ⟶ φ) := by
  apply taut
  intro e m
  grind

def conj_elimR_proof : Proof Λ s ((φ ⋀ ψ) ⟶ ψ) := by
  apply taut
  intro e m
  grind

def disj_elim_proof : Proof Λ s ((φ ⋁ ψ) ⟶ (φ ⟶ χ) ⟶ (ψ ⟶ χ) ⟶ χ) := by
  apply taut
  intro e m
  grind

def disj_elim_not : Proof Λ s (φ ⋁ ψ ⟶ ∼ φ ⟶ ψ) := by
  apply taut
  intro e m
  grind

def contraposition : Proof Λ s ((ψ ⟶ φ) ⟶ (∼φ ⟶ ∼ψ)) := by
  apply taut
  intro e m
  grind

def contraposition' : Proof Λ s ((ψ ⟶ ∼φ) ⟶ (φ ⟶ ∼ψ)) := by
  apply taut
  intro e m
  grind

def contraposition'' : Proof Λ s ((∼ψ ⟶ φ) ⟶ (∼φ ⟶ ψ)) := by
  apply taut
  intro e m
  grind

def impAsDisj : Proof Λ s ((∼φ ⟶ ψ) ⟶ (φ ⋁ ψ)) := by
  apply taut
  intro e m
  grind

def imp_trans_theorem_proof : Proof Λ s ((φ ⟶ ψ) ⟶ (ψ ⟶ χ) ⟶ (φ ⟶ χ)) := by
  apply taut
  intro e m
  grind

def imp_trans_proof : Proof Λ s (φ ⟶ ψ) → Proof Λ s (ψ ⟶ χ) → Proof Λ s (φ ⟶ χ) :=
  λ l1 l2 => mp (mp imp_trans_theorem_proof l1) l2

def imp_com_theorem_proof : Proof Λ s ((φ ⟶ ψ ⟶ χ) ⟶ (ψ ⟶ φ ⟶ χ)) := by
  apply taut
  intro e m
  grind

def imp_com_proof : Proof Λ s (φ ⟶ ψ ⟶ χ) → Proof Λ s (ψ ⟶ φ ⟶ χ) :=
  λ l1 => mp imp_com_theorem_proof l1

def helperInsertAndR_theorem_proof : Proof Λ s ((φ ⟶ ψ) ⟶ (φ ⟶ χ) ⟶ (φ ⟶ ψ ⋀ χ)) := by
  apply taut
  intro e m
  grind

def helperInsertAndR : Proof Λ s (φ ⟶ ψ) → Proof Λ s (φ ⟶ χ) → Proof Λ s (φ ⟶ ψ ⋀ χ) :=
  λ l1 l2 => mp (mp helperInsertAndR_theorem_proof l1) l2

def helperInsertAndL_theorem_proof : Proof Λ s ((φ ⟶ χ) ⟶ (φ ⋀ ψ ⟶ χ)) := by
  apply taut
  intro e m
  grind

def helperInsertAndL : Proof Λ s (φ ⟶ χ) → Proof Λ s (φ ⋀ ψ ⟶ χ) :=
  λ l1 => mp helperInsertAndL_theorem_proof l1
