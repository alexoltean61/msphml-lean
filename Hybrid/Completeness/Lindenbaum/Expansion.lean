import Hybrid.Proof
import Hybrid.Semantics

namespace Completeness

open Completeness

variable {α : Type u}
variable [DecidableEq α]

/--
  TODO SECTION:
    Signature / Symbols extensions and embeddings.
    Properties preserved by embeddings.
-/
structure Symbols.morphism (S₁ : Symbols α) (S₂ : Symbols β) : Type u where
  morph_sort : S₁.signature.S → S₂.signature.S
  morph_op   : S₁.signature.Sig dom rng → S₂.signature.Sig (dom.map morph_sort) (morph_sort rng)
  morph_N : S₁.signature.N st → S₂.signature.N (morph_sort st)
  morph_prop : S₁.prop st → S₂.prop (morph_sort st)
  morph_nom : S₁.nom st → S₂.nom (morph_sort st)
  morph_svar : S₁.svar st → S₂.svar (morph_sort st)

def Symbols.morphism.morph_premise {S₁ : Symbols α} {s : S₁.signature.S} (Γ : PremiseSet S₁ s) (m : Symbols.morphism S₁ S₂) : PremiseSet S₂ (m.morph_sort s) := sorry

def Symbols.morphism.morph_axiom {S₁ : Symbols α} (Λ : AxiomSet S₁) (m : Symbols.morphism S₁ S₂) : AxiomSet S₂ := sorry

structure Symbols.embedding (S₁ : Symbols α) (S₂ : Symbols β) where
  m : Symbols.morphism S₁ S₂
  -- m is injective

omit α in
def Symbols.new_nominals (S₁ : Symbols α) : Σ S₂ : Symbols (ℕ ⊕ α), Symbols.embedding S₁ S₂ := sorry

lemma SatLift {S₁ : Symbols α} {s : S₁.signature.S} {Λ : AxiomSet S₁} {S₂ : Symbols β} {Γ : PremiseSet S₁ s} {m : Symbols.embedding S₁ S₂} :
  (m.m.morph_premise Γ).satisfiable (Models.Ax $ m.m.morph_axiom Λ) ↔ Γ.satisfiable (Models.Ax $ Λ) := sorry

end Completeness
