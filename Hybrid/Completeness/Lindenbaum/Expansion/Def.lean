import Hybrid.Proof
import Hybrid.Semantics

namespace Completeness

open Completeness

variable {α β : Type u}

/--
  TODO SECTION:
    Signature / Symbols extensions and embeddings.
    Properties preserved by embeddings.
-/
structure Symbols.morphism (S₁ : Symbols α) (S₂ : Symbols β) where
  morph_sort : S₁.signature.S → S₂.signature.S
  morph_op {dom rng} : S₁.signature.Sig dom rng → S₂.signature.Sig (dom.map morph_sort) (morph_sort rng)
  morph_N    {st} : S₁.signature.N st → S₂.signature.N (morph_sort st)
  morph_prop {st} : S₁.prop st → S₂.prop (morph_sort st)
  morph_nom  {st} : S₁.nom st → S₂.nom (morph_sort st)
  morph_svar {st} : S₁.svar st → S₂.svar (morph_sort st)

structure Symbols.embedding (S₁ : Symbols α) (S₂ : Symbols β) where
  m : S₁.morphism S₂
  sort_inj : m.morph_sort.Injective
  op_inj   : ∀ dom rng, (@m.morph_op dom rng).Injective
  N_inj    : ∀ st, (@m.morph_N st).Injective
  prop_inj : ∀ st, (@m.morph_prop st).Injective
  nom_inj  : ∀ st, (@m.morph_nom st).Injective
  svar_inj : ∀ st, (@m.morph_svar st).Injective

structure Symbols.nominal_extension [DecidableEq β] (S : Symbols α) (β : Type u) where
  target : Symbols β
  m : S.embedding target
  unused_nominals : { n₂ | ∀ n₁ : S.nom s, m.m.morph_nom n₁ ≠ n₂ } ≃ ℕ

infix:50 "↪" => Symbols.embedding

end Completeness
