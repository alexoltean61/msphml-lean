import Hybrid.Completeness.Henkin.Model

namespace Completeness
open Completeness
open FormL.Elem

/-
  This file deals with some technical, formalization-specific, proofs required for the applicative case of the
  `Truth` lemma.

  The main lemma here, `pasted_extract_prod`, ensures that given a pasted set (i.e., one which
  satisfies a certain ∀∃-statement), we can extract a concrete product (`WProd`) of the witnesses to the existential,
  and each witness in the product satisfies the original predicate.

  We do so by skolemizing the statement, then turning the obtained function into a product. The fact that we can
  turn the skolemized function into a product is due to the domain of the `∀` quantifier being finite. Namely,
  we have `∀ e : χ.Elem, ∃ j : symbs.nominal e.sort ...`, and we proved there is a surjection from some `Fin n` to
  `χ.Elem`.

  So the proofs here make heavy usage of the ability to finitely enumerate the elements of a formula (see `FormL.Elem.enumerate`).

  Of course: this is utterly trivial. But implementing this was not so straightforward. This file is an
  implementation detail.
-/

variable {α : Type u}
variable {symbs : Symbols α}
variable {s : symbs.signature.S}
variable {Λ : AxiomSet symbs}
variable {Γ : PremiseSet symbs s}
variable {s₁ ss t} {σ : symbs.signature.«Σ» (s₁ :: ss) t}
variable {χ : FormL symbs (s₁ :: ss)}

def FormL.subst_wprod_til (φ : FormL symbs sorts) (til : Fin sorts.length): WProd symbs.nominal sorts → FormL symbs sorts := sorry

lemma to_args_as_subst_til {ws : WProd symbs.nominal (s :: sorts)} :
  ∀ φ : FormL symbs (s :: sorts), ws.to_args = φ.subst_wprod_til (Fin.last _) ws := sorry

theorem next_nominal (hp : Γ.pasted) (hmem : ℋ@k (ℋ⟨σ⟩ χ') ∈ Γ) (i : Fin χ'.num_forms) :
  ∃ j : symbs.nominal (χ'.get_elem i).sort, ℋ@k (ℋ⟨σ⟩ (χ'.get_elem i).ctx [j]) ∈ Γ ∧ ℋ@j (χ'.get_elem i).form ∈ Γ :=
  hp hmem $ χ'.get_elem i

noncomputable def iterate_next_nominal (hp : Γ.pasted) (hmem : ℋ@k (ℋ⟨σ⟩ χ) ∈ Γ) : WProd symbs.nominal (s₁ :: ss) := by
  have j := sort_as_idx ▸ (Classical.choose $ next_nominal hp hmem ⟨0, by simp⟩)
  simp at j
  have hj := Classical.choose_spec $ next_nominal hp hmem ⟨0, by simp⟩
  match ss with
  | [] => exact j
  | _  => sorry

/-
  Take the nominals on the diagonal:
               @j σ(φ₁, φ₂, ..., φₙ) ∈ Γ → (by next_nominal)
  @k₁ φ₁ ∈ Γ ∧ @j σ(k₁, φ₂, ..., φₙ) ∈ Γ → (by next_nominal)
  @k₂ φ₂ ∈ Γ ∧ @j σ(k₁, k₂, ..., φₙ) ∈ Γ → (by next_nominal)
  ...................................... → (by next_nominal)
  @kₙ φₙ ∈ Γ ∧ @j σ(k₁, k₂, ..., kₙ) ∈ Γ

  INVARIANT:
    At each step n, for all i < n, @kᵢ φᵢ ∈ Γ ∧ @j σ(k₁, ..., kᵢ, ..., φₙ) ∈ Γ
-/
theorem paste_everything' (hp : Γ.pasted) (hmem : ℋ@k (ℋ⟨σ⟩ χ) ∈ Γ) (step : Fin χ.num_forms):
  ∃ df, ℋ@ j(ℋ⟨σ⟩ df) ∈ Γ ∧
  ∀ i : Fin step.succ,
    ∃ j : symbs.nominal (χ.get_elem step).sort, df = χ.subst_wprod_til ⟨i, Nat.lt_of_lt_of_le i.2 step.2⟩ ws := by
  admit

theorem paste_everything (hp : Γ.pasted) (hmem : ℋ@k (ℋ⟨σ⟩ χ) ∈ Γ):
  ∃ ws : WProd symbs.nominal (s₁ :: ss), ℋ@ k (ℋ⟨σ⟩ ws.to_args) ∈ Γ ∧ ∀ (e : χ.Elem), ℋ@ (ws.select e.ctx) e.form ∈ Γ := by
  admit
