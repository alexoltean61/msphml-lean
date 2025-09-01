import Hybrid.Proof
import Hybrid.Semantics
import Hybrid.Completeness.Lindenbaum.Expansion
import Hybrid.Completeness.Lindenbaum.Lemma
import Hybrid.Completeness.Henkin.Truth

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s : symbs.signature.S}

namespace Completeness

omit [DecidableEq α] in
lemma SatSubset {Γ : PremiseSet symbs s} {C : Set (Model symbs)} : Γ.satisfiable C → Δ ⊆ Γ → Δ.satisfiable C := by
  admit

lemma ModelExistence {Λ : AxiomSet symbs} {Γ : PremiseSet symbs s} : (Γ ⊨Mod(Λ) φ → Γ ⊢(Λ) φ) ↔ (Γ.consistent Λ → Γ.satisfiable Λ.Models) := by
  apply Iff.intro
  . intro h
    admit
  . intro h
    contrapose
    intro h2 h3
    admit

end Completeness

open Completeness

theorem Completeness {Λ : AxiomSet symbs} : Γ ⊨Mod(Λ) φ → Γ ⊢(Λ) φ := by
  rw [ModelExistence]
  intro h_cons
  -- Need to prove that Γ (set of Form symbs s) is satisfiable.
  -- Will use the property that:
  --    If symbs ⊆ symbs' and Γ' is Γ lifted to symbs',
  --      then if Γ' is satisfiable in symbs', Γ is satisfiable in symbs
  -- This is lemma SatLift above
  rw [←SatLift]
  . -- Next, apply SatSubset:
    have ⟨Γ', incl⟩ := Lindenbaum nominal_extension.default h_cons
    apply SatSubset
    case Γ =>
      exact Γ'.set
    . -- Here, apply Truth lemma,
      --  and use the fact that Γ' is a MCS and so is
      --  closed under Gen@ rule.
      exists ⟨Γ'.HenkinModel, HenkinInΛ⟩
      exists Γ'.HenkinAsgn
      have ⟨j, j_in_Γ'⟩ := Γ'.named
      exists ⟦j⟧
      intro φ
      rw [Truth]
      apply gen_at_closed Γ'.mcs
      exact j_in_Γ'
    . -- From the Lindenbaum lemma, we know Γ is a subset
      -- of Γ' (in the extended language)
      apply incl
