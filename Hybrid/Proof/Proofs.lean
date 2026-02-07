import Hybrid.Proof.Hilbert
import Hybrid.Language.Instance.Lemmas

namespace Proof

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {Λ : AxiomSet symbs}

def top_proof : Proof Λ s (ℋ⊤) := prop1 _ _

def id_proof : Proof Λ s (φ ⟶ φ) := sorry

def export_theorem_proof : Proof Λ s ((φ ⋀ ψ ⟶ χ) ⟶ (φ ⟶ ψ ⟶ χ)) :=
  -- Theorem pm3.3 in Metamath
  sorry

def export_proof : Proof Λ s (φ ⋀ ψ ⟶ χ) → Proof Λ s (φ ⟶ ψ ⟶ χ) :=
  λ l1 => mp export_theorem_proof l1

def tertium_non_datur_proof : Proof Λ s (φ ⋁ ∼φ) := sorry

def tertium_non_daturAt_proof (k : symbs.nominal t) (φ : Form symbs t) : Proof Λ s (ℋ@ k φ ⋁ ℋ@ k (∼φ)) := sorry

def conj_intro_proof : Proof Λ s (φ ⟶ ψ ⟶ (φ ⋀ ψ)) := sorry

def conj_elimL_proof : Proof Λ s ((φ ⋀ ψ) ⟶ φ) := sorry

def conj_elimR_proof : Proof Λ s ((φ ⋀ ψ) ⟶ ψ) := sorry

def disj_elim_proof : Proof Λ s ((φ ⋁ ψ) ⟶ (φ ⟶ χ) ⟶ (ψ ⟶ χ) ⟶ χ) := sorry

def contraposition : Proof Λ s ((ψ ⟶ φ) ⟶ (∼φ ⟶ ∼ψ)) := sorry

-- Added by Proof.composition
def imp_trans_proof : Proof Λ s (φ ⟶ ψ) → Proof Λ s (ψ ⟶ χ) → Proof Λ s (φ ⟶ χ) := sorry

def generalize_nominals_proof {i : symbs.nominal t} {x y : symbs.svarType t} {φ : Form symbs s} (h : φ.occurs y = false) : Proof Λ s φ[i // x] → Proof Λ s φ[y // x] := sorry

def helperInsertAnd : Proof Λ s (φ ⟶ ψ) → Proof Λ s (φ ⟶ χ) → Proof Λ s (φ ⟶ ψ ⋀ χ) := sorry

def existElimPf {φ ψ : Form symbs s} (h : ψ.closed):
  Proof Λ s ((φ ⟶ ψ).univClosure φ.FV ⟶ (φ.existClosure φ.FV ⟶ ψ)) := sorry

def q2NomContra {k : symbs.nominal t} : Proof Λ s (φ[k // x] ⟶ ℋ∃ x φ) :=
  sorry

def q2VarContra {y : symbs.svarType t} : Proof Λ s (φ[y // x] ⟶ ℋ∃ x φ) :=
  sorry

def insertExist : Proof Λ s (φ ⟶ ℋ∃ x φ) := by
  conv =>
    rhs; lhs; rw [←(@FormL.subst_self_var _ _ _ _ x _ φ)]
  apply q2VarContra

def insertExistCl : Proof Λ s (φ ⟶ φ.existClosure vars) := by
  induction vars with
  | nil =>
      simp [FormL.existClosure]
      exact id_proof
  | cons h xs ih =>
      obtain ⟨s, x⟩ := h
      conv =>
        rhs ; rhs
        simp [FormL.existClosure]
        rhs
        rw [←FormL.existClosure]
      apply imp_trans_proof ih
      apply insertExist

def instanceToExistPf {φ : Form symbs s} (ψ : φ.Instance) :
  Proof Λ s (ψ.form ⟶ (φ.existClosure φ.FV)) := by
    obtain ⟨inst⟩ := ψ
    let ψ := inst.apply φ
    induction inst generalizing φ with
    | nil =>
        apply insertExistCl
    | cons h t ih =>
        -- h maps x to k
        obtain ⟨sx, x, k⟩ := h
        specialize @ih φ[k//x]
        by_cases isFree : φ.occurs_free x
        . -- ih : Proof Λ s (t.apply φ[k//x] ⟶ ℋ∃ φ[k//x].FV φ[k//x])
          rw [←FormL.FVisFV] at isFree
          -- Now (1), φ[k//x].FV   ==   φ.FV \ { x }, since ⟨sx, x⟩ ∈ FormL.FV φ
          rw [FormL.FVsubst isFree] at ih ; clear isFree
          admit
          /-
            Also (2), t.apply φ[k//x]   ==   (t.apply φ)[k // x], if we can guarantee that no
            variable in the instantiation occurs twice.
              (Both constraints can be solved if instantiation domain is simply φ.FV. We have a proof
              that φ.FV.Nodup).
            So by (1) and (2), ih becomes:
            ih : Proof Λ s (t.apply φ)[k//x] ⟶ ℋ∃ (φ.FV \ { x }) φ[k//x])
          -/
          /-
            By the contrapositive of Q2, we know that:
                φ[k//x] ⟶ ℋ∃ x φ
            Plugging that into ih by transitivity:
            ih : Proof Λ s (t.apply φ)[k//x] ⟶ ℋ∃ (φ.FV \ { x }) ℋ∃ x φ)
            -------
            Now, would be great if you could guarantee that the order of variables in the instantiation is identical to order of variables in φ.FV. Because then:
              (ℋ∃ (φ.FV \ { x }) ℋ∃ x φ) ←→ (ℋ∃ x ℋ∃ (φ.FV \ { x }) φ)  (??? how)
              (ℋ∃ x ℋ∃ (φ.FV \ { x }) φ) ←→ (ℋ∃ φ.FV φ)                  (??? how)
            -------
            Plug all of that back into ih and get:
            ih : Proof Λ s (t.apply φ)[k//x] ⟶ (ℋ∃ φ.FV φ)

            Which is the goal.
          -/
        . simp at isFree
          rw [FormL.not_free_nom_subst isFree] at ih
          admit

def genIterated : Proof Λ s φ → Proof Λ s (φ.univClosure vars) := sorry

def instanceToUnivPf {φ : Form symbs s} (ψ : φ.Instance) :
  Proof Λ s (ψ.form) →
  Proof Λ s (φ.univClosure φ.FV) := by
    -- By repeated generalization on nominals.
    -- (I.e.: if instance maps x to i, generalize i to x in ψ)
    -- (Will obtain a proof of ⊢ φ)
    -- (By genIterated, this becomes ⊢ ∀cl φ)
    admit

def instanceToUnivPf' {φ : Form symbs s} (ψ : φ.Instance) (hfv : χ.closed) :
  Proof Λ s (ψ.form ⟶ χ) →
  Proof Λ s ((φ ⟶ χ).univClosure φ.FV) := by
    -- (ψ.form ⟶ χ) is an instance of (φ ⟶ χ)
    -- So apply instanceToUnivPf to hypothesis and obtain
    -- ⊢ (φ ⟶ χ).univClosure (φ ⟶ χ).FV
    -- Since χ.FV = [], then (φ ⟶ χ).FV = φ.FV.
    -- Therefore:
    -- ⊢ (φ ⟶ χ).univClosure φ.FV
    -- QED
    admit

end Proof
