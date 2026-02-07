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

def import_theorem_proof : Proof Λ s ((φ ⟶ ψ ⟶ χ) ⟶ (φ ⋀ ψ ⟶ χ)) :=
  -- Theorem pm3.31 in Metamath
  sorry

def import_proof : Proof Λ s (φ ⟶ ψ ⟶ χ) → Proof Λ s (φ ⋀ ψ ⟶ χ) :=
  λ l1 => mp import_theorem_proof l1

def imp_com_proof : Proof Λ s (φ ⟶ ψ ⟶ χ) → Proof Λ s (ψ ⟶ φ ⟶ χ) := sorry

def imp_com_proof' : Proof Λ s (φ ⟶ ψ ⟶ χ ⟶ τ) → Proof Λ s (φ ⟶ χ ⟶ ψ ⟶ τ) := sorry

def imp_idem_proof : Proof Λ s (φ ⟶ φ ⟶ ψ) → Proof Λ s (φ ⟶ ψ) := sorry

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

def alpha_conversion_proof {x y : symbs.svarType t} {φ : Form symbs s} (h : φ.occurs y = false) : Proof Λ s (ℋ∀ y φ[y // x]) → Proof Λ s (ℋ∀ x φ) := sorry

def name'_proof {i : symbs.nomType s} (h2 : φ.occurs i = false) (pf : Proof Λ s (i ⟶ φ)) : Proof Λ s φ :=
  have l1 := genAt s i pf
  have l2 := mp (kAt _ _ _) l1
  have l3 := mp l2 (ref _ _)
  have l4 := nameAt _ h2 l3
  l4

def q2_nom'_proof {x : symbs.svar t} (h1 : ¬Λ.occurs i) (h2 : φ.occurs i = false) (pf : Proof Λ s (ℋ@ i (ℋVar x) ⟶ φ)) : Proof Λ s φ :=
  have l1 := gen x pf
  have l2 := mp (q2_nom i _ _) l1
  have eq1 := @FormL.subst_nom_implies _ _ _ _ x i _ (ℋ@ i x) φ
  have eq2 := @FormL.subst_nom_at _ _ _ _ _ s x i x i
  have eq3 := @FormL.subst_nom_var _ _ _ _ x i
  have l3 := eq3 ▸ eq2 ▸ eq1 ▸ l2
  have l4 := mp l3 (ref _ _)
  have y : symbs.svarType t := sorry
  have y_fresh : φ.occurs y = false := sorry
  have l5 := generalize_nominals_proof y_fresh l4
  have l6 := gen y l5
  sorry

def exists_lemma_proof {i : symbs.nominal t} (h1 : ¬Λ.occurs i) (h2 : ¬Θ.occurs i) (pf : Proof Λ s (Θ ⟶ ℋ@ j φ[i // x] ⟶ ℋ⊥)) : Proof Λ s (Θ ⟶ ℋ@j (ℋ∃x φ) ⟶ ℋ⊥) := by
  have oh : (Θ ⟶ ℋ@ j φ[i//x] ⟶ ℋ⊥) = (Θ ⟶ ℋ@ j φ ⟶ ℋ⊥)[i // x] := sorry
  rw [oh] at pf
  have y : symbs.svarType t := sorry
  have y_fresh : (Θ ⟶ ℋ@ j φ ⟶ ℋ⊥).occurs y = false := sorry
  have := generalize_nominals_proof y_fresh pf
  admit

def bridge_proof {j : symbs.nominal t} {φ : Form symbs t} (C : (ℋNom j).Context χ) : Proof Λ s (ℋ⟨σ⟩ χ ⋀ ℋ@ j φ ⟶ ℋ⟨σ⟩ C[φ]) := by

  admit

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
