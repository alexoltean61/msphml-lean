import Hybrid.Examples.SMC.Axioms
import Hybrid.Proof.Proofs

open SMC

def Proof.composition
    (h1 : SMCProof _ (φ₀ ⟶ [α₁] φ₁))
    (h2 : SMCProof _ (φ₁ ⟶ [α₂] φ₂)) :
  SMCProof _ (φ₀ ⟶ [α₁ ; α₂] φ₂) := by
  have l1 : SMCProof _ ([α₁] (φ₁ ⟶ [α₂] φ₂)) := ug (.tail .refl) h2
  -- Some ugly technicalities:
  --   Reasoning with contexts forces us to break the nice [α] φ notation into
  --   primitive applications of ℋ⟨PDLOp⟩ᵈ
  let C : (φ₁ ⟶ [α₂] φ₂).Context (∼α₁, (φ₁ ⟶ [α₂] φ₂)) := .tail .refl
  have l2 : SMCProof _ (ℋ⟨PDLOp⟩ᵈ (∼α₁, φ₁ ⟶ [α₂] φ₂) ⟶ (ℋ⟨PDLOp⟩ᵈ C[φ₁]) ⟶ ℋ⟨PDLOp⟩ᵈ C[ℋ⟨PDLOp⟩ᵈ (∼α₂, φ₂)]) := k _ _ _ _ C
  -- Context reasoning: putting φ₁ in the context C yields formula list (α₁, φ₁)
  have : C[φ₁] = (∼α₁, φ₁) := by aesop
  rw [this] at l2 ; clear this
  -- Similar
  have : C[ℋ⟨PDLOp⟩ᵈ (∼α₂, φ₂)] = (∼α₁, [α₂] φ₂) := by aesop
  rw [this] at l2 ; clear this
  --
  have l3 : SMCProof _ (([α₁] φ₁) ⟶ [α₁][α₂] φ₂) := mp l2 l1
  have l4 : SMCProof _ (φ₀ ⟶ [α₁][α₂] φ₂) := imp_trans_proof h1 l3
  have l5 := imp_trans_proof l4 cseqAx
  exact l5

def Pgm (s i n : Symb.nominal SortVar)
  : SMCForm SortStmt :=
  s ::= 0;
  i ::= 0;
  while (++i <= n) do'
    s ::= s + i

def PgmCorrect (vs : SMCForm SortValStack)
        (mem : SMCForm SortMem)
        (s i n : Symb.nominal SortVar)
        (vn : ℕ) : SMCForm SortConfig :=
    ⟨vs, set(mem, n, vn)⟩ ⟶ [c(Pgm s i n)] ⟨vs, set(set(set(mem, n, vn), s, vn * (vn.add 1).div2), i, vn.add 1)⟩

def todo : SMCProof _ (PgmCorrect vs mem s i n vn) := sorry

def pgm_corr {s : Symb.nominal SortVar}: SMCProof _
-- ([c(s ::= (n : ℕ))] ⟨vs, set(mem, s, n)⟩) := by
  (⟨vs, set(mem, s, n)⟩ ⟶ [c(s ::= 1)] ⟨vs, set(mem, s, (1 : ℕ))⟩) := by
    -- 1. Inlocuire cu DAsgn peste c(Pgm' s)
    -- Rule of composition!
    sorry
