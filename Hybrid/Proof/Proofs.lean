import Hybrid.Proof.ImpPropagation

namespace Proof

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {Λ : AxiomSet symbs}

def negAt :
    Proof Λ s (ℋ@ i (∼φ) ⟶ ∼(ℋ@ i φ)) := by
  apply imp_trans_proof
  . exact mp conj_elimL_proof (selfDual _ _)
  . apply mp contraposition
    apply mp (kAt _ _ _)
    apply genAt
    exact dni

def negAt' :
    Proof Λ s (∼(ℋ@ i φ) ⟶ ℋ@ i (∼φ)) := by
  apply mp contraposition''
  exact mp conj_elimR_proof (selfDual _ _)

def backContrapositive (C : (@FormL.at α symbs t sᵢ i φ).Context ψ) :
    Proof Λ s (ℋ@i φ ⟶ ℋ⟨σ⟩ᵈ ψ) := by
  unfold FormL.applDual
  apply mp contraposition'
  apply imp_trans_proof _ negAt
  have ⟨χ, C', eq, iso, _⟩ := C.to_negAll
  subst eq
  apply imp_trans_proof
  . apply impAppl C' negAt'
  . apply back
    apply FormL.subst_to_ctx

def kAt_disj {k : symbs.nominal t} : Proof Λ s (ℋ@ k (φ ⋁ ψ) ⟶ ℋ@ k φ ⋁ ℋ@ k ψ) := by
  apply imp_trans_proof _ impAsDisj
  apply imp_com_proof
  apply imp_trans_proof negAt'
  apply imp_trans_proof _ (kAt _ _ _)
  apply mp (kAt _ _ _)
  apply genAt
  apply imp_com_proof
  apply disj_elim_not

def tertium_non_daturAt_proof (k : symbs.nominal t) (φ : Form symbs t) : Proof Λ s (ℋ@ k φ ⋁ ℋ@ k (∼φ)) := by
  have l1 : Proof Λ _ (φ ⋁ (∼φ)) := tertium_non_datur_proof
  have l2 := genAt s k l1
  have l3 := mp kAt_disj l2
  exact l3
