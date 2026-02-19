import Hybrid.Examples.Protocols.Axioms

open Protocols

def γ₀ (i r : ProtocolsForm Agent) : ProtocolsForm StNom :=
  (r ◁ sk(r)) ⊔ (r ◁ pk(i)) ⊔ (r ◁ pk(r)) ⊔ (i ◁ pk(i)) ⊔ (i ◁ sk(i)) ⊔ (i ◁ pk(r))

def pl_aux { p q r : ProtocolsForm Prot}
  (h₀ : ProtocolsProof _ $ p ⟶ q)
  (h₁ : ProtocolsProof _ $ p ⟶ (q ⟶ r))
  : ProtocolsProof _ $ p ⟶ r := by
  let prop2 : ProtocolsProof _ $ (p ⟶ (q ⟶ r)) ⟶ ((p ⟶ q) ⟶ (p ⟶ r)) := Proof.prop2 p q r
  let h₂ : ProtocolsProof _ $  ((p ⟶ q) ⟶ (p ⟶ r)) := Proof.mp prop2 h₁
  exact Proof.mp h₂ h₀

def dl_th_1 {α : ProtocolsForm Act} {p q r : ProtocolsForm Prot}
  (h₀ : ProtocolsProof _ $ (p ⟶ [α]q))
  (h₁ : ProtocolsProof _ $ (p ⟶ [α]r))
  : ProtocolsProof _ $  (p ⟶ ([α](q ⋀ r))) := by
  let prop_formula : ProtocolsProof _ $ q ⟶ r ⟶ q ⋀ r := Proof.conj_intro_proof
  let k_formula : ProtocolsProof _ $ ([α](q ⟶ (r ⟶ q ⋀ r))) ⟶ (([α]q) ⟶ ([α](r ⟶ q ⋀ r))) := Kα
  let nec_formula : ProtocolsProof _ $ [α](q ⟶ (r ⟶ q ⋀ r)) := Necα prop_formula
  let h₂ : ProtocolsProof _ $ ([α]q) ⟶ ([α](r ⟶ q ⋀ r)) := Proof.mp k_formula nec_formula
  let h₃ : ProtocolsProof _ $ p ⟶ ([α](r ⟶ q ⋀ r)) := Proof.imp_trans_proof h₀ h₂
  let nec_formula_2 : ProtocolsProof _ $ ([α](r ⟶ q ⋀ r)) ⟶ (([α]r) ⟶ [α](q ⋀ r)) := Kα
  let h₄ : ProtocolsProof _ $ p ⟶ (([α]r) ⟶ [α](q ⋀ r)) := Proof.imp_trans_proof h₃ nec_formula_2
  exact pl_aux h₁ h₄

def dl_th_1' {α β : ProtocolsForm Act} {p q r : ProtocolsForm Prot}
  (h₀ : ProtocolsProof _ $ (p ⟶ [α][β]q))
  (h₁ : ProtocolsProof _ $ (p ⟶ [α][β]r))
  : ProtocolsProof _ $  (p ⟶ ([α][β](q ⋀ r))) := by
  let prop_formula : ProtocolsProof _ $ q ⟶ r ⟶ q ⋀ r := Proof.conj_intro_proof
  let k_formula : ProtocolsProof _ $ ([β](q ⟶ (r ⟶ q ⋀ r))) ⟶ (([β]q) ⟶ ([β](r ⟶ q ⋀ r))) := Kα
  let nec_formula : ProtocolsProof _ $ [β](q ⟶ (r ⟶ q ⋀ r)) := Necα prop_formula
  let h₂  : ProtocolsProof _ $ ([β]q) ⟶ ([β](r ⟶ q ⋀ r)) := Proof.mp k_formula nec_formula
  let h₃  : ProtocolsProof _ $ [α](([β]q) ⟶ ([β](r ⟶ q ⋀ r))) := Necα h₂
  let h₄  : ProtocolsProof _ $ ([α](([β]q) ⟶ ([β](r ⟶ q ⋀ r)))) ⟶ (([α]([β]q)) ⟶ ([α]([β](r ⟶ q ⋀ r)))) := Kα
  let h₅  : ProtocolsProof _ $ ([α][β]q) ⟶ ([α][β](r ⟶ q ⋀ r)) := Proof.mp h₄ h₃
  let h₆  : ProtocolsProof _ $ p ⟶ ([α][β](r ⟶ q ⋀ r)) := Proof.imp_trans_proof h₀ h₅
  let h₇  : ProtocolsProof _ $ ([β](r ⟶ q ⋀ r)) ⟶ (([β]r) ⟶ [β](q ⋀ r)) := Kα
  let h₈  : ProtocolsProof _ $ ([β]q) ⟶ (([β]r) ⟶ [β](q ⋀ r)) := Proof.imp_trans_proof h₂ h₇
  let h₉  : ProtocolsProof _ $ [α](([β]q) ⟶ (([β]r) ⟶ [β](q ⋀ r))) := Necα h₈
  let h₁₀ : ProtocolsProof _ $ ([α](([β]q) ⟶ (([β]r) ⟶ [β](q ⋀ r)))) ⟶ (([α]([β]q)) ⟶ ([α]((([β]r) ⟶ [β](q ⋀ r))))) := Kα
  let h₁₁ : ProtocolsProof _ $ ([α][β]q) ⟶ ([α]((([β]r) ⟶ [β](q ⋀ r)))) := Proof.mp h₁₀ h₉
  let h₁₂ : ProtocolsProof _ $ p ⟶ [α]((([β]r) ⟶ [β](q ⋀ r))) :=Proof.imp_trans_proof h₀ h₁₁
  let h₁₃ : ProtocolsProof _ $ ([α]((([β]r) ⟶ [β](q ⋀ r)))) ⟶ (([α]([β]r)) ⟶ ([α]([β](q ⋀ r)))) := Kα
  let h₁₄ : ProtocolsProof _ $ p ⟶ (([α]([β]r)) ⟶ ([α]([β](q ⋀ r)))) := Proof.imp_trans_proof h₁₂ h₁₃
  exact pl_aux h₁ h₁₄


def dl_th_2_left {α β : ProtocolsForm Act} {p q r : ProtocolsForm Prot}
  (h : ProtocolsProof _ $ (p ⟶ [α]([β](q ⋀ r))))
  : ProtocolsProof _ $ p ⟶ [α]([β]q) := by
  let h₀ : ProtocolsProof _ $ (q ⋀ r) ⟶ q := Proof.conj_elimL_proof
  let h₁ : ProtocolsProof _ $ [β]((q ⋀ r) ⟶ q) := Necα h₀
  let h₂ : ProtocolsProof _ $ ([β]((q ⋀ r) ⟶ q)) ⟶ (([β](q ⋀ r)) ⟶ [β]q) := Kα
  let h₃ : ProtocolsProof _ $ (([β](q ⋀ r)) ⟶ [β]q) := Proof.mp h₂ h₁
  let h₄ : ProtocolsProof _ $ [α](([β](q ⋀ r)) ⟶ [β]q) := Necα h₃
  let h₅ : ProtocolsProof _ $ ([α](([β](q ⋀ r)) ⟶ [β]q)) ⟶ (([α]([β](q ⋀ r))) ⟶ [α]([β]q)) := Kα
  let h₆ : ProtocolsProof _ $ ([α]([β](q ⋀ r))) ⟶ [α]([β]q) := Proof.mp h₅ h₄
  exact Proof.imp_trans_proof h h₆

def dl_th_2_right {α β : ProtocolsForm Act} {p q r : ProtocolsForm Prot}
  (h : ProtocolsProof _ $ (p ⟶ [α]([β](q ⋀ r))))
  : ProtocolsProof _ $ p ⟶ [α]([β]r) := by
  let h₀ : ProtocolsProof _ $ (q ⋀ r) ⟶ r := Proof.conj_elimR_proof
  let h₁ : ProtocolsProof _ $ [β]((q ⋀ r) ⟶ r) := Necα h₀
  let h₂ : ProtocolsProof _ $ ([β]((q ⋀ r) ⟶ r)) ⟶ (([β](q ⋀ r)) ⟶ [β]r) := Kα
  let h₃ : ProtocolsProof _ $ (([β](q ⋀ r)) ⟶ [β]r) := Proof.mp h₂ h₁
  let h₄ : ProtocolsProof _ $ [α](([β](q ⋀ r)) ⟶ [β]r) := Necα h₃
  let h₅ : ProtocolsProof _ $ ([α](([β](q ⋀ r)) ⟶ [β]r)) ⟶ (([α]([β](q ⋀ r))) ⟶ [α]([β]r)) := Kα
  let h₆ : ProtocolsProof _ $ ([α]([β](q ⋀ r))) ⟶ [α]([β]r) := Proof.mp h₅ h₄
  exact Proof.imp_trans_proof h h₆

def OSS { i r : ProtocolsForm Agent}
  { n : ProtocolsForm Msg }
  : ProtocolsProof _ $ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶
    [(send i, r(⦃ n ⦄pk(r)))]([(recv r(n))](𝕂 r, (𝕏 i, n))) := by
    let h₁  : ProtocolsProof _ _ := Proof.ax ⟨⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ [send i, r(⦃ n ⦄pk(r))] 𝔹 i, (𝕏 r, n), Nonempty.intro $ Axiom.OSS₁ ⟩
    let h₂  : ProtocolsProof _ _ := Proof.ax ⟨⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ [send i, r(⦃ n ⦄pk(r))] ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ , Nonempty.intro $ Axiom.H₁ ⟩
    let h₃  : ProtocolsProof _ $ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ [send i, r(⦃ n ⦄pk(r))] (𝔹 i, (𝕏 r, n)) ⋀ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫  := dl_th_1 h₁ h₂
    let h₄  : ProtocolsProof _ _ := Proof.ax ⟨ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ [recv r(n)]𝔹 r, (𝕏 i, n), Nonempty.intro $ Axiom.OSS₂ ⟩
    let h₅  : ProtocolsProof _ _ := Proof.ax ⟨ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ [recv r(n)] ⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫ , Nonempty.intro $ Axiom.H₂ ⟩
    let h₆  : ProtocolsProof _ $ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ [recv r(n)]((𝔹 r, (𝕏 i, n)) ⋀ ⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫) := dl_th_1 h₄ h₅
    let h₇  : ProtocolsProof _ $ [send i, r(⦃ n ⦄pk(r))](⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ [recv r(n)]((𝔹 r, (𝕏 i, n)) ⋀ ⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)) := Necα h₆
    let h₈  : ProtocolsProof _ $ ([send i, r(⦃ n ⦄pk(r))](⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ [recv r(n)]((𝔹 r, (𝕏 i, n)) ⋀ ⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫))) ⟶ (([send i, r(⦃ n ⦄pk(r))](⟪ (i ◁ n) ⊔ γ₀ i r ⟫)) ⟶ ([send i, r(⦃ n ⦄pk(r))]([recv r(n)]((𝔹 r, (𝕏 i, n)) ⋀ ⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)))) := Kα
    let h₉  : ProtocolsProof _ $ (([send i, r(⦃ n ⦄pk(r))](⟪ (i ◁ n) ⊔ γ₀ i r ⟫)) ⟶ ([send i, r(⦃ n ⦄pk(r))]([recv r(n)]((𝔹 r, (𝕏 i, n)) ⋀ ⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)))) := Proof.mp h₈ h₇
    let h₁₀ : ProtocolsProof _ $ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ ([send i, r(⦃ n ⦄pk(r))]([recv r(n)]((𝔹 r, (𝕏 i, n)) ⋀ ⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫))) := Proof.imp_trans_proof h₂ h₉
    let h₁₁ : ProtocolsProof _ $ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ (([send i, r(⦃ n ⦄pk(r))]([recv r(n)]((𝔹 r, (𝕏 i, n)))))) := dl_th_2_left h₁₀
    let h₁₂ : ProtocolsProof _ _ := Proof.ax ⟨ ⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ ⟪  (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫, Nonempty.intro $ Axiom.ST₁ ⟩
    let h₁₃ : ProtocolsProof _ _ := Proof.ax ⟨ (⟪ (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫ ⟶ 𝕏 i, n), Nonempty.intro $ Axiom.ST₃⟩
    let h₁₄ : ProtocolsProof _ $ [recv r(n)]⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ ⟪  (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫ := Necα h₁₂
    let h₁₅ : ProtocolsProof _ $ ([recv r(n)]⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ ⟪  (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫) ⟶ (([recv r(n)](⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)) ⟶ ([recv r(n)](⟪  (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫))) := Kα
    let h₁₆ : ProtocolsProof _ $ ([recv r(n)](⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)) ⟶ ([recv r(n)](⟪  (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫)) := Proof.mp h₁₅ h₁₄
    let h₁₇ : ProtocolsProof _ $ [send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)) ⟶ ([recv r(n)](⟪  (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫))) := Necα h₁₆
    let h₁₈ : ProtocolsProof _ $ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)) ⟶ ([recv r(n)](⟪  (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫)))) ⟶ (([send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)))) ⟶ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪  (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫))))) := Kα
    let h₁₉ : ProtocolsProof _ $ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)))) ⟶ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪  (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫)))) := Proof.mp h₁₈ h₁₇
    let h₂₀ : ProtocolsProof _ $ [recv r(n)](⟪ (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫ ⟶ 𝕏 i, n) := Necα h₁₃
    let h₂₁ : ProtocolsProof _ $ ([recv r(n)](⟪ (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫ ⟶ 𝕏 i, n)) ⟶ (([recv r(n)](⟪ (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫)) ⟶ ([recv r(n)](𝕏 i, n))) := Kα
    let h₂₂ : ProtocolsProof _ $ (([recv r(n)](⟪ (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫)) ⟶ ([recv r(n)](𝕏 i, n))) := Proof.mp h₂₁ h₂₀
    let h₂₃ : ProtocolsProof _ $ [send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪ (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫)) ⟶ ([recv r(n)](𝕏 i, n))) := Necα h₂₂
    let h₂₄ : ProtocolsProof _ $ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪ (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫)) ⟶ ([recv r(n)](𝕏 i, n)))) ⟶ (([send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪ (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫)))) ⟶ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](𝕏 i, n))))) := Kα
    let h₂₅ : ProtocolsProof _ $ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪ (i ◁ n) ⊔ (r ◁ n) ⊔ γ₀ i r ⟫)))) ⟶ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](𝕏 i, n)))) := Proof.mp h₂₄ h₂₃
    let h₂₆ : ProtocolsProof _ $ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)))) ⟶ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](𝕏 i, n)))) := Proof.imp_trans_proof h₁₉ h₂₅
    let h₂₇ : ProtocolsProof _ $ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](⟪ (r ◁ n) ⊔ (i ◁ n) ⊔ γ₀ i r ⟫)))) := dl_th_2_right h₁₀
    let h₂₈ : ProtocolsProof _ $ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)](𝕏 i, n)))) := Proof.imp_trans_proof h₂₇ h₂₆
    let h₂₉ : ProtocolsProof _ $ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ ([send i, r(⦃ n ⦄pk(r))](([recv r(n)]((𝔹 r, (𝕏 i, n)) ⋀ (𝕏 i, n))))) := dl_th_1' h₁₁ h₂₈
    exact dl_th_1' h₁₁ h₂₈
