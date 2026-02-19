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

def dl_th_2 {α β : ProtocolsForm Act} {p q r : ProtocolsForm Prot}
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

def OSS { i r : ProtocolsForm Agent}
  { n : ProtocolsForm Msg }
  : ProtocolsProof _ $ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶
    [(send i, r(⦃ n ⦄pk(r)))]([(recv r(n))](𝔹 r, (𝕏 i, n))) := by
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
    let h₁₁ : ProtocolsProof _ $ ⟪ (i ◁ n) ⊔ γ₀ i r ⟫ ⟶ (([send i, r(⦃ n ⦄pk(r))]([recv r(n)]((𝔹 r, (𝕏 i, n)))))) := dl_th_2 h₁₀
    exact dl_th_2 h₁₀
