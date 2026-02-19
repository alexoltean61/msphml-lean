import Hybrid.Examples.Protocols.Signature
import Hybrid.Proof

open Protocols

inductive Axiom : {s : Sorts} → ProtocolsForm s → Type
| X₁₁₁ {m₁ m₂ : ProtocolsForm Msg} {a : ProtocolsForm Agent}
  : Axiom $ (𝕏 a, (m₁ ‖ m₂)) ⟶ (𝕏 a, m₁)
| X₁₁₂ {m₁ m₂ : ProtocolsForm Msg} {a : ProtocolsForm Agent}
  : Axiom $ (𝕏 a, (m₁ ‖ m₂)) ⟶ (𝕏 a, m₂)
| X₁₂ {m₁ m₂ : ProtocolsForm Msg} {a : ProtocolsForm Agent}
  : Axiom $ (𝕏 a, m₁) ⟶ (𝕏 a, m₂) ⟶ (𝕏 a, (m₁ ‖ m₂))
| H₁ {a b : ProtocolsForm Agent} {m k : ProtocolsForm Msg} {γ : ProtocolsForm StNom }
  : Axiom $ ⟪ (a ◁ m) ⊔ γ ⟫ ⟶ [send a, b(⦃ m ⦄k)] ⟪ (a ◁ m) ⊔ γ  ⟫
| H₂ {a : ProtocolsForm Agent} {m : ProtocolsForm Msg} {γ : ProtocolsForm StNom}
  : Axiom $ ⟪ γ ⟫ ⟶ [recv a(m)] ⟪ (a ◁ m) ⊔ γ ⟫
| ST₁ {a : ProtocolsForm Agent} {m : ProtocolsForm Msg} {γ₁ γ₂ : ProtocolsForm StNom}
  : Axiom $ ⟪ γ₁ ⊔ (a ◁ m) ⊔ γ₂ ⟫ ⟶ ⟪ (a ◁ m) ⊔ γ₁ ⊔ γ₂ ⟫
| ST₃ {a : ProtocolsForm Agent} {m : ProtocolsForm Msg} {γ : ProtocolsForm StNom}
  : Axiom $ ⟪ (a ◁ m) ⊔ γ ⟫ ⟶ 𝕏 a, m
| OSS₁ {a b : ProtocolsForm Agent} {m : ProtocolsForm Msg} { γ : ProtocolsForm StNom }
  : Axiom $ ⟪ (a ◁ m) ⊔ γ ⟫ ⟶ [send a, b(⦃ m ⦄pk(b))] 𝔹 a, (𝕏 b, m)
| OSS₂ {a b : ProtocolsForm Agent} {m : ProtocolsForm Msg} {γ : ProtocolsForm StNom}
  : Axiom $ ⟪ γ ⟫ ⟶ [recv b(m)]𝔹 b, (𝕏 a, m)

@[simp] def ProtocolsΛ : AxiomSet Protocols := λ _ => { φ | Nonempty (Axiom φ) }

abbrev ProtocolsProof := Proof ProtocolsΛ

variable { p : ProtocolsForm Prot }

def NecB {a : ProtocolsForm Agent} {p : ProtocolsForm Prot} (h : ProtocolsProof _ p)
  : (ProtocolsProof _ (𝔹 a, p)) := by
  let C : p.Context (a, p) := .tail .refl
  rw [believeOp]
  exact Proof.ug C h

def KB {a : ProtocolsForm Agent} {p q : ProtocolsForm Prot}
  : ProtocolsProof _ $ (𝔹 a, (p ⟶ q)) ⟶ ((𝔹 a, p) ⟶ (𝔹 a, q)) := by
  let C : (p ⟶ q).Context (a, p ⟶ q) := .tail .refl
  have subst1 : C[p] = (a, p) := rfl
  have subst2 : C[q] = (a, q) := rfl
  rw [believeOp, believeOp, believeOp]
  rw [←subst1, ←subst2]
  apply Proof.k

def Necα {α : ProtocolsForm Act} {p : ProtocolsForm Prot} (h : ProtocolsProof _ p)
  : ProtocolsProof _ $ [α]p := by
  let C : p.Context (α, p) := .tail .refl
  rw [actionOp]
  exact Proof.ug C h

def Kα {α : ProtocolsForm Act} {p q : ProtocolsForm Prot}
  : ProtocolsProof _ $ ([α](p ⟶ q)) ⟶ (([α]p) ⟶ [α]q) := by
  let C : (p ⟶ q).Context (α, p ⟶ q) := .tail .refl
  have subst1 : C[p] = (α, p) := rfl
  have subst2 : C[q] = (α, q) := rfl
  rw [actionOp, actionOp, actionOp]
  rw [←subst1, ←subst2]
  apply Proof.k
