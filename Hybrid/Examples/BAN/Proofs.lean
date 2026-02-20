import Hybrid.Examples.BAN.Signature

namespace BAN

inductive Axiom : {s : Sorts} → BANForm s → Type
  | MMSK {i j : BANForm Agent} {m k : BANForm Message}
    : Axiom $ (i |≡ ι shareKeyOp i j k) ⟶ (i ◁ ι ⦃ m ⦄k) ⟶ (i |≡ j |∼ ι m)
  | MMPK {i j : BANForm Agent} {m : BANForm Message}
    : Axiom $ (i |≡ ι pk(j)) ⟶ (i ◁ ι ⦃ m ⦄sk(j)) ⟶ (i |≡ j |∼ ι m)
  | NV {i j : BANForm Agent} {m : BANForm Message}
    : Axiom $ (i |≡ j |∼ ι m) ⟶ (i |≡ #(m)) ⟶ (i |≡ j |≡ ι m)
  | NC {i : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ i |≡ #(m₁) ⟶ i |≡ #(c(m₁, m₂))
  | JR {i j : BANForm Agent} {m : BANForm Message}
    : Axiom $ (i |≡ j |≡ ι m) ⟶ (i |≡ j |=> ι m) ⟶ (i |≡ ι m)
  | BC1₁ {i j : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ i |≡ (j |≡ ι c(m₁, m₂)) ⟶ (i |≡ (j |≡ ι m₁))
  | BC1₂ {i j : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ i |≡ (j |≡ ι c(m₁, m₂)) ⟶ (i |≡ (j |≡ ι m₂))
  | BC2₁ {i : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ (i |≡ ι c(m₁, m₂)) ⟶ (i |≡ ι m₁)
  | BC2₂ {i : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ (i |≡ ι c(m₁, m₂)) ⟶ (i |≡ ι m₂)
  | BC3₁ {i j : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ (i |≡ j |≡ ι c(m₁, m₂)) ⟶ (i |≡ j |≡ ι m₁)
  | BC3₂ {i j : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ (i |≡ j |≡ ι c(m₁, m₂)) ⟶ (i |≡ j |≡ ι m₂)
  | BC4₁ {i j : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ (i |≡ (j |∼ ι c(m₁, m₂))) ⟶ (i |≡ (j |∼ ι m₁))
  | BC4₂ {i j : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ (i |≡ (j |∼ ι c(m₁, m₂))) ⟶ (i |≡ (j |∼ ι m₂))
  | SC1₁ {i : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ (i ◁ ι c(m₁, m₂)) ⟶ (i ◁ ι m₁)
  | SC1₂ {i : BANForm Agent} {m₁ m₂ : BANForm Message}
    : Axiom $ (i ◁ ι c(m₁, m₂)) ⟶ (i ◁ ι m₂)
  | SC2 {i j : BANForm Agent} {m : BANForm Message}
    : Axiom $ (i |≡ ι pk(j)) ⟶ (i ◁ ι ⦃m⦄sk(j)) ⟶ (i ◁ ι m)
  | SC3 {i j : BANForm Agent} {m k : BANForm Message}
    : Axiom $ (i |≡ ι shareKeyOp i j k) ⟶ (i ◁ ι ⦃m⦄k) ⟶ (i ◁ ι m)


@[simp] def BANΛ : AxiomSet BAN := λ _ => { φ | Nonempty (Axiom φ) }

abbrev BANProof := Proof BANΛ

def MMSK
  (h₁ : BANProof _ (i |≡ ι shareKeyOp i j k))
  (h₂ : BANProof _ (i ◁ ι ⦃ m ⦄k)) :
    BANProof _ (i |≡ j |∼ ι m) := by
  have h₃ : BANProof _ _ := Proof.ax ⟨(i |≡ ι shareKeyOp i j k) ⟶ (i ◁ ι ⦃ m ⦄k) ⟶ (i |≡ j |∼ ι m), Nonempty.intro $ Axiom.MMSK⟩
  have h₄ := Proof.mp h₃ h₁
  exact Proof.mp h₄ h₂

def NV
  (h₁ : BANProof _ (i |≡ j |∼ ι m))
  (h₂ : BANProof _ (i |≡ #(m))) :
    BANProof _ (i |≡ j |≡ ι m) := by
  have h₃ : BANProof _ _ := Proof.ax ⟨(i |≡ j |∼ ι m) ⟶ (i |≡ #(m)) ⟶ (i |≡ j |≡ ι m), Nonempty.intro $ Axiom.NV⟩
  have h₄ := Proof.mp h₃ h₁
  exact Proof.mp h₄ h₂

def pf' (i j : BANForm Agent) (m k : BANForm Message)
  (h₀ : BANProof _ (i |≡ ι shareKeyOp i j k))
  (h₁ : BANProof _ (i ◁ ι ⦃m⦄k)) : BANProof _ (i |≡ j |∼ ι m) := by
  exact MMSK h₀ h₁

def i : BANForm Agent := ℋNom "i"
def j : BANForm Agent := ℋNom "j"
def k : BANForm Message := ℋNom "k"
def n : BANForm Message := ℋNom "n"

def OSS_proof_sk
  (h₀ : BANProof _ $ j ◁ ι ⦃n⦄k)
  (h₁ : BANProof _ $ j |≡ ι shareKeyOp j i k)
  (h₂ : BANProof _ $ j |≡ #(n))
  : BANProof _ (j |≡ i |≡ ι n) := by
  have h₃ := MMSK h₁ h₀
  exact NV h₃ h₂
