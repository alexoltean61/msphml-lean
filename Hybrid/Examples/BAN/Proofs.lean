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

namespace SimpleOSS
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
end SimpleOSS

namespace NSPK
/-
  Needham-Schroeder Public-Key (NSPK)

  A -> B : { nA }sk(A)
  B -> A : { nA, nB }sk(B)
  A -> B : { nB }sk(A)

  We prove that B |≡ A |≡ nB
-/
  def A  : BANForm Agent := ℋNom "A"
  def B  : BANForm Agent := ℋNom "B"
  def nA : BANForm Message := ℋNom "nA"
  def nB : BANForm Message := ℋNom "nB"

def NSPK_mutual_authentication
  (p₁ : BANProof _ $ B ◁ ι ⦃ nA ⦄sk(A))
  (p₂ : BANProof _ $ A ◁ ι ⦃ c(nA, nB)⦄sk(B))
  (p₃ : BANProof _ $ B ◁ ι ⦃ nB ⦄sk(A))
  (a₁ : BANProof _ $ B |≡ ι pk(A))
  (a₂ : BANProof _ $ B |≡ #(nB))
  : BANProof _ (B |≡ (A |≡ ι nB)) := by
  let h₁ : BANProof _ _ := Proof.ax ⟨ (B |≡ ι pk(A)) ⟶ (B ◁ ι ⦃ nB ⦄sk(A)) ⟶ (B |≡ (A |∼ ι nB)), Nonempty.intro $ Axiom.MMPK⟩
  let h₂ : BANProof _ $ (B ◁ ι ⦃ nB ⦄sk(A)) ⟶ (B |≡ (A |∼ ι nB)) := Proof.mp h₁ a₁
  let h₃ : BANProof _ $ B |≡ (A |∼ ι nB) := Proof.mp h₂ p₃
  let h₄ : BANProof _ $ B |≡ (A |≡ ι nB) := NV h₃ a₂
  assumption


end NSPK
