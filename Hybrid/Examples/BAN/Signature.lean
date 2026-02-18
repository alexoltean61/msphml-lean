import Hybrid.BNF
import Hybrid.Language
import Hybrid.Proof

hybrid_def BAN :=
  sort Key     ::= builtin String
  sort Agent   ::= builtin String
  sort Message ::= builtin String
  sort Message ::= "<->"(Agent, Key, Agent) [shareKey]
  sort Message ::= "enc"(Message, Key)      [encrypt]
  sort Message ::= "pair"(Message, Message) [pair]
  sort Nonce   ::= subsort Message
  sort Formula ::= builtin String
  sort Formula ::= "|≡"(Agent, Formula)     [believes]
  sort Formula ::= "ι"(Message)             [mtof]
  sort Formula ::= "|~"(Agent, Formula)     [oncesaid]
  sort Formula ::= "▸"(Agent, Formula)      [sees]
  sort Formula ::= "#"(Message)             [nonce]
  sort Formula ::= "|=>"(Agent, Formula)    [jurisdiction]

#print BAN.Ops

open BAN

@[coe]
def String.toCtNom (str : String) : BAN.CtNoms BAN.Agent := ⟨str, ⟨str, rfl⟩⟩
@[coe]
def String.toCtNom' (str : String) : BAN.CtNoms BAN.Key := ⟨str, ⟨str, rfl⟩⟩
@[coe]
def String.toCtNom'' (str : String) : BAN.CtNoms BAN.Formula := ⟨str, ⟨str, rfl⟩⟩
@[coe]
def String.toCtNom''' (str : String) : BAN.CtNoms BAN.Message := ⟨str, ⟨str, rfl⟩⟩

instance : Coe String (BAN.CtNoms BAN.Agent) where
  coe := String.toCtNom

instance : Coe String (BAN.CtNoms BAN.Key) where
  coe := String.toCtNom'

instance : Coe String (BAN.CtNoms BAN.Formula) where
  coe := String.toCtNom''

instance : Coe String (BAN.CtNoms BAN.Message) where
  coe := String.toCtNom'''

def BANForm := Form BAN

def shareKeyOp (a1 a2 : BANForm Agent) (k : BANForm Key) : BANForm Message := ℋ⟨shareKey⟩ (a1, k, a2)
def encryptOp (m : BANForm Message) (k : BANForm Key) := ℋ⟨encrypt⟩ (m, k)
def pairOp (m₁ : BANForm Message) (m₂ : BANForm Message) := ℋ⟨pair⟩ (m₁, m₂)

def believeOp (a : BANForm Agent) (φ : BANForm Formula) : BANForm Formula := ℋ⟨believes⟩ (a, φ)
def mtofOp (m : BANForm Message) : BANForm Formula := ℋ⟨mtof⟩ (m)
def oncesaidOp (a : BANForm Agent) (φ : BANForm Formula) := ℋ⟨oncesaid⟩ (a, φ)
def seesOp (a : BANForm Agent) (φ : BANForm Formula) := ℋ⟨sees⟩ (a, φ)
def nonceOp (m : BANForm Message) := ℋ⟨nonce⟩ (m)
def jurisdictionOp (a : BANForm Agent) (φ : BANForm Formula) := ℋ⟨jurisdiction⟩ (a, φ)

notation "⦃" m "⦄" k => encryptOp m k
notation "c(" m₁ "," m₂ ")" => pairOp m₁ m₂

notation a " |≡ " φ => believeOp a φ
notation "ι" m => mtofOp m
notation a " |∼ " φ => oncesaidOp a φ
notation a " ▸ " φ => seesOp a φ
notation "#" "(" n ")" => nonceOp n
notation a " |=> " φ => jurisdictionOp a φ

-- example : Form BAN Message :=
--   ℋ⟨shareKey⟩ (ℋNom (.ctNom ⟨"A", ⟨"A", rfl⟩⟩), ℋNom (.ctNom ⟨"123", ⟨"123", rfl⟩⟩), ℋNom (.ctNom ⟨"B", ⟨"B", rfl⟩⟩))

-- example : Form BAN Message :=
--   ℋ⟨shareKey⟩ (ℋNom "A", ℋNom "123", ℋNom "B")

-- example : BANForm Message := shareKeyOp (ℋNom "A") (ℋNom "123") (ℋNom "B")

inductive Axiom : {s : Sorts} → BANForm s → Type
  | MMSK {i j : BANForm Agent} {k : BANForm Key} {m : BANForm Message}
    (h₀ : Axiom $ i |≡ ι shareKeyOp i j k)
    (h₁ : Axiom $ i ▸ ι ⦃ m ⦄k)
    : Axiom $ i |≡ j |∼ ι m
  | NV {i j : BANForm Agent} {m : BANForm Message}
    (h₀ : Axiom (i |≡ j |∼ ι m))
    (h₁ : Axiom (i |≡ #(m)))
    : Axiom (i |≡ j |≡ ι m)
  | NC {i : BANForm Agent} {m₁ m₂ : BANForm Message}
    (h : Axiom $ i |≡ #(m₁))
    : Axiom $ i |≡ #(c(m₁, m₂))
  | JR {i j : BANForm Agent} {m : BANForm Message}
    (h₀ : Axiom $ i |≡ j |≡ ι m)
    (h₁ : Axiom $ i |≡ j |=> ι m)
    : Axiom $ i |≡ ι m
  | BC3₁ {i j : BANForm Agent} {m₁ m₂ : BANForm Message}
    (h : Axiom $ i |≡ j |≡ ι c(m₁, m₂))
    : Axiom $ i |≡ j |≡ ι m₁
  | BC3₂ {i j : BANForm Agent} {m₁ m₂ : BANForm Message}
    (h₀ : Axiom $ i |≡ j |≡ ι c(m₁, m₂))
    : Axiom $ i |≡ j |≡ ι m₂


@[simp] def BANΛ : AxiomSet BAN := λ s => { φ | Nonempty (Axiom φ) }

abbrev BANProof (φ : BANForm s) := Proof BANΛ s φ

def pf' (i j : BANForm Agent) (k : BANForm Key) (m : BANForm Message)
  (h₀ : Axiom (i |≡ ι shareKeyOp i j k))
  (h₁ : Axiom (i ▸ ι ⦃m⦄k)) : Axiom (i |≡ j |∼ ι m) := by
  exact Axiom.MMSK h₀ h₁

section Example
open Axiom

def i : BANForm Agent := ℋNom "i"
def j : BANForm Agent := ℋNom "j"
def k : BANForm Key := ℋNom "k"
def n : BANForm Message := ℋNom "n"

def OSS_proof_sk
  (h₀ : Axiom $ j ▸ ι ⦃n⦄k)
  (h₁ : Axiom $ j |≡ ι shareKeyOp j i k)
  (h₂ : Axiom $ j |≡ #(n))
  : BANProof (j |≡ i |≡ ι n) := by
  apply Proof.ax
  have h₃ := MMSK h₁ h₀
  have h₄ := NV h₃ h₂
  assumption



-- def FormulaSort := ModalBase.WFF
