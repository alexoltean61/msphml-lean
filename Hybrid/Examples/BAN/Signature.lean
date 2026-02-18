import Hybrid.BNF
import Hybrid.Language
import Hybrid.Proof

hybrid_def BAN :=
  sort Key   ::= builtin String
  sort Nonce ::= builtin String
  sort Agent ::= builtin String
  sort Message ::= subsort Nonce
  sort Message ::= "<->"(Agent, Key, Agent) [shareKey]
  sort Message ::= "enc"(Message, Key)      [encrypt]
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

instance : Coe String (BAN.CtNoms BAN.Agent) where
  coe := String.toCtNom
instance : Coe String (BAN.CtNoms BAN.Key) where
  coe := String.toCtNom'
instance : Coe String (BAN.CtNoms BAN.Formula) where
  coe := String.toCtNom''

def BANForm := Form BAN

def shareKeyOp (a1 a2 : BANForm Agent) (k : BANForm Key) : BANForm Message := ℋ⟨shareKey⟩ (a1, k, a2)
def encryptOp (m : BANForm Message) (k : BANForm Key) := ℋ⟨encrypt⟩ (m, k)
def believeOp (a : BANForm Agent) (φ : BANForm Formula) : BANForm Formula := ℋ⟨believes⟩ (a, φ)
def mtofOp (m : BANForm Message) : BANForm Formula := ℋ⟨mtof⟩ (m)
def oncesaidOp (a : BANForm Agent) (φ : BANForm Formula) := ℋ⟨oncesaid⟩ (a, φ)
def seesOp (a : BANForm Agent) (φ : BANForm Formula) := ℋ⟨sees⟩ (a, φ)
def nonceOp (m : BANForm Message) := ℋ⟨nonce⟩ (m)
def jurisdictionOp (a : BANForm Agent) (φ : BANForm Formula) := ℋ⟨jurisdiction⟩ (a, φ)

notation "⦃" m "⦄" k => encryptOp m k

notation a " |≡ " φ => believeOp a φ
notation "ι" m => mtofOp m
notation a " |∼ " φ => oncesaidOp a φ
notation a " ▸ " φ => seesOp a φ
notation "#" "(" n ")" => nonceOp n
notation a " |=> " φ => jurisdictionOp a φ

example : Form BAN Message :=
  ℋ⟨shareKey⟩ (ℋNom (.ctNom ⟨"A", ⟨"A", rfl⟩⟩), ℋNom (.ctNom ⟨"123", ⟨"123", rfl⟩⟩), ℋNom (.ctNom ⟨"B", ⟨"B", rfl⟩⟩))

example : Form BAN Message :=
  ℋ⟨shareKey⟩ (ℋNom "A", ℋNom "123", ℋNom "B")

example : BANForm Message := shareKeyOp (ℋNom "A") (ℋNom "123") (ℋNom "B")

inductive Axiom : {s : Sorts} → BANForm s → Type
  | MMSK {i j : BANForm Agent} {k : BANForm Key} {m : BANForm Message}
    (h₀ : Axiom $ i |≡ ι shareKeyOp i j k)
    (h₁ : Axiom $ i ▸ ι ⦃ m ⦄k)
    : Axiom $ i |≡ j |∼ ι m
  | NV {i j : BANForm Agent} {m : BANForm Message}
    (h₀ : Axiom (i |≡ j |∼ ι m))
    (h₁ : Axiom (i |≡ #(m)))
    : Axiom (i |≡ j |≡ ι m)
  | JR {i j : BANForm Agent} {m : BANForm Message}
    (h₀ : Axiom $ i |≡ j |≡ ι m)
    (h₁ : Axiom $ i |≡ j |=> ι m)
    : Axiom $ i |≡ ι m


@[simp] def BANΛ : AxiomSet BAN := λ s => { φ | Nonempty (Axiom φ) }

def BANProof := Proof BANΛ

def pf' (i j : BANForm Agent) (k : BANForm Key) (m : BANForm Message)
  (h₀ : Axiom (i |≡ ι shareKeyOp i j k))
  (h₁ : Axiom (i ▸ ι ⦃m⦄k)) : Axiom (i |≡ j |∼ ι m) := by
  exact Axiom.MMSK h₀ h₁




-- def FormulaSort := ModalBase.WFF
