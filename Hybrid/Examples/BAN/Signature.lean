import Hybrid.BNF
import Hybrid.Language
import Hybrid.Proof

hybrid_def BAN :=
  sort Agent   ::= builtin String
  sort Message ::= builtin String
  sort Message ::= "<->"(Agent, Message, Agent) [shareKey]
  sort Message ::= "enc"(Message, Message)      [encrypt]
  sort Message ::= "pair"(Message, Message)     [pair]
  sort Message ::= "pk"(Agent)                  [pk]
  sort Message ::= "sk"(Agent)                  [sk]
  sort Nonce   ::= subsort Message
  sort Formula ::= builtin String
  sort Formula ::= "|≡"(Agent, Formula)         [believes]
  sort Formula ::= "ι"(Message)                 [mtof]
  sort Formula ::= "|~"(Agent, Formula)         [oncesaid]
  sort Formula ::= "◁"(Agent, Formula)          [sees]
  sort Formula ::= "#"(Message)                 [nonce]
  sort Formula ::= "|=>"(Agent, Formula)        [jurisdiction]

namespace BAN

@[coe]
def String.toCtNom (str : String) : BAN.CtNoms BAN.Agent := ⟨str, ⟨str, rfl⟩⟩
@[coe]
def String.toCtNom' (str : String) : BAN.CtNoms BAN.Formula := ⟨str, ⟨str, rfl⟩⟩
@[coe]
def String.toCtNom'' (str : String) : BAN.CtNoms BAN.Message := ⟨str, ⟨str, rfl⟩⟩

instance : Coe String (BAN.CtNoms BAN.Agent) where
  coe := String.toCtNom

instance : Coe String (BAN.CtNoms BAN.Formula) where
  coe := String.toCtNom'

instance : Coe String (BAN.CtNoms BAN.Message) where
  coe := String.toCtNom''

def BANForm := Form BAN

def shareKeyOp (a1 a2 : BANForm Agent) (k : BANForm Message) : BANForm Message := ℋ⟨shareKey⟩ (a1, k, a2)
def encryptOp (m k : BANForm Message) := ℋ⟨encrypt⟩ (m, k)
def pairOp (m₁ : BANForm Message) (m₂ : BANForm Message) := ℋ⟨pair⟩ (m₁, m₂)
def pkOp (a : BANForm Agent) := ℋ⟨pk⟩ (a)
def skOp (a : BANForm Agent) := ℋ⟨sk⟩ (a)

def believeOp (a : BANForm Agent) (φ : BANForm Formula) : BANForm Formula := ℋ⟨believes⟩ (a, φ)
def mtofOp (m : BANForm Message) : BANForm Formula := ℋ⟨mtof⟩ (m)
def oncesaidOp (a : BANForm Agent) (φ : BANForm Formula) := ℋ⟨oncesaid⟩ (a, φ)
def seesOp (a : BANForm Agent) (φ : BANForm Formula) := ℋ⟨sees⟩ (a, φ)
def nonceOp (m : BANForm Message) := ℋ⟨nonce⟩ (m)
def jurisdictionOp (a : BANForm Agent) (φ : BANForm Formula) := ℋ⟨jurisdiction⟩ (a, φ)

notation "pk(" a ")" => pkOp a
notation "sk(" a ")" => skOp a

notation "⦃" m "⦄" k => encryptOp m k
notation "c(" m₁ "," m₂ ")" => pairOp m₁ m₂

notation a " |≡ " φ => believeOp a φ
notation "ι" m => mtofOp m
notation a " |∼ " φ => oncesaidOp a φ
notation a " ◁ " φ => seesOp a φ
notation "#" "(" n ")" => nonceOp n
notation a " |=> " φ => jurisdictionOp a φ
