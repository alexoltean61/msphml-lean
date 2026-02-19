import Hybrid.BNF
import Hybrid.Language

hybrid_def Protocols :=
  sort Agent   ::= builtin String
  sort Key     ::= builtin String
  sort Msg     ::= "pk"(Agent)                [pk]
  sort Msg     ::= "sk"(Agent)                [sk]
  sort Msg     ::= builtin String
  sort Msg     ::= "(_,_)"(Msg, Msg)          [pair]
  sort Msg     ::= "⦃_⦄_"(Msg, Msg)           [encryption]
  sort Act     ::= builtin String
  sort Act     ::= "send"(Agent, Agent, Msg)  [send]
  sort Act     ::= "recv"(Agent, Msg)         [recv]
  sort Act     ::= "_;_"(Act, Act)            [seq]
  sort StNom   ::= "◁"(Agent, Msg)           [explicit]
  sort StNom   ::= "⊔"(StNom, StNom)          [comp]
  sort St      ::= builtin String
  sort Prot    ::= builtin String
  sort Prot    ::= "𝔹"(Agent, Prot)           [believe]
  sort Prot    ::= "⟪_⟫"(StNom)               [config]
  sort Prot    ::= "[_]_"(Act, Prot)          [action]
  sort Prot    ::= "𝕏"(Agent, Msg)            [explicitKnowledge]

open Protocols

@[coe]
def String.toCtNom (str : String) : Protocols.CtNoms Protocols.Agent := ⟨str, ⟨str, rfl⟩⟩
@[coe]
def String.toCtNom' (str : String) : Protocols.CtNoms Protocols.Key := ⟨str, ⟨str, rfl⟩⟩
@[coe]
def String.toCtNom'' (str : String) : Protocols.CtNoms Protocols.Msg := ⟨str, ⟨str, rfl⟩⟩
@[coe]
def String.toCtNom''' (str : String) : Protocols.CtNoms Protocols.Act := ⟨str, ⟨str, rfl⟩⟩
@[coe]
def String.toCtNom'''' (str : String) : Protocols.CtNoms Protocols.St := ⟨str, ⟨str, rfl⟩⟩
@[coe]
def String.toCtNom''''' (str : String) : Protocols.CtNoms Protocols.Prot := ⟨str, ⟨str, rfl⟩⟩

instance : Coe String (Protocols.CtNoms Protocols.Agent) where
  coe := String.toCtNom

instance : Coe String (Protocols.CtNoms Protocols.Key) where
  coe := String.toCtNom'

instance : Coe String (Protocols.CtNoms Protocols.Msg) where
  coe := String.toCtNom''

instance : Coe String (Protocols.CtNoms Protocols.Act) where
  coe := String.toCtNom'''

instance : Coe String (Protocols.CtNoms Protocols.St) where
  coe := String.toCtNom''''

instance : Coe String (Protocols.CtNoms Protocols.Prot) where
  coe := String.toCtNom'''''

def ProtocolsForm := Form Protocols

def pkOp (a : ProtocolsForm Agent) : ProtocolsForm Msg := ℋ⟨pk⟩ (a)
def skOp (a : ProtocolsForm Agent) : ProtocolsForm Msg := ℋ⟨sk⟩ (a)

def pairOp (m₁ m₂ : ProtocolsForm Msg) : ProtocolsForm Msg := ℋ⟨pair⟩ (m₁, m₂)
def encryptionOp (m : ProtocolsForm Msg) (k : ProtocolsForm Msg) : ProtocolsForm Msg := ℋ⟨encryption⟩ (m, k)

def sendOp (a₁ a₂ : ProtocolsForm Agent) (m : ProtocolsForm Msg) : ProtocolsForm Act := ℋ⟨send⟩ (a₁, a₂, m)
def recvOp (a : ProtocolsForm Agent) (m : ProtocolsForm Msg) : ProtocolsForm Act := ℋ⟨recv⟩ (a, m)
def seqOp (α₁ α₂ : ProtocolsForm Act) : ProtocolsForm Act := ℋ⟨seq⟩ (α₁, α₂)

def explicitOp (a : ProtocolsForm Agent) (m : ProtocolsForm Msg) : ProtocolsForm StNom := ℋ⟨explicit⟩ (a, m)
def compOp (γ₁ γ₂ : ProtocolsForm StNom) : ProtocolsForm StNom := ℋ⟨comp⟩ (γ₁, γ₂)

def believeOp (a : ProtocolsForm Agent) (p : ProtocolsForm Prot) := ℋ⟨believe⟩ᵈ (a, p)
def configOp (st : ProtocolsForm StNom) := ℋ⟨config⟩ (st)
def actionOp (a : ProtocolsForm Act) (p : ProtocolsForm Prot) := ℋ⟨action⟩ᵈ (a, p)
def explicitKnowledgeOp (a : ProtocolsForm Agent) (m : ProtocolsForm Msg) := ℋ⟨explicitKnowledge⟩ (a, m)

notation "pk(" k ")" => pkOp k
notation "sk(" k ")" => skOp k

notation m₁ " ‖ " m₂ => pairOp m₁ m₂
notation "⦃ " m " ⦄" k => encryptionOp m k

notation "send " a₁ ", " a₂ "(" m ")" => sendOp a₁ a₂ m
notation "recv " a "(" m ")" => recvOp a m
notation α₁ " ; " α₂ => seqOp α₁ α₂

notation a " ◁ " m => explicitOp a m
notation γ₁ " ⊔ " γ₂ => compOp γ₁ γ₂

notation " 𝔹 " a ", " p => believeOp a p
notation " ⟪ " γ " ⟫ " => configOp γ
notation "[" α "]" p => actionOp α p
notation "𝕏 " a ", " p => explicitKnowledgeOp a p

notation "𝕂 " a ", " p => 𝔹 a, p ⋀ p
