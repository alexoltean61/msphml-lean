import Hybrid.Language.Signature
import Hybrid.Language.Form

namespace SMC

-- Define sorts:
abbrev Sorts : Set String := {
  "Nat", "Bool", "Var", "AExp",
  "BExp", "Stmt", "Val", "ValStack",
  "Mem", "CtrlStack", "Config"
}

abbrev SortNat  : Sorts.Elem := ⟨"Nat",  by aesop⟩
abbrev SortBool : Sorts.Elem := ⟨"Bool", by aesop⟩
abbrev SortVar  : Sorts.Elem := ⟨"Var",  by aesop⟩
abbrev SortAExp : Sorts.Elem := ⟨"AExp", by aesop⟩
abbrev SortBExp : Sorts.Elem := ⟨"BExp", by aesop⟩
abbrev SortStmt : Sorts.Elem := ⟨"Stmt", by aesop⟩
abbrev SortVal  : Sorts.Elem := ⟨"Val",  by aesop⟩
abbrev SortValStack : Sorts.Elem := ⟨"ValStack",   by aesop⟩
abbrev SortMem  : Sorts.Elem := ⟨"Mem",  by aesop⟩
abbrev SortCtrlStack : Sorts.Elem := ⟨"CtrlStack", by aesop⟩
abbrev SortConfig : Sorts.Elem := ⟨"Config", by aesop⟩

-- Define operators:
@[simp]
def Op : List Sorts → Sorts → Set String := λ domain range =>
  if domain = [SortNat, SortNat] ∧ range = SortBool then
    { "==", "<=" }
  else if domain = [SortNat] ∧ range = SortAExp then
    { "nat2AExp" }
  else if domain = [SortAExp, SortAExp] ∧ range = SortAExp then
    { "+" }
  else if domain = [SortVar] ∧ range = SortAExp then
    { "++", "var2AExp" }
  else if domain = [SortAExp, SortAExp] ∧ range = SortBExp then
    { "<=" }
  else if domain = [SortVar, SortAExp] ∧ range = SortStmt then
    { ":=" }
  else if domain = [SortBExp, SortStmt, SortStmt] ∧ range = SortStmt then
    { "ite" }
  else if domain = [SortStmt, SortStmt] ∧ range = SortStmt then
    { ";" }
  else if domain = [SortBExp, SortStmt] ∧ range = SortStmt then
    { "while" }
  else if domain = [SortNat] ∧ range = SortVal then
    { "nat2Val" }
  else if domain = [SortBool] ∧ range = SortVal then
    { "bool2Val" }
  else if domain = [SortVal, SortValStack] ∧ range = SortValStack then
    { "·" }
  else if domain = [SortMem, SortVar, SortVal] ∧ range = SortMem then
    { "set" }
  else if domain = [SortAExp] ∧ range = SortCtrlStack then
    { "cAExp" }
  else if domain = [SortBExp] ∧ range = SortCtrlStack then
    { "cBExp" }
  else if domain = [SortStmt] ∧ range = SortCtrlStack then
    { "cStmt" }
  else if domain = [SortVar] ∧ range = SortCtrlStack then
    { "asgn" }
  else if domain = [SortVal] ∧ range = SortCtrlStack then
    { "?" }
  else if domain = [SortCtrlStack, SortCtrlStack] ∧ range = SortCtrlStack then
    { ";", "∪" } -- PDL-inspired symbols
  else if domain = [SortCtrlStack] ∧ range = SortCtrlStack then
    { "*" } -- PDL-inspired symbol
  else if domain = [SortValStack, SortMem] ∧ range = SortConfig then
    { "< >" } -- Configuration symbol; should find something better
  else if domain = [SortCtrlStack, SortConfig] ∧ range = SortConfig then
    { "[ ]" } -- PDL-inspired symbol; should find something better
  else { }

@[simp]
def CtNom : Sorts → Set String := λ s =>
  if s = SortNat then
    -- All natural numbers, as strings:
    { s | ∃ n : ℕ, s = n.repr }
    -- Alternative: try s.isNat
  else if s = SortBool then
    { "true", "false" }
  else if s = SortStmt then
    { "skip" }
  else if s = SortValStack then
    { "nil" }
  else if s = SortMem then
    { "empty" }
  else if s = SortCtrlStack then
    { "plus", "leq", "skip" }
  else { "n" }

@[simp]
def Sig : Signature String where
  S   := Sorts
  «Σ» := Op
  N   := CtNom

  sortsCtbl := sorry -- explicit encoding of sorts to ℕ; todo
  opsCtbl   := sorry -- explicit encoding of ops to ℕ; todo
  nomCtbl   := sorry -- explicit encoding of ctNoms to ℕ; todo

  sNonEmpty := ⟨SortNat⟩
  nNonEmpty := sorry -- constant nominals inhabited; todo

@[simp]
def Symb : Symbols String where
  signature := Sig
  prop := λ _ => { "p" }
  nom  := λ s =>
      if s = SortVar then
      -- Temporarily accept all strings as valid
      -- variable names. Ideally this should be a more restricted
      -- grammar:
      { s | s = s }
    else { }
  svar := λ _ => { s | ∃ n : ℕ, s = "x" ++ n.repr }
  propCtbl := sorry  -- explicit encoding of props to ℕ; todo
  nomCtbl  := sorry  -- explicit encoding of noms to ℕ; todo
  svarCtbl := sorry  -- explicit encoding of vars to ℕ; todo
  nomExt   := sorry  -- extension set of nominals; needed for completenes; todo
  hExtInf  := sorry  -- nomExt is countable; needed for completeness; todo
  hExtDisj := sorry  -- nomExt can be partitioned in two countable sets; needed for completeness; todo

  -- == :: (SortNat, SortNat) -> SortBool
def EqNat : (Symb.signature.«Σ» [SortNat, SortNat] SortBool).Elem := ⟨"==", by aesop⟩
-- <= :: (SortNat, SortNat) -> SortBool
def LEqNat : (Symb.signature.«Σ» [SortNat, SortNat] SortBool).Elem := ⟨"<=", by aesop⟩

-- nat2AExp :: SortNat -> SortAExp
def nat2AExp : (Symb.signature.«Σ» [SortNat] SortAExp).Elem := ⟨"nat2AExp", by aesop⟩
-- var2AExp :: SortVar -> SortAExp
def var2AExp : (Symb.signature.«Σ» [SortVar] SortAExp).Elem := ⟨"var2AExp", by aesop⟩

-- + :: (SortAExp, SortAExp) -> SortAExp
def PlusNat : (Symb.signature.«Σ» [SortAExp, SortAExp] SortAExp).Elem := ⟨"+", by aesop⟩
-- ++ :: SortVar -> SortAExp
def PlusPlusVar : (Symb.signature.«Σ» [SortVar] SortAExp).Elem := ⟨"++", by aesop⟩

-- <= :: (SortAExp, SortAExp) -> SortBExp
-- TODO: There is also a <= strictly between naturals, returning strictly booleans
-- Why both?
def LEqAExp : (Symb.signature.«Σ» [SortAExp, SortAExp] SortBExp).Elem := ⟨"<=", by aesop⟩

-- skip :: SortStmt
-- skip is a nominal

-- Paper states:
--  Stmt ::= x := AExp
-- Shouldn't this rather be?
--  Stmt ::= Var := AExp
--
-- := :: (SortVar, SortAExp) -> SortStmt
def AsgnStmt : (Symb.signature.«Σ» [SortVar, SortAExp] SortStmt).Elem := ⟨":=", by aesop⟩
-- ite :: (SortBExp, SortStmt, SortStmt) -> SortStmt
def IteStmt : (Symb.signature.«Σ» [SortBExp, SortStmt, SortStmt] SortStmt).Elem := ⟨"ite", by aesop⟩
-- seq :: (SortStmt, SortStmt) -> SortStmt
def SeqStmt : (Symb.signature.«Σ» [SortStmt, SortStmt] SortStmt).Elem := ⟨";", by aesop⟩
-- while :: (SortBExp, SortStmt) -> SortStmt
def WhileStmt : (Symb.signature.«Σ» [SortBExp, SortStmt] SortStmt).Elem := ⟨"while", by aesop⟩

-- nat2Val :: SortNat -> SortVal
def nat2Val : (Symb.signature.«Σ» [SortNat] SortVal).Elem := ⟨"nat2Val", by aesop⟩
-- bool2Val :: SortBool -> SortVal
def bool2Val : (Symb.signature.«Σ» [SortBool] SortVal).Elem := ⟨"bool2Val", by aesop⟩

-- . :: (Val, ValStack) -> ValStack
def consValStack : (Symb.signature.«Σ» [SortVal, SortValStack] SortValStack).Elem := ⟨"·", by aesop⟩
-- set :: (Mem, Var, AExp) -> Mem
def setMem : (Symb.signature.«Σ» [SortMem, SortVar, SortVal] SortMem).Elem := ⟨"set", by aesop⟩

-- c :: AExp -> CtrlStack
def cAExp : (Symb.signature.«Σ» [SortAExp] SortCtrlStack).Elem := ⟨"cAExp", by aesop⟩
-- c :: BExp -> CtrlStack
def cBExp : (Symb.signature.«Σ» [SortBExp] SortCtrlStack).Elem := ⟨"cBExp", by aesop⟩

-- c :: Stmt -> CtrlStack
def cStmt : (Symb.signature.«Σ» [SortStmt] SortCtrlStack).Elem := ⟨"cStmt", by aesop⟩
-- asgn :: Var -> CtrlStack
def AsgnCtrlStack : (Symb.signature.«Σ» [SortVar] SortCtrlStack).Elem := ⟨"asgn", by aesop⟩

-- < > :: (ValStack, Mem) -> Config
def mkConfig : (Symb.signature.«Σ» [SortValStack, SortMem] SortConfig).Elem := ⟨"< >", by aesop⟩

-- PDL :: (CtrlStack, Config) -> Config
def PDLOp : (Symb.signature.«Σ» [SortCtrlStack, SortConfig] SortConfig).Elem := ⟨"[ ]", by aesop⟩

-- ? ::    Val -> CtrlStack
def PDLTest : (Symb.signature.«Σ» [SortVal] SortCtrlStack).Elem := ⟨"?", by aesop⟩
-- seq :: (CtrlStack, CtrlStack) -> CtrlStack
def PDLSeq : (Symb.signature.«Σ» [SortCtrlStack, SortCtrlStack] SortCtrlStack).Elem := ⟨";", by aesop⟩

-- PDLUnion :: (CtrlStack, CtrlStack) -> CtrlStack
def PDLUnion : (Symb.signature.«Σ» [SortCtrlStack, SortCtrlStack] SortCtrlStack).Elem := ⟨"∪", by aesop⟩

-- PDLStar :: (CtrlStack) -> CtrlStack
def PDLStar : (Symb.signature.«Σ» [SortCtrlStack] SortCtrlStack).Elem := ⟨"*", by aesop⟩

abbrev SMCFormL := FormL Symb
abbrev SMCForm  := Form Symb

instance : Coe ℕ (SMCForm SortNat) where
  coe := λ n => ℋNom (.ctNom ⟨n.repr, ⟨n, rfl⟩⟩)
instance : Coe Bool (SMCForm SortBool) where
  coe := λ b =>
    match b with
    | true => ℋNom (.ctNom  ⟨"true", by simp [Symb, Sig, CtNom, SortBool, SortNat]⟩)
    | false => ℋNom (.ctNom ⟨"false", by simp [Symb, Sig, CtNom, SortBool, SortNat]⟩)
instance : Coe (SMCForm SortNat) (SMCForm SortAExp) where
  coe := λ n => ℋ⟨nat2AExp⟩ n
instance : Coe (SMCForm SortNat) (SMCForm SortVal) where
  coe := λ n => ℋ⟨nat2Val⟩ n
instance : OfNat (SMCForm SortAExp) n where
  ofNat := ℋ⟨nat2AExp⟩ n
instance : Coe (SMCForm SortVar) (SMCForm SortAExp) where
  coe := λ v => ℋ⟨var2AExp⟩ v
instance : Coe (SMCForm SortBool) (SMCForm SortVal) where
  coe := λ b => ℋ⟨bool2Val⟩ b

class Evaluable (α : Type u) where
  ctrlStackEval : α → SMCForm SortCtrlStack

instance : Evaluable (SMCForm SortAExp) where
  ctrlStackEval := FormL.appl cAExp
instance : Evaluable (SMCForm SortBExp) where
  ctrlStackEval := FormL.appl cBExp
instance : Evaluable (SMCForm SortStmt) where
  ctrlStackEval := FormL.appl cStmt
instance : Evaluable ℕ where
  ctrlStackEval := λ n => FormL.appl cAExp n
instance : Evaluable (SMCForm SortVar) where
  ctrlStackEval := λ x => FormL.appl cAExp x

class HasSeq (α : Type u) where
  seq : α → α → α
instance : HasSeq (SMCForm SortStmt) where
  seq := λ s1 s2 => FormL.appl SeqStmt (FormL.cons s1 s2)
instance : HasSeq (SMCForm SortCtrlStack) where
  seq := λ c1 c2 => FormL.appl PDLSeq (FormL.cons c1 c2)

notation:100 s1:99 ";" s2:100 => HasSeq.seq s1 s2
notation:100 "c" "(" φ:100 ")" => Evaluable.ctrlStackEval φ
notation:100 "⟨" vs ", " mem "⟩" => ℋ⟨mkConfig⟩ (vs, mem)
notation:100 "[" ctrl "]" config => ℋ⟨PDLOp⟩ (ctrl, config)
notation:100 "asgn" "(" x ")" => ℋ⟨AsgnCtrlStack⟩ x
notation:100 x:101 "::=" a:101 => ℋ⟨AsgnStmt⟩ (x, a)
notation:100 "if" bexp "then" s1 "else" s2 "endif" => ℋ⟨IteStmt⟩ (bexp, s1, s2)
notation:100 "while" bexp "do'" s => ℋ⟨WhileStmt⟩ (bexp, s)
notation:100 c1 "∪" c2 => ℋ⟨PDLUnion⟩ (c1, c2)
notation:100 c1"*" => ℋ⟨PDLStar⟩ c1
notation:100 c1"?" => ℋ⟨PDLTest⟩ c1
notation:100 v:99 "⬝" vs:100 => ℋ⟨consValStack⟩ (v, vs)
notation:100 "set" "(" mem ", "  x ", "  n ")" => ℋ⟨setMem⟩ (mem, x, n)
notation:102 "++" x:101 => ℋ⟨PlusPlusVar⟩ x
notation:102 a1:99 "+" a2:100 => ℋ⟨PlusNat⟩ (a1, a2)
notation:100 a1:99 "<=" a2:100 => ℋ⟨LEqAExp⟩ (a1, a2)

def plus : SMCForm SortCtrlStack := ℋNom (.ctNom ⟨"plus", by aesop⟩)
notation:100 "plus" => plus

def leq : SMCForm SortCtrlStack := ℋNom (.ctNom ⟨"leq", by aesop⟩)
notation:100 "leq" => leq

def skip : SMCForm SortCtrlStack := ℋNom (.ctNom ⟨"skip", by aesop⟩)
notation:100 "skip" => skip

end SMC
