import Hybrid.Language.Signature
import Hybrid.Language.Form

namespace SMC

-- Define sorts:
def Sorts : Set String := {
  "Nat", "Bool", "Var", "AExp",
  "BExp", "Stmt", "Val", "ValStack",
  "Mem", "CtrlStack", "Config"
}

def SortNat  : Sorts.Elem := ⟨"Nat", Or.inl rfl⟩
def SortBool : Sorts.Elem := ⟨"Bool", Or.inr (Or.inl rfl)⟩
def SortVar  : Sorts.Elem := ⟨"Var", Or.inr (Or.inr (Or.inl rfl))⟩
def SortAExp : Sorts.Elem := ⟨"AExp", Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
def SortBExp : Sorts.Elem := ⟨"BExp", Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
def SortStmt : Sorts.Elem := ⟨"Stmt", Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
def SortVal  : Sorts.Elem := ⟨"Val", Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
def SortValStack : Sorts.Elem := ⟨"ValStack", Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))⟩
def SortMem  : Sorts.Elem := ⟨"Mem", Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))⟩
def SortCtrlStack : Sorts.Elem := ⟨"CtrlStack", Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))⟩
def SortConfig : Sorts.Elem := ⟨"Config", Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))⟩

-- Define operators:
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
    { "c" }
  else if domain = [SortBExp] ∧ range = SortCtrlStack then
    { "c" }
  else if domain = [SortStmt] ∧ range = SortCtrlStack then
    { "c" }
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

def Sig : Signature String where
  S   := Sorts
  «Σ» := Op
  N   := CtNom

  sortsCtbl := ⟨sorry, sorry, sorry⟩
  opsCtbl   := by intro _ _; unfold Op; admit
  nomCtbl   := by intro _; unfold CtNom; admit

  sNonEmpty := ⟨SortNat⟩
  nNonEmpty := sorry

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
  propCtbl := λ _ => sorry
  nomCtbl  := λ _ => sorry
  svarCtbl := λ _ => sorry

  -- == :: (SortNat, SortNat) -> SortBool
def EqNat : (Symb.signature.«Σ» [SortNat, SortNat] SortBool).Elem := ⟨"==", by simp [Symb, Sig, Op]⟩
-- <= :: (SortNat, SortNat) -> SortBool
def LEqNat : (Symb.signature.«Σ» [SortNat, SortNat] SortBool).Elem := ⟨"<=", by simp [Symb, Sig, Op]⟩

-- nat2AExp :: SortNat -> SortAExp
def nat2AExp : (Symb.signature.«Σ» [SortNat] SortAExp).Elem := ⟨"nat2AExp", by simp [Symb, Sig, Op]⟩
-- var2AExp :: SortVar -> SortAExp
def var2AExp : (Symb.signature.«Σ» [SortVar] SortAExp).Elem := ⟨"var2AExp", by simp [Symb, Sig, SortVar, SortNat, Op]⟩

-- + :: (SortAExp, SortAExp) -> SortAExp
def PlusNat : (Symb.signature.«Σ» [SortAExp, SortAExp] SortAExp).Elem := ⟨"+", by simp [Symb, Sig, SortAExp, SortNat, Op]⟩
-- ++ :: SortVar -> SortAExp
def PlusPlusVar : (Symb.signature.«Σ» [SortVar] SortAExp).Elem := ⟨"++", by simp [Symb, Sig, SortAExp, SortNat, SortVar, Op]⟩

-- <= :: (SortAExp, SortAExp) -> SortBExp
-- TODO: There is also a <= strictly between naturals, returning strictly booleans
-- Why both?
def LEqAExp : (Symb.signature.«Σ» [SortAExp, SortAExp] SortBExp).Elem := ⟨"<=", by simp [Symb, Sig, SortBExp, SortNat, SortAExp, Op]⟩

-- skip :: SortStmt
-- skip is a nominal

-- Paper states:
--  Stmt ::= x := AExp
-- Shouldn't this rather be?
--  Stmt ::= Var := AExp
--
-- := :: (SortVar, SortAExp) -> SortStmt
def AsgnStmt : (Symb.signature.«Σ» [SortVar, SortAExp] SortStmt).Elem := ⟨":=", by simp [Symb, Sig, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩
-- ite :: (SortBExp, SortStmt, SortStmt) -> SortStmt
def IteStmt : (Symb.signature.«Σ» [SortBExp, SortStmt, SortStmt] SortStmt).Elem := ⟨"ite", by simp [Symb, Sig, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩
-- seq :: (SortStmt, SortStmt) -> SortStmt
def SeqStmt : (Symb.signature.«Σ» [SortStmt, SortStmt] SortStmt).Elem := ⟨";", by simp [Symb, Sig, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩
-- while :: (SortBExp, SortStmt) -> SortStmt
def WhileStmt : (Symb.signature.«Σ» [SortBExp, SortStmt] SortStmt).Elem := ⟨"while", by simp [Symb, Sig, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩

-- nat2Val :: SortNat -> SortVal
def nat2Val : (Symb.signature.«Σ» [SortNat] SortVal).Elem := ⟨"nat2Val", by simp [Symb, Sig, SortVal, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩
-- bool2Val :: SortBool -> SortVal
def bool2Val : (Symb.signature.«Σ» [SortBool] SortVal).Elem := ⟨"bool2Val", by simp [Symb, Sig, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩

-- . :: (Val, ValStack) -> ValStack
def consValStack : (Symb.signature.«Σ» [SortVal, SortValStack] SortValStack).Elem := ⟨"·", by simp [Symb, Sig, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩
-- set :: (Mem, Var, AExp) -> Mem
def setMem : (Symb.signature.«Σ» [SortMem, SortVar, SortVal] SortMem).Elem := ⟨"set", by simp [Symb, Sig, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩

-- c :: AExp -> CtrlStack
def cAExp : (Symb.signature.«Σ» [SortAExp] SortCtrlStack).Elem := ⟨"c", by simp [Symb, Sig, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩
-- c :: BExp -> CtrlStack
def cBExp : (Symb.signature.«Σ» [SortBExp] SortCtrlStack).Elem := ⟨"c", by simp [Symb, Sig, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩
-- c :: Stmt -> CtrlStack
def cStmt : (Symb.signature.«Σ» [SortStmt] SortCtrlStack).Elem := ⟨"c", by simp [Symb, Sig, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩
-- asgn :: Var -> CtrlStack
def AsgnCtrlStack : (Symb.signature.«Σ» [SortVar] SortCtrlStack).Elem := ⟨"asgn", by simp [Symb, Sig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩

-- < > :: (ValStack, Mem) -> Config
def mkConfig : (Symb.signature.«Σ» [SortValStack, SortMem] SortConfig).Elem := ⟨"< >", by simp [Symb, Sig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩

-- PDL :: (CtrlStack, Config) -> Config
def PDLOp : (Symb.signature.«Σ» [SortCtrlStack, SortConfig] SortConfig).Elem := ⟨"[ ]", by simp [Symb, Sig, SortConfig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩

-- ? ::    Val -> CtrlStack
def PDLTest : (Symb.signature.«Σ» [SortVal] SortCtrlStack).Elem := ⟨"?", by simp [Symb, Sig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩
-- seq :: (CtrlStack, CtrlStack) -> CtrlStack
def PDLSeq : (Symb.signature.«Σ» [SortCtrlStack, SortCtrlStack] SortCtrlStack).Elem := ⟨";", by simp [Symb, Sig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩

-- PDLUnion :: (CtrlStack, CtrlStack) -> CtrlStack
def PDLUnion : (Symb.signature.«Σ» [SortCtrlStack, SortCtrlStack] SortCtrlStack).Elem := ⟨"∪", by simp [Symb, Sig, SortConfig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩

-- PDLStar :: (CtrlStack) -> CtrlStack
def PDLStar : (Symb.signature.«Σ» [SortCtrlStack] SortCtrlStack).Elem := ⟨"*", by simp [Symb, Sig, SortConfig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, Op]⟩

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
-- Help: you can mix up cAExp, CBexp, cStmt anyway you want here
-- The type checker doesn't mind.
-- But why?
instance : Evaluable (SMCForm SortAExp) where
  ctrlStackEval := FormL.appl cAExp
instance : Evaluable (SMCForm SortBExp) where
  ctrlStackEval := FormL.appl cBExp
instance : Evaluable (SMCForm SortStmt) where
  ctrlStackEval := FormL.appl cAExp
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

def plus : SMCForm SortCtrlStack := ℋNom (.ctNom ⟨"plus", by simp [Symb, Sig, CtNom, SortCtrlStack, SortNat, SortBool, SortStmt, SortValStack, SortMem]⟩)
notation:100 "plus" => plus

def leq : SMCForm SortCtrlStack := ℋNom (.ctNom ⟨"leq", by simp [Symb, Sig, CtNom, SortCtrlStack, SortNat, SortBool, SortStmt, SortValStack, SortMem]⟩)
notation:100 "leq" => leq

def skip : SMCForm SortCtrlStack := ℋNom (.ctNom ⟨"skip", by simp [Symb, Sig, CtNom, SortCtrlStack, SortNat, SortBool, SortStmt, SortValStack, SortMem]⟩)
notation:100 "skip" => skip

end SMC
