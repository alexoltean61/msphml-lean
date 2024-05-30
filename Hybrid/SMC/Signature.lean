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
def SMCOp : List Sorts → Sorts → Set String := λ domain range =>
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
    { ";" }
  else if domain = [SortValStack, SortMem] ∧ range = SortConfig then
    { "< >" } -- Configuration symbol; should find something better
  else if domain = [SortCtrlStack, SortConfig] ∧ range = SortConfig then
    { "[ ]" } -- PDL-inspired symbol; should find something better
  else { }

def SMCCtNom : Sorts → Set String := λ s =>
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
  else { }

def SMCSig : Signature String where
  S   := Sorts
  Sig := SMCOp
  N   := SMCCtNom

  sortsCtbl := by simp [Sorts]
  opsCtbl   := by intro _ _; unfold SMCOp; admit
  nomCtbl   := by intro _; unfold SMCCtNom; admit

  sNonEmpty := ⟨SortNat⟩

def SMCSymb : Symbols String where
  signature := SMCSig
  prop := λ _ => { "p" }
  nom  := λ s =>
      if s = SortVar then
      -- Temporarily accept all strings as valid
      -- variable names. Ideally this should be a more restricted
      -- grammar:
      { s | s = s }
    else { }
  svar := λ _ => { s | ∃ n : ℕ, s = "x" ++ n.repr }
  propCtbl := λ _ => by simp only [Set.countable_singleton]
  nomCtbl  := λ _ => sorry
  svarCtbl := λ _ => by
    simp [Set.countable_iff_exists_injective]
    apply Exists.intro
    · admit
    · intro ⟨_, hex⟩

      admit

  propNonEmpty := λ _ => ⟨"p", rfl⟩


  -- == :: (SortNat, SortNat) -> SortBool
def EqNat : (SMCSymb.signature.Sig [SortNat, SortNat] SortBool).Elem := ⟨"==", by simp [SMCSymb, SMCSig, SMCOp]⟩
-- <= :: (SortNat, SortNat) -> SortBool
def LEqNat : (SMCSymb.signature.Sig [SortNat, SortNat] SortBool).Elem := ⟨"<=", by simp [SMCSymb, SMCSig, SMCOp]⟩

-- nat2AExp :: SortNat -> SortAExp
def nat2AExp : (SMCSymb.signature.Sig [SortNat] SortAExp).Elem := ⟨"nat2AExp", by simp [SMCSymb, SMCSig, SMCOp]⟩
-- var2AExp :: SortVar -> SortAExp
def var2AExp : (SMCSymb.signature.Sig [SortVar] SortAExp).Elem := ⟨"var2AExp", by simp [SMCSymb, SMCSig, SortVar, SortNat, SMCOp]⟩

-- + :: (SortAExp, SortAExp) -> SortAExp
def PlusNat : (SMCSymb.signature.Sig [SortAExp, SortAExp] SortAExp).Elem := ⟨"+", by simp [SMCSymb, SMCSig, SortAExp, SortNat, SMCOp]⟩
-- ++ :: SortVar -> SortAExp
def PlusPlusVar : (SMCSymb.signature.Sig [SortVar] SortAExp).Elem := ⟨"++", by simp [SMCSymb, SMCSig, SortAExp, SortNat, SortVar, SMCOp]⟩

-- <= :: (SortAExp, SortAExp) -> SortBExp
-- TODO: There is also a <= strictly between naturals, returning strictly booleans
-- Why both?
def LEqAExp : (SMCSymb.signature.Sig [SortAExp, SortAExp] SortBExp).Elem := ⟨"<=", by simp [SMCSymb, SMCSig, SortBExp, SortNat, SortAExp, SMCOp]⟩

-- skip :: SortStmt
-- skip is a nominal

-- Paper states:
--  Stmt ::= x := AExp
-- Shouldn't this rather be?
--  Stmt ::= Var := AExp
--
-- := :: (SortVar, SortAExp) -> SortStmt
def AsgnStmt : (SMCSymb.signature.Sig [SortVar, SortAExp] SortStmt).Elem := ⟨":=", by simp [SMCSymb, SMCSig, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩
-- ite :: (SortBExp, SortStmt, SortStmt) -> SortStmt
def IteStmt : (SMCSymb.signature.Sig [SortBExp, SortStmt, SortStmt] SortStmt).Elem := ⟨"ite", by simp [SMCSymb, SMCSig, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩
-- seq :: (SortStmt, SortStmt) -> SortStmt
def SeqStmt : (SMCSymb.signature.Sig [SortStmt, SortStmt] SortStmt).Elem := ⟨";", by simp [SMCSymb, SMCSig, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩
-- while :: (SortBExp, SortStmt) -> SortStmt
def WhileStmt : (SMCSymb.signature.Sig [SortBExp, SortStmt] SortStmt).Elem := ⟨"while", by simp [SMCSymb, SMCSig, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩

-- nat2Val :: SortNat -> SortVal
def nat2Val : (SMCSymb.signature.Sig [SortNat] SortVal).Elem := ⟨"nat2Val", by simp [SMCSymb, SMCSig, SortVal, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩
-- bool2Val :: SortBool -> SortVal
def bool2Val : (SMCSymb.signature.Sig [SortBool] SortVal).Elem := ⟨"bool2Val", by simp [SMCSymb, SMCSig, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩

-- . :: (Val, ValStack) -> ValStack
def consValStack : (SMCSymb.signature.Sig [SortVal, SortValStack] SortValStack).Elem := ⟨"·", by simp [SMCSymb, SMCSig, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩
-- set :: (Mem, Var, AExp) -> Mem
def setMem : (SMCSymb.signature.Sig [SortMem, SortVar, SortVal] SortMem).Elem := ⟨"set", by simp [SMCSymb, SMCSig, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩

-- c :: AExp -> CtrlStack
def cAExp : (SMCSymb.signature.Sig [SortAExp] SortCtrlStack).Elem := ⟨"c", by simp [SMCSymb, SMCSig, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩
-- c :: BExp -> CtrlStack
def cBExp : (SMCSymb.signature.Sig [SortBExp] SortCtrlStack).Elem := ⟨"c", by simp [SMCSymb, SMCSig, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩
-- c :: Stmt -> CtrlStack
def cStmt : (SMCSymb.signature.Sig [SortStmt] SortCtrlStack).Elem := ⟨"c", by simp [SMCSymb, SMCSig, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩
-- asgn :: Var -> CtrlStack
def AsgnCtrlStack : (SMCSymb.signature.Sig [SortVar] SortCtrlStack).Elem := ⟨"asgn", by simp [SMCSymb, SMCSig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩
-- ? ::    Val -> CtrlStack
def TestCtrlStack : (SMCSymb.signature.Sig [SortVal] SortCtrlStack).Elem := ⟨"?", by simp [SMCSymb, SMCSig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩
-- seq :: (CtrlStack, CtrlStack) -> CtrlStack
def SeqCtrlStack : (SMCSymb.signature.Sig [SortCtrlStack, SortCtrlStack] SortCtrlStack).Elem := ⟨";", by simp [SMCSymb, SMCSig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩

-- < > :: (ValStack, Mem) -> Config
def mkConfig : (SMCSymb.signature.Sig [SortValStack, SortMem] SortConfig).Elem := ⟨"< >", by simp [SMCSymb, SMCSig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩

-- PDL :: (CtrlStack, Config) -> Config
def PDLOp : (SMCSymb.signature.Sig [SortCtrlStack, SortConfig] SortConfig).Elem := ⟨"[ ]", by simp [SMCSymb, SMCSig, SortConfig, SortCtrlStack, SortValStack, SortVal, SortBool, SortBExp, SortNat, SortAExp, SortVar, SortStmt, SMCOp]⟩

abbrev SMCFormL := FormL SMCSymb
abbrev SMCForm  := Form SMCSymb

instance : Coe ℕ (SMCForm SortNat) where
  coe := λ n => ℋNom (Sum.inl ⟨n.repr, ⟨n, rfl⟩⟩)
instance : Coe Bool (SMCForm SortBool) where
  coe := λ b =>
    match b with
    | true => ℋNom (Sum.inl ⟨"true", by simp [SMCSymb, SMCSig, SMCCtNom, SortBool, SortNat]⟩)
    | false => ℋNom (Sum.inl ⟨"false", by simp [SMCSymb, SMCSig, SMCCtNom, SortBool, SortNat]⟩)
instance : Coe (SMCForm SortNat) (SMCForm SortAExp) where
  coe := λ n => ℋ⟨nat2AExp⟩ n
instance : Coe (SMCForm SortNat) (SMCForm SortVal) where
  coe := λ n => ℋ⟨nat2Val⟩ n
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
  seq := λ c1 c2 => FormL.appl SeqCtrlStack (FormL.cons c1 c2)

notation:100 s1:99 ";" s2:100 => HasSeq.seq s1 s2
notation:100 "c" "(" φ:100 ")" => Evaluable.ctrlStackEval φ
notation:100 "⟨" vs ", " mem "⟩" => ℋ⟨mkConfig⟩ (vs, mem)
notation:100 "[" ctrl "]" config => ℋ⟨PDLOp⟩ (ctrl, config)
notation:100 v:99 "⬝" vs:100 => ℋ⟨consValStack⟩ (v, vs)
notation:100 "set" "(" mem ", "  x ", "  n ")" => ℋ⟨setMem⟩ (mem, x, n)
notation:100 "++" x:100 => ℋ⟨PlusPlusVar⟩ x
notation:100 a1:99 "+Nat" a2:100 => ℋ⟨PlusNat⟩ (a1, a2)
notation:100 a1:99 "<=AExp" a2:100 => ℋ⟨LEqAExp⟩ (a1, a2)

def plus : SMCForm SortCtrlStack := ℋNom (Sum.inl ⟨"plus", by simp [SMCSymb, SMCSig, SMCCtNom, SortCtrlStack, SortNat, SortBool, SortStmt, SortValStack, SortMem]⟩)
notation:100 "plus" => plus

def leq : SMCForm SortCtrlStack := ℋNom (Sum.inl ⟨"leq", by simp [SMCSymb, SMCSig, SMCCtNom, SortCtrlStack, SortNat, SortBool, SortStmt, SortValStack, SortMem]⟩)
notation:100 "leq" => leq

def skip : SMCForm SortCtrlStack := ℋNom (Sum.inl ⟨"skip", by simp [SMCSymb, SMCSig, SMCCtNom, SortCtrlStack, SortNat, SortBool, SortStmt, SortValStack, SortMem]⟩)
notation:100 "skip" => skip

end SMC
