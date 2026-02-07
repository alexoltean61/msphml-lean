import Hybrid.Language.Form
import Hybrid.Language.Substitution

namespace FormL

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}

def VarList (symbs : Symbols α) := List ((s : symbs.signature.S) × symbs.svar s)
def NomList (symbs : Symbols α) := List ((s : symbs.signature.S) × symbs.nominal s)

def VarList.remove (l : VarList symbs) (x : (s : symbs.signature.S) × symbs.svar s) : VarList symbs := l.filter (λ ⟨s', x'⟩ => s' != x.1 || x'.1 != x.2.1)

def existClosure (φ : Form symbs s) (vars : VarList symbs) : Form symbs s :=
  vars.foldr (λ ⟨_, x⟩ φacc => ℋ∃ x φacc) φ

def univClosure (φ : Form symbs s) (vars : VarList symbs) : Form symbs s :=
  vars.foldr (λ ⟨_, x⟩ φacc => ℋ∀ x φacc) φ

/--
  Free variables of a formula, given as a list of pairs ⟨sort, variable⟩.
-/
@[simp]
def FV : FormL symbs ss → VarList symbs
  | @FormL.svar  _ _ s x   =>
      [⟨s, x⟩]
  | @FormL.bind _ _ s _ x φ =>
      φ.FV.remove ⟨s, x⟩
  | ℋ⟨_⟩ φ  => φ.FV
  | ∼ φ     => φ.FV
  | ℋ@ _ φ => φ.FV
  | (φ, ψ)   => (φ.FV.append ψ.FV).dedup
  | φ ⋁ ψ   => (φ.FV.append ψ.FV).dedup
  | _ => []

@[simp]
def closed (φ : FormL symbs ss) := φ.FV = []

def Instantiation (symbs : Symbols α) := List ((s : symbs.signature.S) × symbs.svar s × symbs.nominal s)

@[simp]
def Instantiation.apply (φ : FormL symbs ss) : Instantiation symbs → FormL symbs ss
  | []                   => φ
  | ⟨_, x, k⟩ :: i' => (Instantiation.apply φ i')[k // x]

structure Instance (φ : FormL symbs ss) where
  inst   : Instantiation symbs

abbrev Instance.form {φ : FormL symbs ss} (ψ : Instance φ) : FormL symbs ss := ψ.inst.apply φ

notation:100 "ℋ∃cl " xs φ => existClosure φ xs
notation:100 "ℋ∀cl " xs φ => univClosure φ xs

end FormL

def ClosedFormL [DecidableEq α] (symbs : Symbols α) (ss) :=
  Subtype (λ (φ : FormL symbs ss) => φ.closed)
def ClosedForm [DecidableEq α] (symbs : Symbols α) (s : symbs.signature.S) :=
  ClosedFormL symbs ([s])
