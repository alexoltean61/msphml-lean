import Hybrid.Language.Variables.Substitution

namespace FormL

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}

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
