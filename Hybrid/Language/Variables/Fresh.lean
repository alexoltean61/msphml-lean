import Hybrid.Language.Variables.FV

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}

namespace FormL

@[simp]
def freshVarIdx (φ : FormL symbs ss) (s : symbs.signature.S) : ℕ :=
  φ.FV.foldr (λ ⟨s', x⟩ acc => if s' != s then acc else max (1 + (symbs.svarCtbl.encode x)) acc ) 0
@[simp]
def freshVar (φ : FormL symbs ss) (s : symbs.signature.S) : symbs.svar s := φ.freshVarIdx s

end FormL

def FormLList (symbs : Symbols α) := List ((ss : List symbs.signature.S) × FormL symbs ss)

@[simp]
def FormLList.freshVarIdx (l : FormLList symbs) (s : symbs.signature.S) : ℕ :=
  l.foldr (λ ⟨_, φ⟩ acc => max (1 + φ.freshVarIdx s) acc ) 0
@[simp]
def FormLList.freshVar (l : FormLList symbs) (s : symbs.signature.S) : symbs.svar s := l.freshVarIdx s
