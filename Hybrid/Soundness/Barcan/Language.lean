import Aesop
import Hybrid.Semantics

-- First, define the language.

-- Define sorts:
def sorts : Set String := { "S" }
def sortS : sorts.Elem := ⟨ "S", rfl ⟩

-- Define operators:
def ops : List sorts → sorts → Set String := λ domain range =>
  if domain = [sortS, sortS] ∧ range = sortS then
    { "σ" }
  else { }

def signature : Signature String where
  S   := sorts
  Sig := ops
  N   := λ _ => { }

  sortsCtbl := by simp [sorts]
  opsCtbl   := by intro _ _; unfold ops; aesop
  nomCtbl   := by aesop

  sNonEmpty := ⟨sortS⟩

def sig : signature.Sig [sortS, sortS] sortS := ⟨"σ", by unfold signature ; unfold ops ; aesop⟩

def symbs : Symbols String where
  signature := signature
  prop := λ _ => { "p" }
  nom  := λ _ => { "j", "k" }
  svar := λ _ => { "x" }
  propCtbl := λ _ => by aesop
  nomCtbl  := λ _ => by aesop
  svarCtbl := λ _ => by aesop

  propNonEmpty := λ _ => ⟨"p", by aesop⟩

def j : symbs.nom sortS  := ⟨"j", by simp [symbs]⟩
def k : symbs.nom sortS  := ⟨"k", by simp [symbs]⟩
def x : symbs.svar sortS := ⟨"x", by simp [symbs]⟩
