import Hybrid.Proof.Hilbert

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {Λ : AxiomSet symbs}

def Fragment (symbs : Symbols α) := (ss : List symbs.signature.S) → FormL symbs ss → Bool

structure FormL.fragment (P : Fragment symbs) (ss : List symbs.signature.S) where
  form   : FormL symbs ss
  inFrag : P _ form

def Form.fragment (P : Fragment symbs) (s : symbs.signature.S) :=
    FormL.fragment P ([s])

def Proof.inFragment (P : Fragment symbs) : Proof Λ s φ → Bool := λ pf =>
    P _ φ &&
        match pf with
        | mp pf1 pf2  => pf1.inFragment P && pf2.inFragment P
        | ug _ pf     => pf.inFragment P
        | broadcastS _ pf  => pf.inFragment P
        | genAt _ _ pf     => pf.inFragment P
        | nameAt _ _ pf    => pf.inFragment P
        | paste _ _ _ _ pf => pf.inFragment P
        | gen _ pf => pf.inFragment P
        | _        => true

structure Proof.fragment (P : Fragment symbs) (Λ : AxiomSet symbs) (φ : Form symbs s) where
  pf     : Proof Λ s φ
  inFrag : pf.inFragment P

@[simp]
def Fragment.univ : Fragment symbs := λ _ _ => true

instance : Coe (FormL symbs ss) (FormL.fragment .univ ss) where
  coe φ := ⟨φ, rfl⟩

instance : Coe (Proof Λ s φ) (Proof.fragment .univ Λ φ) where
  coe pf := ⟨pf, by induction pf <;> (unfold Proof.inFragment; aesop)⟩
