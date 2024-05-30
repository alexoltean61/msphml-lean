import Hybrid.Language

/--
  Given a non-null list of sorts, and a denotation function that assignaturens a Lean type to each sort,
    `WProd` returns the product type of all sort denotations in the list.
-/
@[reducible] def WProd {signature : Signature α} (W : signature.S → Type) : List (signature.S) → Type
  -- Modal operators have at least one sort (the range sort); formulas require a non-empty list of sorts.
  -- If things are sound, the `[]` case below should never be reached. If it is reached, a term of type Empty
  -- will guarantee unsoundness.
  | []      => Empty
  | [s]     => W s
  | s :: sorts  => W s × WProd W sorts

structure Frame (signature : Signature α) where
  W  : signature.S → Type -- should you add non-empty contraint?
  R  : signature.Sig dom range → Set (WProd W (range :: dom))
  Nm : {s : signature.S} → signature.N s → W s

structure Model (symbs : Symbols α) where
  Fr  : Frame symbs.signature
  Vₚ  : symbs.prop s → Set (Fr.W s)
  Vₙ  : symbs.nom s → Fr.W s

def Model.VNom (M : Model symbs) : symbs.nominal s → M.Fr.W s
| .inl n => M.Fr.Nm n
| .inr n => M.Vₙ n

def Assignment (M : Model symbs) : Type := {s: symbs.signature.S} → symbs.svar s → M.Fr.W s

def Assignment.variant {M : Model symbs} (g' g : Assignment M) (x : symbs.svar s): Prop :=
  ∀ y : symbs.svar s, x ≠ y → g' y = g y

def Sat (M : Model symbs) (g : Assignment M) (w : WProd M.Fr.W sorts) : FormL symbs sorts → Prop
| .prop p        => w ∈ M.Vₚ p
| .nom n         => w = M.VNom n
| .svar x        => w = g x
| .appl σ arg    => ∃ w', Sat M g w' arg ∧ ⟨w, w'⟩ ∈ M.Fr.R σ -- TODO: also allow constant modal operators in the FormL definition
| .neg φ         => ¬ Sat M g w φ
| .or φ ψ        => Sat M g w φ ∨ Sat M g w ψ
| .at k φ        => let u := M.VNom k;  Sat M g u φ
| .bind x φ      => ∀ g', g'.variant g x → Sat M g' w φ
| .cons φ ψs     => Sat M g w.1 φ ∧ Sat M g w.2 ψs

notation:50 "⟨" M "," g "," w "⟩" "⊨" φ => Sat M g w φ

-- The set of worlds at which a formula is satisfied in a model, under an assignment
-- (Auxiliary, currently unneeded)
def FormL.Worlds (φ : FormL symbs sorts) (M : Model symbs) (g : Assignment M) : Set (WProd M.Fr.W sorts) :=
  λ w => Sat M g w φ

def FormL.satisfiable (φ : FormL symbs sorts) : Prop :=
  ∃ M g w, ⟨M, g, w⟩ ⊨ φ

def Model.valid (M : Model symbs) (φ : FormL symbs sorts) : Prop :=
  ∀ g w, ⟨M, g, w⟩ ⊨ φ

def Frame.valid (Fr : Frame symbs.signature) (φ : FormL symbs sorts) : Prop :=
  ∀ M g w, M.Fr = Fr → ⟨M, g, w⟩ ⊨ φ

def FormL.valid (φ : FormL symbs sorts): Prop :=
  ∀ M g w, ⟨M, g, w⟩ ⊨ φ

notation:50 M "⊨" φ => Model.valid M φ
notation:50 F "⊨" φ => Frame.valid F φ
notation:50 "⊨" φ   => FormL.valid φ

def SatSet (M : Model symbs) (g : Assignment M) (w : M.Fr.W s) (Γ : PremiseSet symbs s) : Prop :=
  ∀ φ, φ ∈ Γ → ⟨M, g, w⟩ ⊨ φ

notation:50 "⟨" M "," g "," w "⟩" "⊨" Γ => SatSet M g w Γ

-- The local consequence relation
def SemanticConsequence (Γ : PremiseSet symbs s) (φ : Form symbs s) : Prop :=
  ∀ M g w, (⟨M, g, w⟩ ⊨ Γ) → ⟨M, g, w⟩ ⊨ φ

notation:50 Γ "⊨" φ => SemanticConsequence Γ φ
