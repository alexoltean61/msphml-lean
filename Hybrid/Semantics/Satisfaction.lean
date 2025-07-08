import Hybrid.Language

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
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

/--
  We can use a `Context` to take a certain projection from a `WProd`.
    A `Context` effectively selects a certain formula ocurring in a formula list.
    `WProd.select` selects the corresponding *world* of that formula in a `WProd`.
-/
def WProd.select {φ : Form symbs s} {ψ : FormL symbs sorts} (ws : WProd W sorts) (C : φ.Context ψ) : W s :=
  match C with
  | .refl => ws
  | .head => ws.1
  | .tail C' => ws.2.select C'

structure Frame (signature : Signature α) where
  W  : signature.S → Type
  R  : signature.Sig dom range → Set (WProd W (range :: dom))
  Nm : {s : signature.S} → signature.N s → W s

  WNonEmpty : ∀ s, Inhabited (W s)

structure Model (symbs : Symbols α) where
  Fr  : Frame symbs.signature
  Vₚ  : symbs.prop s → Set (Fr.W s)
  Vₙ  : symbs.nom s → Fr.W s

def Model.VNom (M : Model symbs) : symbs.nominal s → M.Fr.W s
| .inl n => M.Fr.Nm n
| .inr n => M.Vₙ n

def Assignment (M : Model symbs) : Type u := {s: symbs.signature.S} → symbs.svar s → M.Fr.W s

def Assignment.variant {M : Model symbs} (g' g : Assignment M) (x : symbs.svar s): Prop :=
  (∀ y : symbs.svar s, x ≠ y → g' y = g y) ∧
    ∀ {t : symbs.signature.S} (y : symbs.svar t), s ≠ t → g' y = g y

def Assignment.free_agree {M : Model symbs} (g g' : Assignment M) (φ : FormL symbs sorts): Prop :=
  ∀ {s : symbs.signature.S} (x : symbs.svar s), φ.varOccursFree x → g x = g' x

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
notation:50 "⟨" M "," g "," w "⟩" "⊭" φ => ¬ Sat M g w φ

variable {α : Type u}
variable {symbs : Symbols α}
variable {s : symbs.signature.S}

section Defs
  -- Definitions below will be paramtrized over a particular *class* of models,
  -- so not necessarily over the class of all models.

  -- The set of worlds at which a formula is satisfied in a model, under an assignment
  -- (Auxiliary, currently unneeded)
  def FormL.Worlds (φ : Form symbs s) (M : Model symbs) (g : Assignment M) : Set (M.Fr.W s) :=
    λ w => Sat M g w φ

  def FormL.satisfiable (φ : Form symbs s) (ModelClass : Set (Model symbs)) : Prop :=
    ∃ M : ModelClass, ∀ g w, ⟨M, g, w⟩ ⊨ φ

  def Model.valid (M : Model symbs) (φ : Form symbs s) : Prop :=
    ∀ g w, ⟨M, g, w⟩ ⊨ φ
  notation:50 M "⊨" φ => Model.valid M φ

  def FormL.validClass (φ : Form symbs s) (ModelClass : Set (Model symbs)) : Prop :=
    ∀ M : ModelClass, M ⊨ φ
  notation:50 "⊨" "(" M ")" φ   => FormL.validClass φ M

  /-
    The class of all models.
  -/
  def Models.All : Set (Model symbs) :=
    {M : Model symbs | true}

  /-
    The class of models determined by a class of frames contains all
      models which whose frame belongs to the class.
  -/
  def Models.Fr (Frs : Set (Frame symbs.signature)) : Set (Model symbs) :=
    {M : Model symbs | M.Fr ∈ Frs}

  /-
    The class of models determined by a particular set of axioms contains all
      models in which those axioms are valid.
  -/
  def Models.Ax (Λ : AxiomSet symbs) : Set (Model symbs) :=
    {M : Model symbs | ∀ s, ∀ φ ∈ Λ s, M ⊨ φ}

  /-
    A formula is valid in a frame `Fr`,
      iff it is valid in each model which has `Fr` as its frame.
  -/
  def Frame.valid (Fr : Frame symbs.signature) (φ : Form symbs s) : Prop :=
    ∀ M : (Models.Fr { Fr }), M ⊨ φ
  notation:50 F "⊨" φ => Frame.valid F φ

  /-
    The class of frames determined by a particular set of axioms contains all
      frames in which those axioms are valid.
  -/
  def Frames.Ax (Λ : AxiomSet symbs) : Set (Frame symbs.signature) :=
    {Fr : Frame symbs.signature | ∀ s, ∀ φ ∈ Λ s, Fr ⊨ φ}

  def Sat.Set (M : Model symbs) (g : Assignment M) (w : M.Fr.W s) (Γ : PremiseSet symbs s) : Prop :=
    ∀ φ : Γ, ⟨M, g, w⟩ ⊨ φ.1
  notation:50 "⟨" M "," g "," w "⟩" "⊨" Γ => Sat.Set M g w Γ

  -- The local consequence relation
  def Entails (Γ : PremiseSet symbs s) (φ : Form symbs s) (ModelClass : Set (Model symbs)) : Prop :=
    ∀ M : ModelClass, ∀ g w, (⟨M.1, g, w⟩ ⊨ Γ) → ⟨M.1, g, w⟩ ⊨ φ
  notation:50 Γ "⊨" "(" M ")" φ => Entails Γ φ M

  @[reducible] def FormL.valid (φ : Form symbs s) : Prop :=
    ⊨(Models.All) φ
  notation:50 "⊨" φ  => FormL.valid φ

  @[reducible] def Models.AxValid (φ : Form symbs s) (Λ : AxiomSet symbs) : Prop :=
    ⊨(Models.Ax Λ) φ
  notation:50 "⊨" "Mod" "(" Λ:25 ")" φ:arg => Models.AxValid φ Λ

  @[reducible] def Models.FrValid (φ : Form symbs s) (Λ : AxiomSet symbs) : Prop :=
    ⊨(Models.Fr (Frames.Ax Λ)) φ
  notation:50 "⊨" "Fr" "(" Λ:25 ")" φ:arg => Models.FrValid φ Λ

  @[reducible] def Entails.General (Γ : PremiseSet symbs s) (φ : Form symbs s) : Prop :=
    Γ ⊨(Models.All) φ
  notation:50 Γ:arg "⊨" φ:arg => Entails.General Γ φ

  @[reducible] def Entails.Mod (Γ : PremiseSet symbs s) (φ : Form symbs s) (Λ : AxiomSet symbs) : Prop :=
    Γ ⊨(Models.Ax Λ) φ
  notation:50 Γ:arg "⊨" "Mod" "(" Λ:25 ")" φ:arg => Entails.Mod Γ φ Λ

  @[reducible] def Entails.Fr (Γ : PremiseSet symbs s) (φ : Form symbs s) (Λ : AxiomSet symbs) : Prop :=
    Γ ⊨(Models.Fr (Frames.Ax Λ)) φ
  notation:50 Γ:arg "⊨" "Fr" "(" Λ:25 ")" φ:arg => Entails.Fr Γ φ Λ

end Defs

section Lemmas

  @[simp]
  lemma Sat.prop : (⟨M, g, w⟩ ⊨ .prop p) ↔ w ∈ M.Vₚ p := by
    simp only [Sat]

  @[simp]
  lemma Sat.nom : (⟨M, g, w⟩ ⊨ .nom n) ↔ w = M.VNom n := by
    simp only [Sat]

  @[simp]
  lemma Sat.svar : (⟨M, g, w⟩ ⊨ .svar x) ↔ w = g x := by
    simp only [Sat]

  @[simp]
  lemma Sat.appl {w : M.Fr.W s} {σ : symbs.signature.Sig (s₁ :: t) s} : (⟨M, g, w⟩ ⊨ ℋ⟨σ⟩ arg) ↔ ∃ w', Sat M g w' arg ∧ ⟨w, w'⟩ ∈ M.Fr.R σ := by
    simp only [Sat]

  @[simp]
  lemma Sat.neg : (⟨M, g, w⟩ ⊨ ∼φ) ↔ ⟨M, g, w⟩ ⊭ φ := by
    simp only [Sat]

  @[simp]
  lemma Sat.or : (⟨M, g, w⟩ ⊨ φ ⋁ ψ) ↔ ((⟨M, g, w⟩ ⊨ φ) ∨ ⟨M, g, w⟩ ⊨ ψ) := by
    simp only [Sat]

  @[simp]
  lemma Sat.at : (⟨M, g, w⟩ ⊨ ℋ@k φ) ↔ (⟨M, g, M.VNom k⟩ ⊨ φ) := by
    simp only [Sat]

  @[simp]
  lemma Sat.forall {φ : Form symbs s} {x : symbs.svar t}: (⟨M, g, w⟩ ⊨ ℋ∀ x φ) ↔ (∀ g', g'.variant g x → ⟨M, g', w⟩ ⊨ φ) := by
    simp only [Sat]

  @[simp]
  lemma Sat.cons {φ : Form symbs s} : (⟨M, g, ws⟩ ⊨ φ.cons ψs) ↔ ((⟨M, g, ws.1⟩ ⊨ φ) ∧ ⟨M, g, ws.2⟩ ⊨ ψs) := by
    simp only [Sat]

  @[simp]
  lemma Sat.implies : (⟨M, g, w⟩ ⊨ φ ⟶ ψ) ↔ (⟨M, g, w⟩ ⊨ φ) → ⟨M, g, w⟩ ⊨ ψ := by
    apply Iff.intro
    . simp only [FormL.implies, Sat]
      intro h _
      apply Or.elim h
      . intro
        contradiction
      . simp only [imp_self]
    . simp only [FormL.implies, Sat]
      intro h
      apply not_or_of_imp
      assumption

  @[simp]
  lemma Sat.and : (⟨M, g, w⟩ ⊨ φ ⋀ ψ) ↔ (⟨M, g, w⟩ ⊨ φ) ∧ ⟨M, g, w⟩ ⊨ ψ := by
    apply Iff.intro
    repeat {
      simp only [FormL.and, Sat]
      rw [not_or, not_not, not_not]
      simp only [imp_self]
    }

  @[simp]
  lemma Sat.iff : (⟨M, g, w⟩ ⊨ φ ←→ ψ) ↔ ((⟨M, g, w⟩ ⊨ φ) ↔ ⟨M, g, w⟩ ⊨ ψ) := by
    apply Iff.intro
    . simp only [FormL.iff, FormL.and, FormL.implies, Sat, not_or, not_not, not_and, and_imp]
      intros
      apply Iff.intro
      repeat assumption
    . simp only [FormL.iff, FormL.and, FormL.implies, Sat, not_or, not_not, not_and]
      intro h
      apply And.intro
      . exact h.mp
      . exact h.mpr

  @[simp]
  lemma Sat.exists {φ : Form symbs s} {x : symbs.svar t}: (⟨M, g, w⟩ ⊨ ℋ∃ x φ) ↔ (∃ g', g'.variant g x ∧ ⟨M, g', w⟩ ⊨ φ) := by
    simp [FormL.exists]

  @[simp]
  lemma Sat.negAll {φ : FormL symbs sorts} : (⟨M, g, ws⟩ ⊨ φ.negAll) ↔ (∀ {s' : symbs.signature.S} {ψ : Form symbs s'} (C : ψ.Context φ), ⟨M, g, ws.select C⟩ ⊭ ψ) := by
    apply Iff.intro
    . intro h1 ψ _ C h2
      induction φ with
      | cons h t _ ih2 =>
          simp only [FormL.negAll, Sat] at h1
          cases C with
          | head =>
              simp only [WProd.select] at h2
              have := h1.1
              contradiction
          | tail C' =>
              specialize ih2 h1.2 C'
              simp only [WProd.select, imp_false] at h2 ih2
              contradiction
      | _ =>
          simp only [FormL.negAll] at h1
          cases C with
          | refl => simp only [WProd.select] at h2 ; contradiction
    . intro h1
      induction φ with
      | cons h t _ ih2 =>
          simp only [FormL.negAll, Sat]
          apply And.intro
          . specialize h1 .head
            simp only [WProd.select] at h1
            exact h1
          . apply ih2
            intro _ χ C
            cases C with
            | refl =>
                simp only [WProd.select]
                specialize h1 (.tail .refl)
                simp only [WProd.select] at h1
                exact h1
            | head =>
                simp only [WProd.select]
                specialize h1 (.tail .head)
                simp only [WProd.select] at h1
                exact h1
            | tail C' =>
                simp only [WProd.select]
                specialize h1 (.tail $ .tail C')
                simp only [WProd.select] at h1
                exact h1
      | _ =>
          simp only [FormL.negAll]
          specialize h1 .refl
          simp only [WProd.select] at h1
          exact h1

  @[simp]
  lemma Sat.applDual {w : M.Fr.W s} {σ : symbs.signature.Sig (s₁ :: t) s} :
    (⟨M, g, w⟩ ⊨ ℋ⟨σ⟩ᵈ args) ↔
      (∀ ws, ⟨w, ws⟩ ∈ (M.Fr.R σ) →
        ∃ (s' : symbs.signature.S) (φ : Form symbs s') (ctx : φ.Context args), ⟨M, g, ws.select ctx⟩ ⊨ φ) := by
    simp only [FormL.applDual, Sat, not_exists, not_and, WProd]
    apply Iff.intro
    . intro h1 w h2
      specialize h1 w
      by_contra h3
      simp only [not_exists] at h3
      apply h1
      . simp only [Sat.negAll]
        apply h3
      . assumption
    . intro h1 ws h2
      by_contra h3
      specialize h1 ws h3
      rw [Sat.negAll] at h2
      . have ⟨_, ⟨_, ⟨ctx, _⟩⟩⟩ := h1
        specialize h2 ctx
        contradiction

  @[simp]
  lemma Sat.top : ⟨M, g, w⟩ ⊨ ℋ⊤ := by
    simp [FormL.top]
    apply Classical.em

  @[simp]
  lemma Sat.bot : ⟨M, g, w⟩ ⊭ ℋ⊥ := by
    simp [FormL.bot]

  lemma Sat.context {ψ : FormL symbs sorts} : (⟨M, g, ws⟩ ⊨ ψ) ↔ (∀ {s}, ∀ {φ : Form symbs s}, ∀ ctx : (φ.Context ψ), ⟨M, g, ws.select ctx⟩ ⊨ φ) := by
    apply Iff.intro
    . intro h s φ ctx
      induction ctx with
      | refl =>
          simp only [WProd.select]
          exact h
      | head =>
          simp only [Sat.cons] at h
          simp only [WProd.select]
          exact h.1
      | tail _ ih =>
          simp only [Sat.cons] at h
          simp only [WProd.select]
          apply ih
          exact h.2
    . intro h
      induction ψ with
      | cons χ τ _ ih2 =>
          simp only [Sat.cons]
          apply And.intro
          . have hAppl := h FormL.Context.head
            simp [WProd.select] at hAppl
            exact hAppl
          . apply ih2
            intro s φ ctx
            have hAppl := h (FormL.Context.tail ctx)
            simp [WProd.select] at hAppl
            exact hAppl
      | _ =>
          have := h FormL.Context.refl
          simp [WProd.select] at this
          exact this

  lemma WProd.select_iso {φ ψ : Form symbs s} {χ τ : FormL symbs sorts} {C₁ : φ.Context χ} {C₂ : ψ.Context τ} {ws : WProd W sorts} (h : C₁.iso C₂) : ws.select C₁ = ws.select C₂ := by
    induction C₁
    . cases C₂
      . simp only [WProd.select]
    . cases C₂
      . simp only [WProd.select]
      . simp only [FormL.Context.iso] at h
    . cases C₂
      . simp only [FormL.Context.iso] at h
      . simp only [FormL.Context.iso, WProd.select] at h ⊢
        apply_assumption
        assumption

  lemma Models.all_maximal : ∀ C : Set (Model Symbs), C ⊆ Models.All := by
    simp only [All, Set.setOf_true, Set.subset_univ, implies_true]

  lemma Models.fr_in_ax {Λ : AxiomSet symbs} : (Models.Fr (Frames.Ax Λ)) ⊆  Models.Ax Λ := by
    simp [Models.Fr, Models.Ax]
    intro M fr s sSort φ φAx
    simp only [Frames.Ax, Frame.valid, Models.Fr, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall,
      Set.mem_singleton_iff] at fr
    apply_assumption
    . exact φAx
    . rfl

  lemma Entails.if_general {Γ : PremiseSet symbs s} : (Γ ⊨ φ) → (Γ ⊨(C) φ) := by
    intro h
    intro M
    have := h ⟨M, Models.all_maximal C M.2⟩
    exact this

  lemma Entails.if_model_frame {Λ : AxiomSet symbs} : Γ ⊨Mod(Λ) φ → Γ ⊨Fr(Λ) φ := by
    intro h
    intro M
    have := h ⟨M, Models.fr_in_ax M.2⟩
    exact this

  lemma Entails.no_premises {C : Set (Model symbs)} : (∅ ⊨(C) φ) ↔ ⊨(C) φ := by
    apply Iff.intro
    . intro h M g w
      apply h
      . simp only [Sat.Set, Subtype.forall, Set.mem_empty_iff_false, false_implies, implies_true]
    . intro h M g w _
      apply h

  lemma Valid.if_general_model (C : Set (Model symbs)) : (⊨ φ) → ⊨(C) φ := by
    unfold FormL.valid
    rw [←Entails.no_premises, ←Entails.no_premises]
    apply Entails.if_general

 lemma Entails.deduction : ((Γ ∪ {φ}) ⊨(C) ψ) ↔ Γ ⊨(C) (φ ⟶ ψ) := by
    apply Iff.intro
    . intro h1 M g w h2
      rw [Sat.implies]
      intro h3
      apply h1
      simp only [Sat.Set, Subtype.forall, Set.union_singleton, Set.mem_insert_iff, forall_eq_or_imp] at h2 ⊢
      apply And.intro
      repeat assumption
    . intro h M g w h2
      have := h M g w
      simp only [Sat.implies] at this
      simp only [Sat.Set, Subtype.forall, Set.union_singleton, Set.mem_insert_iff,
        forall_eq_or_imp] at h2
      apply this
      . intro φ
        apply h2.2
        exact φ.2
      . exact h2.1


  lemma Entails.monotonicity {Γ Δ : PremiseSet symbs s} (h : Γ ⊆ Δ) : (Γ ⊨(C) φ) → (Δ ⊨(C) φ) := by
    intro h1 M
    intro g w h2
    apply h1
    intro φ
    exact h2 ⟨φ.1, h φ.2⟩

 lemma Valid.conjunction_entails {C : Set (Model symbs)} :
  (∃ ch : FiniteChoice Γ, ⊨(C) (ch.conjunction ⟶ φ)) → (Γ ⊨(C) φ) := by
    intro ⟨ch, h⟩
    induction ch generalizing φ with
    | nil =>
        apply Entails.monotonicity
        . apply Set.empty_subset
        rw [Entails.no_premises]
        simp only [FiniteChoice.conjunction] at h
        intro M g w
        have := h M g w
        simp only [Sat.implies, Sat.or, Sat.neg] at this
        apply this
        apply Classical.em
    | cons ψ ch ih =>
        have : Γ = Γ ∪ {ψ.1} := by simp only [Set.union_singleton, Subtype.coe_prop,
          Set.insert_eq_of_mem]
        rw [this, Entails.deduction]
        apply ih
        clear ih
        cases ch
        . simp only [FiniteChoice.conjunction] at h ⊢
          intro M g w
          rw [Sat.implies, Sat.implies]
          intros
          apply Sat.implies.mp (h M g w)
          assumption
        . simp only [FiniteChoice.conjunction] at h ⊢
          intro M g w
          rw [Sat.implies, Sat.implies]
          intros
          apply Sat.implies.mp (h M g w)
          rw [Sat.and]
          apply And.intro
          repeat assumption

  lemma Assignment.variant_refl {g : Assignment M} : g.variant g x := by
    unfold Assignment.variant
    aesop

  @[symm]
  lemma Assignment.variant_symm {g g' : Assignment M} : g.variant g' x → g'.variant g x := by
    unfold Assignment.variant
    aesop

  section free_agree
    variable {α : Type u}
    variable [DecidableEq α]
    variable {symbs : Symbols α}
    variable {s : symbs.signature.S}

    @[symm]
    def Assignment.free_agree_symm {M : Model symbs} {g g' : Assignment M} {φ : FormL symbs sorts} : g.free_agree g' φ → g'.free_agree g φ := by
      unfold Assignment.free_agree
      intro h1 s x h2
      symm
      apply h1
      repeat apply_assumption

  end free_agree

end Lemmas
