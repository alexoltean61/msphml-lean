import Hybrid.Semantics
import Hybrid.Soundness.Barcan.Language

/-
  What this file will do:
    We want to find a countermodel for the polyadic Barcan formula
      ∀ x σᵈ (φ₁, ..., φᵢ, ..., φₙ) → σᵈ (φ₁, ..., ∀ x φᵢ, ..., φₙ), for any 1 ≤ i ≤ n

    In this Lean formalization, selecting and substituting a single argument from an operator's argument list
    is expressed using "Contexts" (see Hybrid.Language.Context), so the Barcan formula looks like:
      ∀ x σᵈ ψ ⟶ σᵈ C[∀ x φ], for any C : occurrence of φ within ψ (i.e., C : φ.Context ψ)

  The countermodel's signature is defined in Hybrid.Soundness.Barcan.Language.

  Here, we define a frame and model as:
    W = {w₀, w₁}                (sorts are irrelevant to this example)
    R σ = { (w₀, w₀, w₁) }

    q is true at w₀, not at w₁
    p is true at w₁, not at w₀
    nominal j is true at w₀,
    nominal k is true at w₁

  We take g = {x → w₀}

  So we intend to prove that:
    (1) ⟨M, g, w₁⟩ ⊨ ∀ x σᵈ(@ⱼ (x ∧ p), @ₖ (x ∧ q))
  but not
    (2) ⟨M, g, w₁⟩ ⊨ σᵈ(∀ x @ⱼ (x ∧ p), @ₖ (x ∧ q))

  (1) is proved as BarcanAntecedentTrue.
  (2) is proved as BarcanConsequentFalse.
-/

def w₀ : Fin 2 := 0
def w₁ : Fin 2 := 1

lemma two_worlds : w ≠ w₀ → w = w₁ := by
  -- Annoyingly manual proof
  unfold w₀
  unfold w₁
  simp [Fin.ext_iff]
  have := w.2
  revert this
  match w.1 with
  | 0 => intros ; contradiction
  | .succ n =>
      simp [Nat.pos_of_lt_add_right, Nat.lt_iff_add_one_le]

lemma distinct_worlds : w₁ ≠ w₀ := by simp [w₀, w₁]

-- Now, define the countermodel:
def frame : Frame signature where
  W  := λ _ => Fin 2       -- two worlds for each sort (and we have just one sort)
  R  := λ {dom range} _ => -- ⟨w₀, w₀, w₁⟩ ∈ Rσ, for all dyadic σ (but we have just one σ)
  if h : dom = [sortS, sortS] ∧ range = sortS then
    h.left ▸ h.right ▸ { (⟨w₀, ⟨w₀, w₁⟩⟩) }
  else { }
  Nm := λ _ => w₀

def countermodel : Model symbs := ⟨
  frame,
  λ prop =>
    if prop = p then
      { w₀ } -- p is true only at w₀
    else if prop = q then
      { w₁ } -- q is true only at w₁
    else { },
  λ nom =>
    if nom = j then
      w₀     -- j points to w₀
    else if nom = k then
      w₁     -- k points to w₁
    else
      w₀     -- no other nominals exist, so this is placeholder
⟩

def g : Assignment countermodel :=
  λ _ => w₀  -- we start with g pointing x (the only variable) to w₀

-- Annoying that you have to specify .svar and .prop everywhere,
-- but coercions introduce weird bugs elsewhere:
def barcan_antecedent : Form symbs sortS := ℋ∀ x (ℋ⟨sig⟩ᵈ (ℋ@ j (.svar x ⋀ .prop p), ℋ@ k (.svar x ⋀ .prop q)))

def barcan_consequent : Form symbs sortS := ℋ⟨sig⟩ᵈ (ℋ∀ x (ℋ@ j (.svar x ⋀ .prop p)), ℋ@ k (.svar x ⋀ .prop q))

theorem BarcanAntecedentTrue  : ⟨countermodel, g, w₀⟩ ⊨ barcan_antecedent := by
  rw [barcan_antecedent, Sat]
  intro g' _
  rw [Sat.applDual]
  intro ws wRws
  simp [countermodel, frame] at wRws
  subst wRws
  by_cases h : g' x = g x
  . exists sortS
    exists ℋ@ j (.svar x ⋀ .prop p)
    exists .head
    simp [WProd.select, Sat, Model.VNom, countermodel, h, g]
  . exists sortS
    exists ℋ@ k (.svar x ⋀ .prop q)
    exists .tail .refl
    unfold g at h
    simp [WProd.select, Sat, not_or, not_not, two_worlds h, Model.VNom, countermodel, k, j, p, q]

theorem BarcanConsequentFalse : ⟨countermodel, g, w₀⟩ ⊭ barcan_consequent := by
  rw [barcan_consequent, Sat.applDual]
  intro habs
  specialize habs ⟨w₀, w₁⟩ (by simp [countermodel, frame])
  have ⟨_, ⟨φ, ⟨ctx_wit, hwit⟩⟩⟩ := habs
  cases ctx_wit with
  | head =>
      simp [WProd.select, Sat] at hwit
      let g' : Assignment countermodel := λ y =>
        if y = x then
          w₁
        else g y
      have is_variant : g'.variant g x := by
        simp [Assignment.variant, g']
        intro _ _ h1 h2
        have h2 := h2.symm
        contradiction
      specialize hwit g' is_variant
      simp [Model.VNom, countermodel, g'] at hwit
      exact distinct_worlds hwit.symm
  | tail ctx' =>
      cases ctx' with
      | refl =>
          simp [WProd.select, Sat, Model.VNom, countermodel, k, j, p, q, g] at hwit
          exact distinct_worlds hwit

theorem BarcanUnsound : ∃ (ψ: FormL symbs ([sortS, sortS])) (φ : Form symbs sortS) (C : φ.Context ψ) (σ : symbs.signature.Sig ([sortS, sortS]) sortS),
    -- The Barcan formula is not satisfied everywhere in the countermodel:
    ¬ countermodel ⊨ (ℋ∀ x(ℋ⟨σ⟩ᵈψ) ⟶ ℋ⟨σ⟩ᵈC[ℋ∀ x φ]) := by
    exists (ℋ@ j (.svar x ⋀ .prop p), ℋ@ k (.svar x ⋀ .prop q))
    exists ℋ@ j (.svar x ⋀ .prop p)
    exists FormL.Context.head
    exists sig
    simp only [FormL.Context.subst, id, Model.valid, not_forall]
    exists g
    exists w₀
    simp only [Sat.implies, Classical.not_imp]
    apply And.intro
    . exact BarcanAntecedentTrue
    . exact BarcanConsequentFalse

#print axioms BarcanUnsound
