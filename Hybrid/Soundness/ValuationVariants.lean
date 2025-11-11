import Hybrid.Semantics.Satisfaction

variable {α : Type u}
variable [DecidableEq α]
variable {symbs : Symbols α}
variable {s : symbs.signature.S}

namespace Soundness

open Soundness

section Defs

  /--
    Defines a model identical to `M`, except the valuation function assigns world `w` to nominal `j`.
  -/
  def Model.v_variant (M : Model symbs) (n : symbs.nominal s) (w : M.Fr.W s) : Model symbs :=
    match n with
    | .ctNom n =>
      {
        «Fr» :=
          {
            W  := M.Fr.W,
            R  := M.Fr.R,
            Nm := λ {t} m =>
              if h : t = s then
                if h ▸ m = n then
                  h ▸ w
                else
                  M.Fr.Nm m
              else M.Fr.Nm m,
            WNonEmpty := M.Fr.WNonEmpty,
            WDisjoint := M.Fr.WDisjoint
          },
        Vₚ := M.Vₚ
        Vₙ := M.Vₙ
      }
    | .nom n =>
      {
        «Fr» := M.Fr
        Vₚ := M.Vₚ
        Vₙ := λ {t} m =>
              if h : t = s then
                if h ▸ m = n then
                  h ▸ w
                else
                  M.Vₙ m
              else M.Vₙ m,
      }

  /--
    This function exists because Lean is not able to unfold inside pattern matching.
    But it acts like the identity function on `g`.
  -/
  def Assignment.v_variant (g : Assignment M) (n : symbs.nominal s) (w : M.Fr.W s) : Assignment (M.v_variant n w) := λ x =>
    match n with
    | .ctNom _ => g x
    | .nom _ => g x

  /--
    This function exists because Lean is not able to unfold inside pattern matching.
    But it acts like the identity function on `g`.
  -/
  def Assignment.v_variant_inverse (n : symbs.nominal s) (w : M.Fr.W s) (g : Assignment (M.v_variant n w)) : Assignment M := λ x =>
    match n with
    | .ctNom _ => g x
    | .nom _ => g x

  /--
    This function exists because Lean is not able to unfold inside pattern matching.
    But it acts like the identity function on `ws`.
  -/
  def WProd.v_variant {M : Model symbs} (ws : WProd M.Fr.W sorts) (n : symbs.nominal s) (w : M.Fr.W s) : WProd (M.v_variant n w).Fr.W sorts :=
    match n with
  | .ctNom _ => ws
  | .nom _ => ws

  /--
    This function exists because Lean is not able to unfold inside pattern matching.
    But it acts like the identity function on `ws`.
  -/
  def WProd.v_variant_inverse {M : Model symbs} (n : symbs.nominal s) (w : M.Fr.W s) (ws : WProd (M.v_variant n w).Fr.W sorts) : WProd M.Fr.W sorts :=
    match n with
  | .ctNom _ => ws
  | .nom _ => ws


  lemma WProd.v_variant_surj {M : Model symbs} {n : symbs.nominal s} {w : M.Fr.W s} (ws' : WProd (M.v_variant n w).Fr.W sorts) : ∃ ws : WProd M.Fr.W sorts, ws.v_variant n w = ws' := by
    exists ws'.v_variant_inverse
    cases n <;>
    . simp [v_variant_inverse, v_variant]

end Defs

section Lemmas

  /--
    TODO: This lemma should be unnecessary!
  -/
  lemma v_variant_nom_fr {M : Model symbs} {j : symbs.nomType s} {w : WProd M.Fr.W ([s])} : (M.v_variant j w).Fr = M.Fr := by
    simp [Model.v_variant]

  /--
    A `v_variant` for `j` and `w` evaluates nominal `j` to world `w`.
  -/
  lemma v_variant_valuation {M : Model symbs} {j : symbs.nominal s} {w : WProd M.Fr.W ([s])} : (M.v_variant j w).VNom j = w.v_variant j w := by
    cases j
    repeat simp [Model.v_variant, Model.VNom, WProd.v_variant]

  /--
    A model and its valuation variant have the same underlying set of worlds.
  -/
  lemma v_variant_world_inv {M : Model symbs} {j : symbs.nominal s} {w : M.Fr.W s} : ∀ s, M.Fr.W s = (M.v_variant j w).Fr.W s := by
    cases j
    repeat simp [Model.v_variant]

  /--
    If `k ≠ j`, then the world assigned to `j` in any `v_variant` for `k` is connected to the same worlds
    via any accesibility relation as in the original model.
  -/
  lemma v_variant_acc_inv {M : Model symbs} {k : symbs.nominal s} {j : symbs.nominal t} {σ : symbs.signature.«Σ» (s₁::ss) t} {w : WProd M.Fr.W ([s])} {ws : WProd M.Fr.W (s₁ :: ss)} (h : k ≠ₛ j) :
    ⟨(M.VNom j), ws⟩ ∈ M.Fr.R σ ↔ ⟨(M.v_variant k w).VNom j, ws.v_variant k w⟩ ∈ (M.v_variant k w).Fr.R σ := by
    cases k
    . cases j
      . by_cases same_sorts : t = s
        . subst same_sorts
          simp [Symbols.nominal.ne] at h
          rw [eq_comm] at h
          simp [Model.v_variant, Model.VNom, WProd.v_variant, h]
        . clear h
          simp [Model.v_variant, Model.VNom, WProd.v_variant, same_sorts]
      . simp [Model.v_variant, Model.VNom, WProd.v_variant]
    . cases j
      . simp [Model.v_variant, Model.VNom, WProd.v_variant]
      . by_cases same_sorts : t = s
        . subst same_sorts
          simp [Symbols.nominal.ne] at h
          rw [eq_comm] at h
          simp [Model.v_variant, Model.VNom, WProd.v_variant, h]
        . clear h
          simp [Model.v_variant, Model.VNom, WProd.v_variant, same_sorts]

  /--
    Selecting a world out of a `WProd` commutes with interpreting the world as part of a `v_variant` for a model.
  -/
  lemma WProd.v_variant_select_inv {M : Model symbs} {ws : WProd M.Fr.W sorts} {n : symbs.nominal s} {w : M.Fr.W s} {C: FormL.Context φ ψ} : (ws.v_variant n w).select C = (ws.select C).v_variant n w := by
    cases n
    repeat simp [WProd.v_variant]

  lemma v_variant_nom_agreement {M : Model symbs} {ws : WProd M.Fr.W ([t])} {g : Assignment M} {j : symbs.nominal s} {k : symbs.nominal t} (h : (ℋNom k).occurs j = false) (w : M.Fr.W s) :
    (⟨M, g, ws⟩ ⊨ (ℋNom k)) ↔ ⟨M.v_variant j w, g.v_variant j w, ws.v_variant j w⟩ ⊨ (ℋNom k) := by
    cases j
    . cases k
      . by_cases same_sorts : t = s
        . subst same_sorts
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          rw [eq_comm] at h
          simp [Model.v_variant, Model.VNom, WProd.v_variant, h]
        . clear h
          simp [Model.v_variant, Model.VNom, WProd.v_variant, same_sorts]
      . simp [Model.v_variant, Model.VNom, WProd.v_variant]
    . cases k
      . simp [Model.v_variant, Model.VNom, WProd.v_variant]
      . by_cases same_sorts : t = s
        . subst same_sorts
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          rw [eq_comm] at h
          simp [Model.v_variant, Model.VNom, WProd.v_variant, h]
        . simp [Model.v_variant, Model.VNom, WProd.v_variant, same_sorts]

  lemma v_variant_at_agreement {M : Model symbs} {ws : WProd M.Fr.W ([u])} {g : Assignment M} {j : symbs.nominal s} {k : symbs.nominal t} {φ : Form symbs t} (h : (ℋ@[[u]] k φ).occurs j = false) (w : M.Fr.W s)
  (ih : (⟨M, g, M.VNom k⟩ ⊨ φ) ↔ ⟨M.v_variant j w, g.v_variant j w, WProd.v_variant (M.VNom k) j w⟩ ⊨ φ) :
    (⟨M, g, ws⟩ ⊨ ℋ@[[u]] k φ) ↔ ⟨M.v_variant j w, g.v_variant j w, ws.v_variant j w⟩ ⊨ ℋ@[[u]] k φ := by
    cases j
    . cases k
      . by_cases same_sorts : t = s
        . subst same_sorts
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          have ⟨h1, h2⟩ := h
          clear h
          rw [eq_comm] at h2
          simp [Model.v_variant, Model.VNom, h2]
          apply ih
        . simp [Model.v_variant, Model.VNom, WProd.v_variant, same_sorts]
          apply ih
      . simp [Model.v_variant, Model.VNom, WProd.v_variant]
        apply ih
    . cases k
      . simp [Model.v_variant, Model.VNom, WProd.v_variant]
        apply ih
      . by_cases same_sorts : t = s
        . subst same_sorts
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          have ⟨h1, h2⟩ := h
          clear h
          rw [eq_comm] at h2
          simp [Model.v_variant, Model.VNom, h2]
          apply ih
        . simp [Model.v_variant, Model.VNom, WProd.v_variant, same_sorts]
          apply ih

  /-
    TODO: Do you really need to repeat the almost same proof twice?
  -/
  lemma v_variant_at_agreement' {M : Model symbs} (w : M.Fr.W s) {j : symbs.nominal s} {k : symbs.nominal t} {g : Assignment (M.v_variant j w)} {ws : WProd (M.v_variant j w).Fr.W ([u])} {φ : Form symbs t} (h : (ℋ@[[u]] k φ).occurs j = false)
  (ih : (⟨M, g.v_variant_inverse j w, M.VNom k⟩ ⊨ φ) ↔ ⟨M.v_variant j w, g, WProd.v_variant (M.VNom k) j w⟩ ⊨ φ) :
    (⟨M, g.v_variant_inverse j w, ws.v_variant_inverse j w⟩ ⊨ ℋ@[[u]] k φ) ↔ ⟨M.v_variant j w, g, ws⟩ ⊨ ℋ@[[u]] k φ := by
    cases j
    . cases k
      . by_cases same_sorts : t = s
        . subst same_sorts
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          have ⟨h1, h2⟩ := h
          clear h
          rw [eq_comm] at h2
          simp [Model.v_variant, Model.VNom, h2]
          apply ih
        . simp [Model.v_variant, Model.VNom, same_sorts]
          apply ih
      . simp [Model.v_variant, Model.VNom]
        apply ih
    . cases k
      . simp [Model.v_variant, Model.VNom]
        apply ih
      . by_cases same_sorts : t = s
        . subst same_sorts
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          have ⟨h1, h2⟩ := h
          clear h
          rw [eq_comm] at h2
          simp [Model.v_variant, Model.VNom, h2]
          apply ih
        . simp [Model.v_variant, Model.VNom, same_sorts]
          apply ih

  lemma v_variant_agreement {M : Model symbs} {φ : FormL symbs sorts} {ws : WProd M.Fr.W sorts} {g : Assignment M} {j : symbs.nominal s} (h : φ.occurs j = false) (w : M.Fr.W s) :
    (⟨M, g, ws⟩ ⊨ φ) ↔ ⟨M.v_variant j w, g.v_variant j w, ws.v_variant j w⟩ ⊨ φ := by
    cases j <;>
    . rename_i j
      induction φ generalizing g with
      | @nom t k  => apply v_variant_nom_agreement h
      | @«at» t _ k _ ih =>
          apply v_variant_at_agreement h
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          specialize @ih (M.VNom k) g h.1
          rw [ih]
      | neg _ ih =>
          simp only [Sat.neg]
          exact not_congr (ih h)
      | bind _ _ ih =>
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          simp
          apply Iff.intro
          . intros h2 g' g'_var
            specialize @h2 g' g'_var
            specialize @ih ws g' h
            rw [ih] at h2
            apply h2
          . intros h2 g' g'_var
            specialize @h2 g' g'_var
            specialize @ih ws g' h
            rw [ih]
            apply h2
      | appl _ _ ih =>
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          simp
          apply Iff.intro
          . intro ⟨ws', ⟨sat, wsRws'⟩⟩
            first | exists ws'.v_variant (.ctNom j) w | exists ws'.v_variant (.nom j) w
            apply And.intro _ wsRws'
            specialize @ih ws' g h
            rw [ih] at sat
            exact sat
          . intro ⟨ws', ⟨sat, wsRws'⟩⟩
            have ⟨ws'_inverse, heq⟩ := ws'.v_variant_surj
            subst heq
            exists ws'_inverse
            apply And.intro _ wsRws'
            specialize @ih ws'_inverse g h
            rw [ih]
            exact sat
      | or  _ _ ih1 ih2 =>
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          specialize @ih1 ws g h.1
          specialize @ih2 ws g h.2
          simp [ih1, ih2]
      | cons _ _ ih1 ih2 =>
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          specialize @ih1 ws.1 g h.1
          specialize @ih2 ws.2 g h.2
          simp [ih1, ih2]
          rename_i s₁ s₂ t a a_1
          aesop
      | _ => simp [Model.v_variant, WProd.v_variant, Assignment.v_variant]

  /-
    TODO: Do you really need to repeat the almost same proof twice?
  -/
  lemma v_variant_agreement' {M : Model symbs} {φ : FormL symbs sorts} {j : symbs.nominal s} (w : M.Fr.W s) {ws : WProd (M.v_variant j w).Fr.W sorts} {g : Assignment (M.v_variant j w)} (h : φ.occurs j = false) :
    (⟨M, g.v_variant_inverse j w, ws.v_variant_inverse j w⟩ ⊨ φ) ↔ ⟨M.v_variant j w, g, ws⟩ ⊨ φ := by
    cases j <;>
    . rename_i j
      induction φ generalizing g with
      | @nom t k  => apply v_variant_nom_agreement h
      | @«at» t _ k _ ih =>
          apply v_variant_at_agreement' w h
          apply ih
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          exact h.1
      | neg _ ih =>
          simp only [Sat.neg]
          exact not_congr (ih h)
      | bind _ _ ih =>
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          simp
          apply Iff.intro
          . intros h2 g' g'_var
            specialize @h2 g' g'_var
            specialize @ih ws g' h
            rw [←ih]
            apply h2
          . intros h2 g' g'_var
            specialize @h2 g' g'_var
            specialize @ih ws g' h
            rw [←ih] at h2
            apply h2
      | appl _ _ ih =>
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          simp
          apply Iff.intro
          . intro ⟨ws', ⟨sat, wsRws'⟩⟩
            exists ws'
            apply And.intro _ wsRws'
            specialize @ih ws' g h
            rw [←ih]
            exact sat
          . intro ⟨ws', ⟨sat, wsRws'⟩⟩
            exists ws'.v_variant_inverse j w
            apply And.intro _ wsRws'
            specialize @ih ws' g h
            rw [ih]
            exact sat
      | or  _ _ ih1 ih2 =>
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          specialize @ih1 ws g h.1
          specialize @ih2 ws g h.2
          simp [ih1, ih2]
      | cons _ _ ih1 ih2 =>
          simp [FormL.occurs, Term.occurs, FormL.nom_occurs] at h
          specialize @ih1 ws.1 g h.1
          specialize @ih2 ws.2 g h.2
          simp [←ih1, ←ih2]
          apply Iff.intro <;>
          . intro ⟨h1, h2⟩
            apply And.intro
            . exact h1
            . exact h2
      | _ => simp [WProd.v_variant_inverse, Model.v_variant, Assignment.v_variant_inverse]

  /--
    If `M` belongs to the class of models that satisfy `Λ`, and `j` does not occur in `Λ`,
      then `M`'s v_variant which takes `j` to `w` also belongs to the class that satisfies `Λ`.
  -/
  lemma Set.Elem.v_variant_modelclass_inv (Λ : AxiomSet symbs) (M : Λ.Models) (j : symbs.nominal s) (h : ¬Λ.occurs j) (w : M.1.Fr.W s) : (M.1.v_variant j w) ∈ Λ.Models := by
    cases j <;>
    . simp only [AxiomSet.Models, Set.mem_setOf_eq, Model.valid]
      simp only [AxiomSet.occurs, not_exists, Bool.not_eq_true] at h
      intro s φ φ_in_Λ g w
      specialize h s ⟨φ, φ_in_Λ⟩
      rw [←v_variant_agreement']
      . unfold Assignment.v_variant_inverse
        unfold WProd.v_variant_inverse
        simp only
        apply M.2
        exact φ_in_Λ
      . exact h

end Lemmas
