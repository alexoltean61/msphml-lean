import Hybrid.Completeness.Lindenbaum.Expansion.Def

namespace Completeness

open Completeness

variable {α β : Type u}
variable {S₁ : Symbols α}
variable {S₂ : Symbols β}
variable {s : S₁.signature.S}

def Symbols.morphism.morph_nominal (nom : S₁.nominal s) (m : S₁.morphism S₂) : S₂.nominal (m.morph_sort s) :=
  match nom with
  | .inl n => m.morph_N n
  | .inr n => m.morph_nom n

def Symbols.morphism.morph_formula {sorts : List S₁.signature.S} (φ : FormL S₁ sorts) (m : S₁.morphism S₂) : FormL S₂ (sorts.map m.morph_sort) :=
  match φ with
  | .prop p   => .prop $ m.morph_prop p
  | .nom  n   => .nom $ m.morph_nominal n
  | .svar x   => .svar $ m.morph_svar x
  | .or φ ψ   => .or (m.morph_formula φ) (m.morph_formula ψ)
  | .neg φ    => .neg $ m.morph_formula φ
  | @FormL.at _ _ _ s k φ   => ℋ@[[(m.morph_sort s)]] (m.morph_nominal k) (m.morph_formula φ)
  | .bind x φ => .bind (m.morph_svar x) (m.morph_formula φ)
  | .appl σ φ => .appl (m.morph_op σ) (m.morph_formula φ)
  | .cons φ ψ => .cons (m.morph_formula φ) (m.morph_formula ψ)

def Symbols.morphism.morph_premise (Γ : PremiseSet S₁ s) (m : S₁.morphism S₂) : PremiseSet S₂ (m.morph_sort s) :=
  { m.morph_formula φ | φ ∈ Γ }

abbrev Symbols.embedding.morph_formula (φ : FormL S₁ sorts) (m : S₁ ↪ S₂) : FormL S₂ (sorts.map m.m.morph_sort) :=
  m.m.morph_formula φ

abbrev Symbols.embedding.morph_premise (Γ : PremiseSet S₁ s) (m : S₁ ↪ S₂) : PremiseSet S₂ (m.m.morph_sort s) :=
  m.m.morph_premise Γ

section ClassicalRequired

  open Classical

  abbrev Symbols.morphism.morph_axiom (Λ : AxiomSet S₁) (m : S₁.morphism S₂) : AxiomSet S₂ :=
    λ s => if h : ∃ s_inv, s = m.morph_sort s_inv then
              { h.choose_spec ▸ m.morph_formula φ | φ ∈ Λ h.choose }
            else { }

  abbrev Symbols.embedding.morph_axiom (Λ : AxiomSet S₁) (m : S₁ ↪ S₂) : AxiomSet S₂ :=
    m.m.morph_axiom Λ

  abbrev Symbols.morphism.morph_worlds (W : S₁.signature.S → Type u) (m : S₁.morphism S₂) : S₂.signature.S → Type u :=
    λ s₂ =>
        if h : ∃ s₁, s₂ = m.morph_sort s₁ then
                  W h.choose
        else PUnit

  noncomputable def Symbols.morphism.morph_wprod {W : S₁.signature.S → Type u} (ws : WProd W sorts) (inh : ∀ s, Inhabited (W s)) (m : S₁.morphism S₂) : WProd (m.morph_worlds W) (sorts.map m.morph_sort) :=
  match sorts with
  | []  => ws
  | [s] => by
      -- This is absolutely awful
      simp only [List.map_cons, List.map_nil, WProd, morph_worlds, exists_apply_eq_apply',
        ↓reduceDIte]
      exact (inh (of_eq_true (exists_apply_eq_apply'._simp_1 m.morph_sort s)).choose).default
  | s :: s' :: ss => by
      simp only [List.map_cons, WProd]
      apply Prod.mk
      . -- This is absolutely awful
        simp only [morph_worlds, exists_apply_eq_apply', ↓reduceDIte]
        exact (inh (of_eq_true (exists_apply_eq_apply'._simp_1 m.morph_sort s)).choose).default
      . exact m.morph_wprod ws.2 inh

  noncomputable def Symbols.morphism.morph_frame (F : Frame S₁.signature) (m : S₁.morphism S₂) : Frame S₂.signature :=
  {
    W := m.morph_worlds F.W
    WNonEmpty s₂ :=
        if h : ∃ s₁, s₂ = m.morph_sort s₁ then by
              simp only [morph_worlds, h, ↓reduceDIte]
              exact ⟨(F.WNonEmpty h.choose).default⟩
        else by
            simp only [morph_worlds, h, ↓reduceDIte]
            exact ⟨⟨⟩⟩
    R := λ {dom₂} {rng₂} σ₂ =>
          if h : ∃ dom₁ : List S₁.signature.S, dom₁.map m.morph_sort = dom₂ then
            if h' : ∃ rng₁ : S₁.signature.S, m.morph_sort rng₁ = rng₂ then
              if h'' : ∃ σ₁ : S₁.signature.«Σ» h.choose h'.choose, h.choose_spec ▸ h'.choose_spec ▸ m.morph_op σ₁ = σ₂ then
                h.choose_spec ▸ h'.choose_spec ▸ { m.morph_wprod ws F.WNonEmpty | ws ∈ F.R h''.choose }
              else { }
            else { }
          else { }
    Nm := λ {s₂} n₂ =>
          if h : ∃ s₁, s₂ = m.morph_sort s₁ then
            -- This is absolutely awful
            if h' : ∃ n₁ : S₁.signature.N h.choose, n₂ = h.choose_spec ▸ m.morph_N n₁ then by
              simp only [morph_worlds, h, ↓reduceDIte]
              exact F.Nm h'.choose
            else by
              simp only [morph_worlds, h, ↓reduceDIte]
              exact (F.WNonEmpty h.choose).default
          else by
            simp only [morph_worlds, h, ↓reduceDIte]
            exact ⟨⟩
  }

  noncomputable def Symbols.morphism.morph_world {F : Frame S₁.signature} (w : F.W s₁) (m : S₁.morphism S₂) : (m.morph_frame F).W (m.morph_sort s₁) :=
    sorry

  noncomputable def Symbols.embedding.morph_world {F : Frame S₁.signature} (w : F.W s₁) (m : S₁ ↪ S₂) : (m.m.morph_frame F).W (m.m.morph_sort s₁) :=
    sorry

  noncomputable def Symbols.morphism.morph_model (M : Model S₁) (m : S₁.morphism S₂) : Model S₂ :=
  {
    «Fr» := m.morph_frame M.Fr
    Vₚ   := λ {s₂} p₂ =>
          if h : ∃ s₁, s₂ = m.morph_sort s₁ then
            -- This is absolutely awful
            if h' : ∃ p₁ : S₁.prop h.choose, p₂ = h.choose_spec ▸ m.morph_prop p₁ then by
              simp only [morph_frame, morph_worlds, h, ↓reduceDIte]
              exact M.Vₚ h'.choose
            else by
              simp only [morph_frame, morph_worlds, h, ↓reduceDIte]
              exact { }
          else by
            simp only [morph_frame, morph_worlds, h, ↓reduceDIte]
            exact { }
    Vₙ   := λ {s₂} n₂ =>
          if h : ∃ s₁, s₂ = m.morph_sort s₁ then
            -- This is absolutely awful
            if h' : ∃ n₁ : S₁.nom h.choose, n₂ = h.choose_spec ▸ m.morph_nom n₁ then by
              simp only [morph_frame, morph_worlds, h, ↓reduceDIte]
              exact M.Vₙ h'.choose
            else by
              simp only [morph_frame, morph_worlds, h, ↓reduceDIte]
              exact (M.Fr.WNonEmpty h.choose).default
          else by
            simp only [morph_frame, morph_worlds, h, ↓reduceDIte]
            exact ⟨⟩
  }

  noncomputable abbrev Symbols.embedding.morph_model (M : Model S₁) (m : S₁ ↪ S₂) : Model S₂ :=
    m.m.morph_model M

  noncomputable def Symbols.morphism.morph_assignment {M : Model S₁} (g : Assignment M) (m : S₁.morphism S₂) : Assignment (m.morph_model M) :=
    sorry

  noncomputable def Symbols.embedding.morph_assignment {M : Model S₁} (g : Assignment M) (m : S₁ ↪ S₂) : Assignment (m.morph_model M) :=
    m.m.morph_assignment g

end ClassicalRequired

notation:50 emb:lead "+" s:arg => Symbols.morphism.morph_sort (Symbols.embedding.m emb) s
notation:50 emb:lead "+" φ:arg => Symbols.embedding.morph_formula φ emb
notation:50 emb:lead "+" Γ:arg => Symbols.embedding.morph_premise Γ emb
notation:50 emb:lead "+" Λ:arg => Symbols.embedding.morph_axiom Λ emb
notation:50 emb:lead "+" M:arg => Symbols.embedding.morph_model M emb
notation:50 emb:lead "+" w:arg => Symbols.embedding.morph_world w emb
notation:50 emb:lead "+" g:arg => Symbols.embedding.morph_assignment g emb

end Completeness
