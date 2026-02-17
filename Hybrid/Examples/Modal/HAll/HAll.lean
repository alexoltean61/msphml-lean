/-
  Here we define the 𝓗(∀) fragment, mono-sorted and monadic
-/
import Hybrid.Examples.Modal.Signature
import Hybrid.Language
import Hybrid.Proof

def IsHAll : Fragment ModalBase
  | _, .svar _   => true
  | _, .nom (.nom _) => true    -- no constant nominals in ℋ(∀)
  | _, .prop _   => true
  | _, .appl _ φ => IsHAll _ φ
  | _, .or φ ψ   => IsHAll _ φ && IsHAll _ ψ
  | _, .neg φ    => IsHAll _ φ
  | _, .bind _ φ => IsHAll _ φ
  | _, _         => false

def HAll  := Form.fragment IsHAll FormulaSort

@[coe]
def HAll.toForm (φ : HAll) : Form ModalBase FormulaSort := φ.1
instance : Coe HAll (Form ModalBase FormulaSort) where
  coe := HAll.toForm

def pvar := ModalBase.prop FormulaSort
def var  := ModalBase.svar FormulaSort
def nom  := ModalBase.nom FormulaSort
@[coe]
def HAll.prop    (p : pvar) : HAll := ⟨.prop p, rfl⟩
@[coe]
def HAll.svar    (x : var) : HAll := ⟨.svar x, rfl⟩
@[coe]
def HAll.nom     (k : nom) : HAll  := ⟨.nom <| .nom k, rfl⟩
def HAll.diamond (φ  : HAll)  : HAll := ⟨ℋ⟨ModalBase.poss⟩ φ.1, φ.2⟩
def HAll.or      (φ ψ : HAll) : HAll := ⟨φ.1 ⋁ ψ.1, by simp only [IsHAll, φ.2, ψ.2, Bool.and_self]⟩
def HAll.and     (φ ψ : HAll) : HAll := ⟨φ.1 ⋀ ψ.1, by simp [IsHAll]; exact And.intro φ.2 ψ.2⟩
def HAll.imp     (φ ψ : HAll) : HAll := ⟨φ.1 ⟶ ψ.1, by simp [IsHAll]; exact And.intro φ.2 ψ.2⟩
def HAll.iff     (φ ψ : HAll) : HAll := ⟨φ.1 ←→ ψ.1, by simp [IsHAll, φ.2, ψ.2]⟩
def HAll.neg     (φ : HAll)   : HAll := ⟨∼φ.1, φ.2⟩
def HAll.forAll (x: var) (φ : HAll) : HAll := ⟨ℋ∀ x φ.1, φ.2⟩

def HAll.box     (φ  : HAll)  : HAll  := (φ.neg).diamond.neg
def HAll.exists (x : var) (φ : HAll)  := ((φ.neg).forAll x).neg

section IsHAll

variable {φ : Form ModalBase FormulaSort}

lemma negAll : φ.negAll = ∼φ := by
  cases φ <;> aesop

@[simp]
lemma hallNegAll (h : IsHAll _ φ) : IsHAll _ φ.negAll := by
  simp [negAll, IsHAll]
  exact h

@[simp]
lemma hallApplDual (h : IsHAll _ φ) : IsHAll _ (ℋ⟨ModalBase.poss⟩ᵈ φ) := by
  simp [FormL.applDual, IsHAll]
  apply hallNegAll h

lemma hallIsHAll {φ : HAll} : IsHAll _ φ.toForm := by
  obtain ⟨form, isHAll⟩ := φ
  cases form with
  | svar _   => exact isHAll
  | nom n    =>
      cases n with
      | nom n => exact isHAll
      | _ => unfold IsHAll at isHAll; contradiction
  | «prop» _ => exact isHAll
  | appl _ φ => simp; exact isHAll
  | or φ ψ   => simp; exact isHAll
  | neg φ    => simp; exact isHAll
  | bind x φ => simp; exact isHAll
  | _        => unfold IsHAll at isHAll; contradiction

end IsHAll

def HAll.boxLL  (φ  : HAll)  : HAll := ⟨ℋ⟨ModalBase.poss⟩ᵈ φ.1, hallApplDual φ.2⟩

lemma HAll.boxIsLL {φ : HAll} : φ.box = φ.boxLL := by
  obtain ⟨form, IsHAll⟩ := φ
  cases form <;> aesop

def HAll.boxN : ℕ → HAll → HAll
  | 0, φ   => φ
  | n+1, φ => (φ.box).boxN n
def HAll.diamondN : ℕ → HAll → HAll
  | 0, φ   => φ
  | n+1, φ => (φ.diamond).diamondN n

instance : Coe var HAll  := ⟨HAll.svar⟩
instance : Coe pvar HAll := ⟨HAll.prop⟩
instance : Coe nom HAll  := ⟨HAll.nom⟩

infixr:60 " ⟶ " => HAll.imp
infixr:60 " ~> " => HAll.imp
infixr:60 " ←→ " => HAll.iff
infixl:65 " ⋀ " => HAll.and
infixl:65 " ⋁ " => HAll.or
prefix:150 "□" => HAll.box
prefix:150 "◇" => HAll.diamond
notation:150 "□" "^" n:arg φ:100 => HAll.boxN n φ
notation:150 "◇" "^" n:arg φ:100 => HAll.diamondN n φ
prefix:170 "~" => HAll.neg
notation:200 "∀ " x:arg ". " φ:50 => HAll.forAll x φ
notation:200 "∃ " x:arg "· " φ:50 => HAll.exists x φ
notation:200 "∀ " x:arg "· " φ:50 => HAll.forAll x φ
notation:200 "∃ " x:arg "· " φ:50 => HAll.exists x φ
