import Lean
import Hybrid.Language.Signature

open Lean Elab Command Term Meta

/- Some helper expressions for the elaborators -/
abbrev rflExpr (tp e : Expr) : Expr := mkAppN (mkConst ``rfl [1]) $ #[tp, e]
abbrev stringType : Expr := mkConst ``String []
abbrev boolType : Expr := mkConst ``Bool []
abbrev propSort : Expr := Expr.sort .zero
abbrev falseExpr : Expr := mkConst ``False []
abbrev trueExpr : Expr  := mkConst ``True []
abbrev falseBoolExpr : Expr := mkConst ``Bool.false []
abbrev trueBoolExpr : Expr  := mkConst ``Bool.true []
abbrev symbolsStringType : Expr := Expr.app (mkConst ``Symbols [Level.zero]) stringType
abbrev setStringType : Expr := Expr.app (mkConst ``Set [Level.zero]) stringType
abbrev setStringElemType (set : Expr) : Expr :=
    mkAppN (mkConst ``Set.Elem [Level.zero]) #[stringType, set]
abbrev subtypeTerm (term pred pf : Expr) : Expr :=
    mkAppN (mkConst ``Subtype.mk [1]) #[stringType, pred, term, pf]
abbrev setEmpty : Expr :=
    mkAppN (mkConst ``setOf [0]) #[stringType, .lam `x stringType falseExpr .default]
abbrev setUniv  : Expr :=
    Expr.app (mkConst ``Set.univ [Level.zero]) stringType
abbrev setSingleton (elem : Expr) : Expr :=
    mkAppN (mkConst ``Set.singleton [Level.zero]) #[stringType, elem]
abbrev listType (elems : Expr) : Expr :=
  Expr.app (mkConst ``List [Level.zero]) elems
abbrev mkList (type : Expr) (elems : Array Name) : Expr :=
    elems.foldr (λ nm acc => mkAppN (mkConst ``List.cons [0]) #[type, mkConst nm, acc]) (mkApp (mkConst ``List.nil [0]) type)
abbrev countableProp (set : Expr) : Expr := mkAppN (mkConst ``Countable [Level.zero]) #[stringType, set]
abbrev inhabitedType (type : Expr) : Expr := Expr.app (mkConst ``Inhabited [Level.zero]) type

/--
  Used to create expressions like:
    `if t1 == t2 then b1 else b2`
-/
abbrev eqIteExpr (cmpTy retTy s1 s2 b1 b2 : Expr) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar (type? := some $ mkAppN (mkConst ``DecidableEq [1]) #[cmpTy]) (kind := .synthetic)
  let succ ← synthesizeInstMVarCore mvar.mvarId!
  let inst ← instantiateMVars mvar
  unless succ do
    throwError "failed to synthesize DecidableEq instance"
  return mkAppN (mkConst ``ite [1])
    #[
      retTy,
      mkAppN (mkConst ``Eq [1]) #[cmpTy, s1, s2],
      mkAppN (mkConst ``decEq [1]) #[cmpTy, inst, s1, s2],
      b1, b2
    ]
def mkBEq (ty t1 t2 : Expr) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar (type? := some $ mkAppN (mkConst ``BEq [0]) #[ty]) (kind := .synthetic)
  let succ ← synthesizeInstMVarCore mvar.mvarId!
  let inst ← instantiateMVars mvar
  unless succ do
    throwError "failed to synthesize BEq instance"
  return mkAppN (mkConst ``BEq.beq [0]) #[ty, inst, t1, t2]

/--
  Used to create expressions like:
    `if domain == dom && range == rng && operator == op then b1 else b2`
-/
abbrev sigOpIteExpr (sortsType bvar2 dom bvar1 rng bvar0 op b1 b2 : Expr) : TermElabM Expr := do
  let check1 ← mkBEq (listType sortsType) bvar2 dom
  let check2 ← mkBEq sortsType  bvar1 rng
  let check3 ← mkBEq stringType bvar0 op
  let checks := mkAppN (mkConst ``Bool.and [])
        #[
          check1,
          mkAppN (mkConst ``Bool.and [])
          #[
            check2, check3
          ]
        ]
  let checksAsProp := mkAppN (mkConst ``Eq [1]) #[
    boolType,
    checks,
    trueBoolExpr
  ]
  return mkAppN (mkConst ``ite [1])
    #[
      boolType,
      checksAsProp,
      mkAppN (mkConst ``Bool.decEq) #[checks, trueBoolExpr],
      b1, b2
    ]
/--
  Used to create expressions like:
    `if s == SortS && str == string then b1 else b2`
-/
abbrev sigNomIteExpr (sortsType bvar1 st bvar0 str b1 b2 : Expr) : TermElabM Expr := do
  let mvar2 ← mkFreshExprMVar (type? := some $ mkAppN (mkConst ``BEq [0]) #[sortsType]) (kind := .synthetic)
  let succ ← synthesizeInstMVarCore mvar2.mvarId!
  let inst2 ← instantiateMVars mvar2
  unless succ do
    throwError "failed to synthesize BEq instance for Sorts.Elem"
  let mvar3 ← mkFreshExprMVar (type? := some $ mkAppN (mkConst ``BEq [0]) #[stringType]) (kind := .synthetic)
  let succ ← synthesizeInstMVarCore mvar3.mvarId!
  let inst3 ← instantiateMVars mvar3
  unless succ do
    throwError "failed to synthesize BEq instance for String"
  let check1 := mkAppN (mkConst ``BEq.beq [0]) #[sortsType, inst2, bvar1, st]
  let check2 := mkAppN (mkConst ``BEq.beq [0]) #[stringType, inst3, bvar0, str]
  let checks := mkAppN (mkConst ``Bool.and []) #[check1, check2]
  let checksAsProp := mkAppN (mkConst ``Eq [1]) #[
    boolType,
    checks,
    trueBoolExpr
  ]
  return mkAppN (mkConst ``ite [1])
    #[
      boolType,
      checksAsProp,
      mkAppN (mkConst ``Bool.decEq) #[checks, trueBoolExpr],
      b1, b2
    ]
