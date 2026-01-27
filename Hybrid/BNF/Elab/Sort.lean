import Lean
import Hybrid.BNF.Syntax
import Hybrid.BNF.Helpers

open Lean Elab Command Term

def sortIdentToName : Syntax → Name
  | .node _ `sort_ident_ #[.ident _ _ str _] => str
  | s => panic! ("sortIdentToName: not a proper identifier: " ++ toString s)

def isSortIdent : Syntax → Bool
  | .node _ `sort_ident_ #[.ident _ _ _ _] => true
  | _ => false

def gatherSortName : Syntax → CommandElabM (Syntax × Name)
  | `(sort_decl| sort $ident:sort_ident ::= $_ ) =>
        return ⟨ident, sortIdentToName ident⟩
  | _ => throwUnsupportedSyntax

def gatherSortNames : Syntax → CommandElabM (Array (Syntax × Name))
  | `(signature_decl| $ss:sort_decl* ) => ss.mapM gatherSortName
  | _ => throwUnsupportedSyntax

def resolveSort (nmspace : Name) : Syntax → CommandElabM Name := λ stx => do
    let globalStNm := Name.str nmspace (sortIdentToName stx).lastComponentAsString
    let resolved ← liftCoreM <| resolveGlobalName globalStNm
    match resolved with
    | [⟨nm, _⟩] =>
        -- Add hover info to syntax:
        liftTermElabM <| discard <| addTermInfo stx (mkConst nm [])
        return nm
    | [] => throwErrorAt stx "can't resolve sort identifier"
    | _  => throwErrorAt stx "ambiguous sort identifier (likely bug)"

def defineSorts : Name → Array (Syntax × Name) → TermElabM Name := λ nmspace sortNames => do
  let defName : Name := .str nmspace "Sorts" -- e.g., def SMC.Sorts := ...

  -- Construct a predicate (λ str => predBody), where predBody is obtained
  -- by iterating through all sort names and acummulating the body with the operation
  --    body := if str == ident then true else body
  -- starting with value false.
  let mut predBody := falseBoolExpr
  -- Little hack to avoid duplicates, fixme sometime:
  let mut visited: Name → Bool := λ _ => False
  for ⟨_, nm⟩ in sortNames do
    if !visited nm then
      predBody ← eqIteExpr stringType boolType (.bvar 0) (mkStrLit nm.lastComponentAsString) trueBoolExpr predBody
      visited  := λ i => if i == nm then true else visited i
  predBody := mkAppN (mkConst ``Eq [1]) #[boolType, predBody, trueBoolExpr]
  let pred := Expr.lam `str stringType predBody .default

  -- Declare def SMC.Sorts := { str | pred str }:
  let set  := mkAppN (mkConst ``setOf [0]) #[stringType, pred]
  addAndCompile
    (.defnDecl
      {
        name   := defName
        levelParams := []
        type   := setStringType
        value  := set
        hints  := .abbrev
        safety := .safe
      }
    )
  setReducibilityStatus defName .reducible

  visited := λ _ => False
  -- Now iterate through names again and declare each individual sort
  -- as an elem of SMC.Sorts & add hover info pointing to declaration:
  for ⟨stx, nm⟩ in sortNames do
    let declName := Name.str nmspace nm.lastComponentAsString
    let declType := setStringElemType (mkConst defName [])
    -- Don't want to declare the same sort twice if more than one "sort S ::=" row exists:
    if !visited nm then
      addAndCompile
        (.defnDecl
          {
            name   := declName
            levelParams := []
            type   := declType
            value  := subtypeTerm (mkStrLit nm.lastComponentAsString) pred (rflExpr boolType trueBoolExpr)
            hints  := .abbrev
            safety := .safe
          }
        )
      setReducibilityStatus declName .reducible
      visited := λ i => if i == nm then true else visited i
    -- But for all "sort S ::=" rows, want to add hover info pointing to declaration:
    discard <| addTermInfo stx (mkConst declName []) (expectedType? := some declType) (isBinder := true)
    addConstInfo (mkIdent declName) declName
  return defName
