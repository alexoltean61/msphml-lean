import Lean
import Hybrid.BNF.Elab.Sort
import Hybrid.BNF.Helpers

open Lean Elab Command Term

structure OpSyntax where
  stx  : Syntax
  dom  : Array Syntax
  rng  : Syntax
  usrFacingName : Option Syntax

structure OpResolved where
  stx  : Syntax
  name : Name
  dom  : Array Name
  rng  : Name
  usrFacingName : Option Name
  usrFacingNameStx : Option Syntax

def outwardToName : Syntax → Name
  | .node _ `«outward_name[_]» #[_, .ident _ _ nm _, _] =>
        nm
  | s => panic! ("outwardToName: not a proper identifier: " ++ toString s)

def opIdentToName : Syntax → Array Name → Name → Name
  | .node _ `operator_ident_ #[.node _ `str #[.atom _ str] ], dom, rng =>
      let domStr : String := dom.foldr (λ nm str => nm.lastComponentAsString ++ "_" ++ str) ""
      let rngStr : String := rng.lastComponentAsString
      .str .anonymous $ ((str.dropPrefix "\"").toString.dropSuffix "\"").toString ++ domStr ++ rngStr
  | .node _ `ssortSubsort_ _, #[dom], rng =>
      .str .anonymous $ dom.lastComponentAsString.toLower ++ "2" ++ rng.lastComponentAsString
  | s, _, _ => panic! ("opIdentToName: not a proper identifier: " ++ toString s)

def resolveOp (nmspace : Name) : OpSyntax → CommandElabM OpResolved := λ ⟨stx, dom, rng, usr⟩ => do
  let resolvedDom ← dom.mapM (resolveSort nmspace)
  let resolvedRng ← resolveSort nmspace rng
  return {
    stx  := stx,
    name := opIdentToName stx resolvedDom resolvedRng,
    dom  := resolvedDom,
    rng  := resolvedRng,
    usrFacingName := outwardToName <$> usr
    usrFacingNameStx := usr
  }

/--
  Extracts an operator's name, domain and user facing name from a syntax node.
-/
def extractOp (rng : Syntax) : Syntax → Option OpSyntax
  | .node _ `sort_def__ #[.node _ `production__ #[.node _ `«operator_decl_(_)_» #[op, _, domCST, _, usrFacingCST] ] ] => do
      let dom := domCST.getArgs.filter isSortIdent -- remove commas, keep only sort identifiers
      let usrFacing := usrFacingCST.getOptional? -- keepstripPrefix none if no usr facing provided; remove brackets, keep only identifier
      return { stx := op, dom := dom, rng := rng, usrFacingName := usrFacing }
  | .node _ `sort_def__ #[op@(.node _ `ssortSubsort_ #[_, ssCst]) ] => do
      return { stx := op, dom := #[ssCst], rng := rng, usrFacingName := none }
  | _ => none

def gatherOpsFromDef (rng : Syntax) : Syntax.TSepArray `sort_def "|" → CommandElabM (Array OpSyntax) := λ ⟨defs⟩ => do
    let mut ops : Array OpSyntax := #[]
    for d in defs do
      let opStx := extractOp rng d
      match opStx with
      | some opStx =>
          ops := ops.push opStx
      | _ => pure ()
    return ops

def gatherOpsFromDecl : Syntax → CommandElabM (Array OpSyntax)
  | `(sort_decl| sort $name:sort_ident ::= $dfs:sort_def|* ) => do
        gatherOpsFromDef name dfs
  | _ => throwUnsupportedSyntax

def gatherOps : Syntax → CommandElabM (Array OpSyntax)
  | `(signature_decl| $ss:sort_decl* ) => do
        return (<- ss.mapM gatherOpsFromDecl).foldl (λ acc ops => ops ++ acc) #[]
  | _ => throwUnsupportedSyntax

def defineOps : Name → Name → Array OpResolved → TermElabM Name := λ nmspace sortsDecl ops => do
  let defName : Name := .str nmspace "Ops" -- e.g., def SMC.Ops := ...
  let sortsElemType := setStringElemType <| mkConst sortsDecl

  let mut predBody := falseBoolExpr
  for ⟨_, nm, dom, rng, _, _⟩ in ops do
      predBody ← sigOpIteExpr sortsElemType
          (.bvar 2) (mkList sortsElemType dom)   -- domain == dom
          (.bvar 1) (mkConst rng)                -- range == rng
          (.bvar 0) (mkStrLit nm.lastComponentAsString)       -- operator == op
          trueBoolExpr predBody
  predBody := mkAppN (mkConst ``Eq [1]) #[boolType, predBody, trueBoolExpr]
  let pred : Expr :=
      .lam `domain (listType sortsElemType) (
        .lam `range sortsElemType (
          .lam `operator stringType
            predBody
          .default
        )
        .default
      )
      .default
  let set  := mkAppN (mkConst ``setOf [0]) #[stringType, mkAppN pred #[.bvar 1, .bvar 0] ]
  let sortedSet : Expr :=
      .lam `domain (listType sortsElemType) (
        .lam `range sortsElemType set .default
      ) .default
  addAndCompile
    (.defnDecl
      {
        name   := defName
        levelParams := []
        type   := .forallE `domain (listType sortsElemType) (.forallE `range sortsElemType setStringType .default) .default
        value  :=  sortedSet
        hints  := .abbrev
        safety := .safe
      }
    )
  setReducibilityStatus defName .reducible

  for ⟨stx, nm, dom, rng, usrFacing, usrFacingStx⟩ in ops do
    let declName := match usrFacing with
                    | some usrNm => .str nmspace usrNm.lastComponentAsString
                    | none => .str nmspace nm.lastComponentAsString
    let domExprs : Expr := mkList sortsElemType dom
    let rngExpr  : Expr := mkConst rng
    let declType := setStringElemType $ mkAppN (mkConst defName) #[domExprs, rngExpr]
    addAndCompile
      (.defnDecl
        {
          name   := declName
          levelParams := []
          type   := declType
          value  := subtypeTerm (mkStrLit nm.lastComponentAsString) (mkAppN pred #[domExprs, rngExpr]) (rflExpr boolType trueBoolExpr)
          hints  := .abbrev
          safety := .safe
        }
      )
    setReducibilityStatus declName .reducible
    match usrFacingStx with
    | some usrStx =>
        discard <| addTermInfo stx (mkConst declName []) (expectedType? := some declType) (isBinder := false)
        discard <| addTermInfo usrStx (mkConst declName []) (expectedType? := some declType) (isBinder := true)
    | none =>
        discard <| addTermInfo stx (mkConst declName []) (expectedType? := some declType) (isBinder := true)
  return defName
