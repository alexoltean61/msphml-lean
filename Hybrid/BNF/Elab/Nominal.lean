import Lean
import Hybrid.BNF.Elab.Sort
import Hybrid.BNF.Helpers

open Lean Elab Command Term Meta

structure NomSyntax where
  stx   : Syntax
  st    : Syntax

structure NomResolved where
  stx   : Syntax
  name  : Name
  st    : Name

structure BuiltinSyntax where
  stx   : Syntax
  tp    : Syntax
  st    : Syntax

structure BuiltinResolved where
  stx   : Syntax
  tp    : Name
  st    : Name

def nomIdentToName : Syntax → Name
  | .node _ `nominal_ident_ #[.ident _ _ str _] => str
  | s => panic! ("nomIdentToName: not a proper identifier: " ++ toString s)

def extractNom (st : Syntax) : Syntax → Option NomSyntax
  | .node _ `sort_def__ #[.node _ `production__ #[.node _ `nominal_decl__ #[stx@(.node _ `nominal_ident_ #[_]) ] ] ] => do
      return { stx := stx, st := st }
  | _ => none

def gatherNomsFromDef (rng : Syntax) : Syntax.SepArray "|" → CommandElabM (Array NomSyntax) := λ ⟨defs⟩ => do
    let mut noms : Array NomSyntax := #[]
    for d in defs do
      let nomStx := extractNom rng d
      match nomStx with
      | some nomStx =>
          noms := noms.push nomStx
      | _ => pure ()
    return noms

def gatherNomsFromDecl : Syntax → CommandElabM (Array NomSyntax)
  | `(sort_decl| sort $name:sort_ident ::= $dfs:sort_def|* ) => do
        gatherNomsFromDef name dfs
  | _ => throwUnsupportedSyntax

def gatherNoms : Syntax → CommandElabM (Array NomSyntax)
  | `(signature_decl| $ss:sort_decl* ) => do
        return (<- ss.mapM gatherNomsFromDecl).foldl (λ acc noms => noms ++ acc) #[]
  | _ => throwUnsupportedSyntax

def resolveNom (nmspace : Name) : NomSyntax → CommandElabM NomResolved := λ ⟨stx, st⟩ => do
  return {
    stx  := stx,
    name := nomIdentToName stx,
    st   := ← resolveSort nmspace st
  }

def extractBuiltin (st : Syntax) : Syntax → Option BuiltinSyntax
  | .node _ `sort_def__ #[.node _ `production__ #[.node _ `nominal_decl__ #[stx@(.node _ `lean_typeBuiltin_ #[_, tp]) ] ] ] => do
      return { stx := stx, tp := tp, st := st }
  | _ => none

def gatherBuiltinsFromDef (rng : Syntax) : Syntax.SepArray "|" → CommandElabM (Array BuiltinSyntax) := λ ⟨defs⟩ => do
    let mut noms : Array BuiltinSyntax := #[]
    for d in defs do
      let bltStx := extractBuiltin rng d
      match bltStx with
      | some bltStx => noms := noms.push bltStx
      | _ => pure ()
    return noms

def gatherBuiltinsFromDecl : Syntax → CommandElabM (Array BuiltinSyntax)
  | `(sort_decl| sort $name:sort_ident ::= $dfs:sort_def|* ) => do
        gatherBuiltinsFromDef name dfs
  | _ => throwUnsupportedSyntax

def gatherBuiltins : Syntax → CommandElabM (Array BuiltinSyntax)
  | `(signature_decl| $ss:sort_decl* ) => do
        return (<- ss.mapM gatherBuiltinsFromDecl).foldl (λ acc blt => blt ++ acc) #[]
  | _ => throwUnsupportedSyntax

def resolveBuiltin (nmspace : Name) : BuiltinSyntax → CommandElabM BuiltinResolved := λ ⟨stx, tp, st⟩ => do
  let resolvedType ← liftCoreM <| resolveGlobalName tp.getId
    match resolvedType with
    | [⟨resolvedType, _⟩] =>
        -- Add hover info to syntax:
        liftTermElabM <| discard <| addTermInfo stx (mkConst resolvedType [])
        return {
          stx  := stx,
          tp   := resolvedType,
          st   := ← resolveSort nmspace st
        }
    | [] => throwErrorAt stx "can't resolve builtin type identifier"
    | _  => throwErrorAt stx "ambiguous builtin type identifier"

def defineNoms : Name → Name → Array NomResolved → Array BuiltinResolved → TermElabM Name := λ nmspace sortsDecl noms builtins => do
  let defName : Name := .str nmspace "CtNoms" -- e.g., def SMC.CtNoms := ...
  let sortsElemType := setStringElemType <| mkConst sortsDecl
  -- Handle regular nominals first
  let mut predBody ← mkBEq stringType (.bvar 0) (mkStrLit "⟨default⟩")
  for ⟨_, name, st⟩ in noms do
      predBody ← sigNomIteExpr sortsElemType
          (.bvar 1) (mkConst st)
          (.bvar 0) (mkStrLit name.lastComponentAsString)
          trueBoolExpr predBody
  predBody := mkAppN (mkConst ``Eq [1]) #[boolType, predBody, trueBoolExpr]
  predBody := .lam `str stringType predBody .default
  -- Then handle builtins
  for ⟨stx, tp, st⟩ in builtins do
    let tpExpr : Expr := mkConst tp
    -- Try to fetch ToString instance for given type, throw error if none
    let mvar ← mkFreshExprMVar (type? := some $ mkAppN (mkConst ``ToString [0]) #[tpExpr]) (kind := .synthetic)
    let succ ← synthesizeInstMVarCore mvar.mvarId!
    let inst ← instantiateMVars mvar
    unless succ do
      throwErrorAt stx "failed to synthesize ToString instance"
    predBody ← eqIteExpr sortsElemType (.forallE `str stringType (.sort 0) .default)
                 (.bvar 0) (mkConst st)  -- if s == st then λ ... else predBody
                  (.lam `str stringType
                      (mkAppN (mkConst ``Exists [1])
                        #[mkConst tp, .lam `n (mkConst tp)
                            (mkAppN (mkConst ``Eq [1]) #[stringType, .bvar 1, mkAppN (mkConst ``ToString.toString [0]) #[tpExpr, inst, .bvar 0] ])
                         .default])
                    .default)
                  predBody
  let pred := .lam `s sortsElemType predBody .default
  let set  := mkAppN (mkConst ``setOf [0]) #[stringType, mkAppN pred #[.bvar 0] ]
  let sortedSet : Expr := .lam `s sortsElemType set .default
  addAndCompile -- TODO: ensure no declaration with the same name exists in the namespace!
    (.defnDecl
      {
        name   := defName
        levelParams := []
        type   := .forallE `s sortsElemType setStringType .default
        value  :=  sortedSet
        hints  := .abbrev
        safety := .safe
      }
    )
  setReducibilityStatus defName .reducible
  -- Then declare each individual non builtin nominal
  for ⟨stx, nm, st⟩ in noms do
    let declName := .str nmspace nm.lastComponentAsString
    let stExpr   : Expr := mkConst st
    let declType := setStringElemType $ mkAppN (mkConst defName) #[stExpr]
    addAndCompile -- TODO: ensure no declaration with the same name exists in the namespace!
      (.defnDecl
        {
          name   := declName
          levelParams := []
          type   := declType
          value  := subtypeTerm (mkStrLit nm.lastComponentAsString) (mkAppN pred #[stExpr]) (rflExpr boolType trueBoolExpr)
          hints  := .abbrev
          safety := .safe
        }
      )
    setReducibilityStatus declName .reducible
    discard <| addTermInfo stx (mkConst declName []) (expectedType? := some declType) (isBinder := true)
  return defName
