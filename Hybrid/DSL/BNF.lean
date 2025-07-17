import Lean
import Hybrid.Language.Signature
import Hybrid.Language.Form

open Lean Elab Term Meta Std

/-
set_option trace.Elab.definition true
set_option pp.all true
set_option pp.rawOnError true
-/

declare_syntax_cat sort_ident
declare_syntax_cat nominal_ident
declare_syntax_cat operator_ident
declare_syntax_cat lean_type
declare_syntax_cat nominal_decl
declare_syntax_cat operator_decl
declare_syntax_cat production
declare_syntax_cat ssort
declare_syntax_cat sort_decl
declare_syntax_cat signature_decl
declare_syntax_cat inner_def

/-- Hybrid sort identifier -/
syntax ident : sort_ident
syntax ident : nominal_ident
syntax str   : operator_ident
/-- Lean builtin type, used as domain to model a given hybrid sort -/
syntax "builtin" ident : lean_type

/-- Hybrid constant nominal -/
syntax (lean_type <|> nominal_ident) : nominal_decl
syntax operator_ident "(" sort_ident,+ ")" : operator_decl
syntax nominal_decl   : production
syntax operator_decl  : production

/-- Declaration of a hybrid sort -/
syntax "subsort" sort_ident : ssort
syntax "sort " sort_ident "::=" sepBy1((ssort <|> production), "|") : sort_decl
syntax (sort_decl)* : signature_decl
syntax (name := inner_def) "```" signature_decl "```" : inner_def
syntax (name := language_def) "```" "hybrid_def" ident signature_decl "```" : term


/- Some helper expressions for the elaborators -/
abbrev StringExpr : Expr := Expr.const ``String []
abbrev SymbolsStringType : Expr := Expr.app (Expr.const ``Symbols [Level.zero]) StringExpr
abbrev SetStringType : Expr := Expr.app (Expr.const ``Set [Level.zero]) StringExpr
abbrev SetElem (set : Expr) : Expr :=
    mkAppN (Expr.const ``Set.Elem [Level.zero]) #[StringExpr, set]
abbrev SetUniv : Expr :=
    Expr.app (Expr.const ``Set.univ [Level.zero]) StringExpr
abbrev SetSingleton (elem : Expr) : Expr :=
    mkAppN (Expr.const ``Set.singleton [Level.zero]) #[StringExpr, elem]
abbrev ListType (elems : Expr) : Expr :=
  Expr.app (Expr.const ``List [Level.zero]) elems
abbrev OpsType (set : Expr) : Expr :=
    Expr.forallE `domain (ListType $ SetElem set)
      (Expr.forallE `range (SetElem set) SetStringType .default)
    .default
abbrev CountableProp (set : Expr) : Expr := mkAppN (Expr.const ``Countable [Level.zero]) #[StringExpr, set]
abbrev InhabitedType (type : Expr) : Expr := Expr.app (Expr.const ``Inhabited [Level.zero]) type

/--
  Consumes the name of the language definition, initializes the metavariable context
    and finally rewrites the syntax tree to an inner_def.

  TODO: this is just a draft, it creates metavariable expressions for the Symbols constructor
-/
@[term_elab language_def]
def hybrid_def_init : TermElab :=
  adaptExpander fun
  | `(``` hybrid_def $name:ident $decl:signature_decl ```), _ => do
        -- This is the metavariable for the actual Symbols term:
        let symbolsMvar ← mkFreshExprMVar SymbolsStringType (userName := `symbols_mvar)
        -- These are the metavariables for the values required for a Symbols constructor application.
        -- They should be iteratively assigned during further elaboration.
        let sortsMvar ← mkFreshExprMVar SetStringType (userName := `sorts_mvar)
        let opsMvar ← mkFreshExprMVar (OpsType sortsMvar) (userName := `ops_mvar)
        let ctNomMvar ← mkFreshExprMVar (Expr.forallE `s (SetElem sortsMvar) SetStringType .default) (userName := `ct_nom_mvar)
        let sortsCtblMvar ← mkFreshExprMVar (CountableProp sortsMvar) (userName := `sorts_ctbl_mvar)
        let opsCtblMvar ← mkFreshExprMVar
                (Expr.forallE `domain (ListType $ SetElem sortsMvar)
                  (Expr.forallE `range (SetElem sortsMvar)
                    (CountableProp (mkAppN opsMvar #[Expr.bvar 1, Expr.bvar 0]))
                  .default)
                .default)
              (userName := `ops_ctbl_mvar)
        let ctNomCtblMvar ← mkFreshExprMVar
                (Expr.forallE `s (SetElem sortsMvar)
                  (CountableProp (Expr.app ctNomMvar (Expr.bvar 0)))
                .default)
              (userName := `nom_ctbl_mvar)
        let sortsInhabitedMvar ← mkFreshExprMVar (InhabitedType sortsMvar) (userName := `sorts_inhabited_mvar)
        --let prop := Expr.forallE `s (SetElem sortsMvar) (SetSingleton (Expr.lit (Literal.strVal "p"))) .default
        let propMvar ← mkFreshExprMVar (Expr.forallE `s (SetElem sortsMvar) SetStringType .default) (userName := `prop_mvar)
        let nomMvar ← mkFreshExprMVar (Expr.forallE `s (SetElem sortsMvar) SetStringType .default) (userName := `nom_mvar)
        let svarMvar ← mkFreshExprMVar (Expr.forallE `s (SetElem sortsMvar) SetStringType .default) (userName := `svar_mvar)
        let propNonEmpty ← mkFreshExprMVar (Expr.forallE `s (InhabitedType (Expr.app propMvar (Expr.bvar 0))) SetStringType .default) (userName := `prop_non_empty_mvar)
        let propCtblMvar ← mkFreshExprMVar
                (Expr.forallE `s (SetElem sortsMvar)
                  (CountableProp (Expr.app propMvar (Expr.bvar 0)))
                .default)
              (userName := `prop_ctbl_mvar)
        let nomCtblMvar ← mkFreshExprMVar
                (Expr.forallE `s (SetElem sortsMvar)
                  (CountableProp (Expr.app nomMvar (Expr.bvar 0)))
                .default)
              (userName := `nom_ctbl_mvar)
        let svarCtblMvar ← mkFreshExprMVar
                (Expr.forallE `s (SetElem sortsMvar)
                  (CountableProp (Expr.app svarMvar (Expr.bvar 0)))
                .default)
              (userName := `svar_ctbl_mvar)

        -- Now unify the symbols metavar with the Expr of its constructor applied to the other metavars:
        let unification_success ← isDefEq symbolsMvar (mkAppN
          (Expr.const ``Symbols.mk [Level.zero])
          #[StringExpr,
            mkAppN (Expr.const ``Signature.mk [Level.zero]) #[StringExpr, sortsMvar, opsMvar, ctNomMvar, sortsCtblMvar, opsCtblMvar, ctNomCtblMvar, sortsInhabitedMvar],
            propMvar, nomMvar, svarMvar, propCtblMvar, nomCtblMvar, svarCtblMvar, propNonEmpty]
        )
        if !unification_success then
          panic! "Could not unify metavariables"
        else
          `(inner_def| ``` $decl:signature_decl ```)
  | _, _ => throwUnsupportedSyntax

/--
  Macro for unwinding productions chained with "|" in the first sort declaration,
    to two different sort declarations with no "|".
-/
@[macro inner_def]
def inner_def_unwind_decl : Macro
  | `(inner_def|
      ```   sort $s:sort_ident ::= $rule | $rules|*
            $decls*
      ```) =>
      `(inner_def|
      ``` sort $s ::= $rule
          sort $s ::= $rules|*
          $decls*
      ```)
  | __ => Macro.throwUnsupported

/--
  This elaborator for definitions takes care of definitions with at least one declaration.
  It needs to be ran inside `adaptExpander` because it mutates the syntax
    tree of the `hybrid_def`, like a macro:
  After processing the first declaration, it removes it from the syntax
    and keeps only the subsequent ones, which will be elaborated recursively.

  TODO: (Learn how to) implement me!
-/
@[term_elab inner_def]
def inner_def_elab_cons : TermElab :=
  adaptExpander fun
  | `(inner_def|
    ```   sort $s:sort_ident ::= $rule
          $decls*
    ```) => do
      logInfo m!"Sort '{s}'"
      logInfo m!"Rule: '{rule}'"
      `(inner_def|
      ```
            $[$decls]*
      ```)
  | _ => throwUnsupportedSyntax

/--
  This elaborator for definitions takes care of definitions with no declarations at all.
  It is responsible for final-stage plumbing, i.e. producing the actual
    `Symbols String` term that corresponds to the language definition, and
    making sure it is available in the local declaration context with the name
    given by the definition `$id`.
  Example: if we have `hybrid_def SMC`, once the full definition is parsed there
    should be a `SMC : Symbols String` variable declared in the context.

  TODO: (Learn how to) implement me!
-/
@[term_elab inner_def]
def inner_def_elab_nil : TermElab
  | `(inner_def| ``` ```), _ => do
        let mctx ← getMCtx
        let mvarId := mctx.userNames.find! `symbols_mvar
        return Expr.mvar mvarId
  | _, _ => throwUnsupportedSyntax

def language :=
```hybrid_def SMC
    sort Nat  ::= builtin Nat
    sort Bool ::= builtin Bool | "_==_"(Nat, Nat) | "_<=_"(Nat, Nat)

    sort Var  ::= builtin String
    sort AExp ::= subsort Nat | subsort Var
    sort AEXp ::= "_+_"(AExp, AExp) | "++"(Var)
    sort BExp ::= "_<=_"(AExp, AExp)
    sort Stmt ::= skip
                | "_:=_"(Var, AExp)
                | "if_then_else_"(BExp, Stmt, Stmt)
                | "while_do_"(BExp, Stmt)
                | "_;_"(Stmt, Stmt)

    sort Val ::= subsort Nat | subsort Bool
    sort ValStack ::= nil
                | "_._"(Val, ValStack)
    sort Mem ::= empty | "set"(Mem, Var, Nat)
    sort CtrlStack ::= "c"(AExp)
                | "c"(BExp)
                | "c"(Stmt)
                | "asgn"(Var)
                | plus | leq
                | "_?"(Val)
                | "_;_"(CtrlStack, CtrlStack)
    sort Config ::= "<_,_>"(ValStack, Mem)
```
