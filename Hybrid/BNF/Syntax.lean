declare_syntax_cat sort_ident
declare_syntax_cat nominal_ident
declare_syntax_cat operator_ident
declare_syntax_cat lean_type
declare_syntax_cat nominal_decl
declare_syntax_cat operator_decl
declare_syntax_cat outward_name
declare_syntax_cat production
declare_syntax_cat ssort
declare_syntax_cat sort_decl
declare_syntax_cat signature_decl
declare_syntax_cat sort_def
declare_syntax_cat sort_defs

/-- Hybrid sort identifier -/
syntax ident : sort_ident
syntax ident : nominal_ident
syntax str   : operator_ident
/-- Lean builtin type, used as domain to model a given hybrid sort -/
syntax "builtin" ident : lean_type

/-- Hybrid constant nominal -/
syntax (lean_type <|> nominal_ident) : nominal_decl
syntax "[" ident "]" : outward_name
syntax operator_ident "(" sort_ident,+ ")" optional(outward_name) : operator_decl
syntax (nominal_decl <|> operator_decl) : production

/-- Declaration of a hybrid sort -/
syntax "subsort" sort_ident : ssort
syntax (ssort <|> production) : sort_def
syntax sepBy1(sort_def, "|") : sort_defs
syntax "sort " sort_ident "::=" sort_defs : sort_decl
syntax (sort_decl)* : signature_decl
syntax (name := language_def) "hybrid_def" ident ":=" signature_decl : command
