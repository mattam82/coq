val do_symbols : poly:bool -> sort_poly:bool -> unfold_fix:bool ->
  (Vernacexpr.coercion_flag * ((Names.lident * Constrexpr.sort_poly_decl_expr option) list * Constrexpr.constr_expr)) list
  -> unit

val do_rules :
  sort_poly:bool ->
  Names.Id.t ->
  (Constrexpr.sort_poly_decl_expr option * Constrexpr.constr_expr * Constrexpr.constr_expr) list ->
  unit
