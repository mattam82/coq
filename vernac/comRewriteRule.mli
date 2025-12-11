val do_symbols : poly:SortPolyFlags.t -> unfold_fix:bool ->
  (Vernacexpr.coercion_flag * ((Names.lident * Constrexpr.sort_poly_decl_expr option) list * Constrexpr.constr_expr)) list
  -> unit

val do_rules :
  poly:SortPolyFlags.t ->
  Names.Id.t ->
  (Constrexpr.sort_poly_decl_expr option * Constrexpr.constr_expr * Constrexpr.constr_expr) list ->
  unit
