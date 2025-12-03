open Names

val declare_definition :
  poly_flags:SortPolyFlags.t -> Id.t -> Evd.evar_map -> EConstr.t -> Names.GlobRef.t
