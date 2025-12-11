open Names

val declare_definition :
  poly:SortPolyFlags.t -> Id.t -> Evd.evar_map -> EConstr.t -> Names.GlobRef.t
