let declare_definition ~poly_flags name sigma body =
  let cinfo = Declare.CInfo.make ~name ~typ:None () in
  let info = Declare.Info.make ~poly_flags () in
  Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma
