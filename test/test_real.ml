open Encoding

module Test (Mappings : Mappings_intf.S) = struct
  module Batch = Batch.Make (Mappings)

  let solver = Batch.create ()

  let%test "test-to_string-eq" =
    let x = Expression.mk_symbol_s `RealType "x"
    and y = Expression.mk_symbol_s `RealType "y" in
    Batch.check solver
      [ Strings.mk_eq (Real.mk_to_string x) (Real.mk_to_string y) ]
end

module Z3 = Test (Z3_mappings)
module C2 = Test (Colibri2_mappings)
