open Encoding

module Test (Mapping : Mappings_intf.S) = struct
  module Batch = Batch.Make (Mapping)

  let solver = Batch.create ()
  let encode e = try ignore (Mapping.encode_expr e) with exn -> raise exn
  let one = Integer.mk_val Int.one
  let minus_one = Integer.mk_val Int.minus_one
  let zero = Integer.mk_val Int.zero
  let x = Expression.mk_symbol_s `IntType "x"

  (* Satisfiability *)
  let%test _ = Batch.check solver [ Integer.mk_gt x zero ]
  let%test _ = Batch.check solver [ Integer.mk_gt one minus_one ]
  let%test _ = Batch.check solver [ Integer.mk_eq (Integer.mk_pow x one) x ]
end

module Test_Z3 = Test (Z3_mappings)
module Test_Colibri2 = Test (Colibri2_mappings)
