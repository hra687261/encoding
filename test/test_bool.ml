open Encoding
module Batch = Batch.Make (Z3_mappings)

let test_fun (module Batch : Batch_intf.S) =
  let symb_x = Expression.mk_symbol_s `BoolType "x" in
  let x = Expression.mk_symbol symb_x in
  let pc = [ Boolean.mk_not (Boolean.mk_eq x (Boolean.mk_val true)) ] in
  let solver = Batch.create () in
  assert (Batch.check solver pc);
  let m = Batch.model solver in
  Some (Value.Bool false) = Model.evaluate (Option.get m) symb_x

let%test "test_not_z3" = test_fun (module Batch.Make (Z3_mappings))
let%test "test_not_colibri2" = test_fun (module Batch.Make (Colibri2_mappings))
