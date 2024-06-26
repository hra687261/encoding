open Smtml
open Ty
open Expr
open Value

(* bool *)
let () =
  let t = value True in
  let f = value False in
  assert (naryop Ty_bool Logand [ t; t; t; t ] = t);
  assert (naryop Ty_bool Logor [ f; f; f; f ] = f);
  assert (naryop Ty_bool Logand [ t; f; t ] = f);
  assert (naryop Ty_bool Logor [ f; t; f ] = t)

(* str *)
let () =
  let v s = value (Str s) in
  assert (naryop Ty_str Concat [ v "a"; v "b"; v "c" ] = v "abc");
  assert (naryop Ty_str Concat [ v "abc" ] = v "abc");
  assert (naryop Ty_str Concat [ v ""; v "" ] = v "")
