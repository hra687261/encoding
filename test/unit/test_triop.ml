open Smtml
open Ty
open Expr
open Value

(* bool *)
let () =
  let i i = value (Int i) in
  assert (triop Ty_bool Ite (value True) (i 1) (i 0) = i 1);
  assert (triop Ty_bool Ite (value False) (i 1) (i 0) = i 0)

(* str *)
let () =
  let i i = value (Int i) in
  let v str = value (Str str) in
  assert (triop Ty_str String_extract (v "abcd") (i 1) (i 2) = v "bc");
  assert (triop Ty_str String_index (v "abcd") (v "bc") (i 0) = i 1);
  assert (triop Ty_str String_replace (v "abcd") (v "bc") (v "ef") = v "aefd")

(* list *)
let () =
  let i i = value (Int i) in
  let v l = value (List l) in
  assert (
    triop Ty_list List_set (v [ Int 0; Int 1; Int 2 ]) (i 1) (i 3)
    = v [ Int 0; Int 3; Int 2 ] )
