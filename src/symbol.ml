(***************************************************************************)
(* This file is part of the third-party OCaml library `smtml`.             *)
(* Copyright (C) 2023-2024 formalsec                                       *)
(*                                                                         *)
(* This program is free software: you can redistribute it and/or modify    *)
(* it under the terms of the GNU General Public License as published by    *)
(* the Free Software Foundation, either version 3 of the License, or       *)
(* (at your option) any later version.                                     *)
(*                                                                         *)
(* This program is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           *)
(* GNU General Public License for more details.                            *)
(*                                                                         *)
(* You should have received a copy of the GNU General Public License       *)
(* along with this program.  If not, see <https://www.gnu.org/licenses/>.  *)
(***************************************************************************)

type t =
  { ty : Ty.t
  ; name : string
  }

let ( @: ) (name : string) (ty : Ty.t) : t = { name; ty }

let compare (t1 : t) (t2 : t) : int =
  let compare_name = String.compare t1.name t2.name in
  if compare_name = 0 then Ty.compare t1.ty t2.ty else compare_name

let equal (s1 : t) (s2 : t) : bool =
  Ty.equal s1.ty s2.ty && String.equal s1.name s2.name

let make (ty : Ty.t) (name : string) : t = name @: ty

let mk_symbol (ty : Ty.t) (name : string) : t = name @: ty

let pp (fmt : Fmt.formatter) ({ name; _ } : t) : unit = Fmt.string fmt name

let rename (symbol : t) (name : string) : t = { symbol with name }

let to_string ({ name; _ } : t) : string = name

let to_json ({ name; ty } : t) : Yojson.Basic.t =
  `Assoc [ (name, `Assoc [ ("ty", `String (Fmt.str "%a" Ty.pp ty)) ]) ]

let type_of ({ ty; _ } : t) : Ty.t = ty
