module Fresh = struct
  module Expr = Colibri2_core.Expr
  module Ty = Expr.Ty
  module Term = Expr.Term
  module A = Colibri2_stdlib.Std.A
  module LRA = Colibri2_theories_LRA
  module Scheduler = Colibri2_solver.Scheduler
  module Context = Colibri2_stdlib.Context
  module Interp = Colibri2_core.Interp
  module Uninterp = Colibri2_theories_quantifiers.Uninterp
  module Ground = Colibri2_core.Ground
  module IArray = Colibri2_popop_lib.IArray
  module Egraph = Colibri2_core.Egraph

  module Var = struct
    include Term.Var

    let is_int _ = false
    let print = pp
  end

  module Ex = struct
    type t = unit

    let print fmt () = Fmt.pf fmt "()"
    let empty = ()
    let union () () = ()
  end

  module Rat = struct
    include A

    let m_one = A.minus_one
    let print = A.pp
    let is_int = A.is_integer
    let is_zero v = A.equal v A.zero
    let is_one v = A.equal v A.one
    let mult = A.mul
    let minus = A.neg
    let is_m_one v = A.equal v m_one
    let ceiling = ceil
  end

  module Make () = struct
    exception Error of string

    type expr = Term.t

    type model =
      Colibri2_core.Egraph.wt * (Term.Const.t * Colibri2_core.Value.t) list

    module Sim = OcplibSimplex.Basic.Make (Var) (Rat) (Ex)

    type optimize = Sim.Core.t
    type handle = optimize * (Sim.Core.P.t * bool) option

    type solver =
      { mutable scheduler : Scheduler.t
      ; mutable pushpop : Scheduler.bp list
      ; mutable state :
          [ `Sat of Colibri2_core.Egraph.wt
          | `Unknown of Colibri2_core.Egraph.wt
          | `Search
          | `Unsat
          | `StepLimitReached
          ]
      ; mutable status_colibri :
          [ `No | `Sat | `Unsat | `Unknown | `StepLimitReached ] Context.Ref.t
      ; mutable decls : Term.Const.S.t
      }

    type status =
      [ `Sat of Colibri2_core.Egraph.wt
      | `Unknown of Colibri2_core.Egraph.wt
      | `Search
      | `Unsat
      | `StepLimitReached
      ]

    (* additional builtins *)

    let string_ty_cst : Expr.Term.ty_const =
      Expr.Id.mk ~builtin:Expr.Base
        (Dolmen_std.Path.global "StringTy")
        Expr.{ arity = 0; alias = No_alias }

    let string_ty = Ty.apply string_ty_cst []
    let float32_ty = Ty.float 8 24
    let float64_ty = Ty.float 11 53

    let int_to_string : Expr.term_cst =
      Expr.Id.mk ~name:"IntToString" ~builtin:Expr.Base
        (Dolmen_std.Path.global "IntToString")
        (Ty.arrow [ Ty.int ] string_ty)

    let string_to_int : Expr.term_cst =
      Expr.Id.mk ~name:"StringToInt" ~builtin:Expr.Base
        (Dolmen_std.Path.global "StringToInt")
        (Ty.arrow [ string_ty ] Ty.int)

    let real_to_string : Expr.term_cst =
      Expr.Id.mk ~name:"RealToString" ~builtin:Expr.Base
        (Dolmen_std.Path.global "RealToString")
        (Ty.arrow [ Ty.real ] string_ty)

    let string_to_real : Expr.term_cst =
      Expr.Id.mk ~name:"StringToReal" ~builtin:Expr.Base
        (Dolmen_std.Path.global "StringToReal")
        (Ty.arrow [ string_ty ] Ty.real)

    let real_to_uint32 : Expr.term_cst =
      Expr.Id.mk ~name:"RealToUInt32" ~builtin:Expr.Base
        (Dolmen_std.Path.global "RealToUInt32")
        (Ty.arrow [ Ty.real ] Ty.real)

    let trim_string : Expr.term_cst =
      Expr.Id.mk ~name:"TrimString" ~builtin:Expr.Base
        (Dolmen_std.Path.global "TrimString")
        (Ty.arrow [ string_ty ] string_ty)

    let f32_to_string : Expr.term_cst =
      Expr.Id.mk ~name:"F32ToString" ~builtin:Expr.Base
        (Dolmen_std.Path.global "F32ToString")
        (Ty.arrow [ float32_ty ] string_ty)

    let string_to_f32 : Expr.term_cst =
      Expr.Id.mk ~name:"StringToF32" ~builtin:Expr.Base
        (Dolmen_std.Path.global "StringToF32")
        (Ty.arrow [ string_ty ] float32_ty)

    let f64_to_string : Expr.term_cst =
      Expr.Id.mk ~name:"F64ToString" ~builtin:Expr.Base
        (Dolmen_std.Path.global "F64ToString")
        (Ty.arrow [ float64_ty ] string_ty)

    let string_to_f64 : Expr.term_cst =
      Expr.Id.mk ~name:"StringToF64" ~builtin:Expr.Base
        (Dolmen_std.Path.global "StringToF64")
        (Ty.arrow [ string_ty ] float64_ty)

    module SHT = Hashtbl.Make (Symbol)

    let tty_of_etype (e : Types.expr_type) : Term.ty =
      match e with
      | `IntType -> Ty.int
      | `RealType -> Ty.real
      | `BoolType -> Ty.bool
      | `StrType -> string_ty
      | `I32Type -> Ty.bitv 32
      | `I64Type -> Ty.bitv 64
      | `F32Type -> float32_ty
      | `F64Type -> float64_ty

    let tty_to_etype (ty : Term.ty) =
      match ty with
      | { ty_descr = TyApp ({ builtin = Expr.Int; _ }, _); _ } -> `IntType
      | { ty_descr = TyApp ({ builtin = Expr.Real; _ }, _); _ } -> `RealType
      | { ty_descr = TyApp ({ builtin = Expr.Prop; _ }, _); _ } -> `BoolType
      | { ty_descr =
            TyApp
              ( { builtin = Expr.Base
                ; path = Absolute { name = "StringTy"; _ }
                ; _
                }
              , _ )
        ; _
        } ->
        `StrType
      | { ty_descr = TyApp ({ builtin = Expr.Bitv 32; _ }, _); _ } -> `I32Type
      | { ty_descr = TyApp ({ builtin = Expr.Bitv 64; _ }, _); _ } -> `I64Type
      | { ty_descr = TyApp ({ builtin = Expr.Float (8, 24); _ }, _); _ } ->
        `F32Type
      | { ty_descr = TyApp ({ builtin = Expr.Float (11, 53); _ }, _); _ } ->
        `F64Type
      | _ -> assert false

    let sym_cache = SHT.create 17

    let tcst_of_symbol (s : Symbol.t) =
      match SHT.find_opt sym_cache s with
      | None ->
        let x = Symbol.to_string s
        and t = Symbol.type_of s in
        let cst = Term.Const.mk (Dolmen_std.Path.global x) (tty_of_etype t) in
        SHT.add sym_cache s cst;
        cst
      | Some c -> c

    let tcst_to_symbol (c : Expr.term_cst) : Symbol.t =
      match c with
      | { builtin = Expr.Base
        ; path = Local { name } | Absolute { name; _ }
        ; id_ty
        ; _
        } ->
        Symbol.mk_symbol (tty_to_etype id_ty) name
      | _ -> assert false

    module I :
      Op_intf.S
        with type v := int
         and type t := expr
         and type unop := Types.I.unop
         and type binop := Types.I.binop
         and type relop := Types.I.relop
         and type cvtop := Types.I.cvtop
         and type triop := Types.I.triop = struct
      open Z3
      open Types.I

      let encode_val i = Term.Int.mk (Int.to_string i)

      let encode_unop op e =
        let op' = match op with Neg -> Term.Int.minus in
        op' e

      let encode_binop op e1 e2 =
        let op' =
          match op with
          | Add -> Term.Int.add
          | Sub -> Term.Int.sub
          | Mul -> Term.Int.mul
          | Div -> Term.Int.div
          | Rem -> Term.Int.rem
          | Pow ->
            fun e1 e2 ->
              Term.apply_cst
                Colibri2_theories_LRA.RealValue.Builtin.colibri_pow_int_int []
                [ e1; e2 ]
          | _ -> raise (Error "Unsupported integer operations")
        in
        op' e1 e2

      let encode_relop op e1 e2 =
        let op' =
          match op with
          | Eq -> Term.eq
          | Ne -> Term.neq
          | Lt -> Term.Int.lt
          | Gt -> Term.Int.gt
          | Le -> Term.Int.le
          | Ge -> Term.Int.ge
        in
        op' e1 e2

      let encode_cvtop op e =
        let op' =
          match op with
          | ToString -> fun v -> Term.apply_cst int_to_string [] [ v ]
          | OfString -> fun v -> Term.apply_cst string_to_int [] [ v ]
          | ReinterpretReal -> assert false
        in
        op' e

      let encode_triop _op _e1 _e2 _e3 = assert false
    end

    module Real :
      Op_intf.S
        with type v := float
         and type t := expr
         and type unop := Types.R.unop
         and type binop := Types.R.binop
         and type relop := Types.R.relop
         and type cvtop := Types.R.cvtop
         and type triop := Types.R.triop = struct
      open Types.R

      let encode_val f = Term.Real.mk (Float.to_string f)

      let encode_unop op e =
        let op' =
          match op with
          | Neg -> Term.Real.minus
          | Abs -> assert false
          | Sqrt -> assert false
          | Ceil -> Term.Real.ceiling
          | Floor -> Term.Real.floor
          | Nearest | IsNan -> assert false
        in
        op' e

      let encode_binop op e1 e2 =
        let op' =
          match op with
          | Add -> Term.Real.add
          | Sub -> Term.Real.sub
          | Mul -> Term.Real.mul
          | Div -> Term.Real.div
          | Min -> assert false
          | Max -> assert false
          | _ -> assert false
        in
        op' e1 e2

      let encode_relop op e1 e2 =
        let op' =
          match op with
          | Eq -> Term.eq
          | Ne -> Term.neq
          | Lt -> Term.Real.lt
          | Gt -> Term.Real.gt
          | Le -> Term.Real.le
          | Ge -> Term.Real.ge
        in
        op' e1 e2

      let encode_cvtop op e =
        let op' =
          match op with
          | ToString -> fun v -> Term.apply_cst real_to_string [] [ v ]
          | OfString -> fun v -> Term.apply_cst string_to_real [] [ v ]
          | ConvertUI32 -> fun t -> Term.apply_cst real_to_uint32 [] [ t ]
          | ReinterpretInt -> Term.Int.to_real
          | DemoteF64 | ConvertSI32 | ConvertSI64 | ConvertUI64 | PromoteF32 ->
            assert false
        in
        op' e

      let encode_triop _op _e1 _e2 _e3 = assert false
    end

    module Boolean :
      Op_intf.S
        with type v := bool
         and type t := expr
         and type unop := Types.B.unop
         and type binop := Types.B.binop
         and type relop := Types.B.relop
         and type cvtop := Types.B.cvtop
         and type triop := Types.B.triop = struct
      open Types.B

      let encode_val = function
        | true -> Term.of_cst Term.Const._true
        | false -> Term.of_cst Term.Const._false

      let encode_unop op e =
        let op' = match op with Not -> Term.neg in
        op' e

      let encode_binop op e1 e2 =
        let op' =
          match op with
          | And -> fun a b -> Term._and [ a; b ]
          | Or -> fun a b -> Term._or [ a; b ]
          | Xor -> Term.xor
        in
        op' e1 e2

      let encode_relop op e1 e2 =
        let op' = match op with Eq -> Term.eq | Ne -> Term.neq in
        op' e1 e2

      let encode_cvtop _op _e = assert false

      let encode_triop op e1 e2 e3 =
        let op' = match op with ITE -> Term.ite in
        op' e1 e2 e3
    end

    module Str :
      Op_intf.S
        with type v := string
         and type t := expr
         and type unop := Types.S.unop
         and type binop := Types.S.binop
         and type relop := Types.S.relop
         and type cvtop := Types.S.cvtop
         and type triop := Types.S.triop = struct
      open Types.S

      let encode_val _ = assert false

      let encode_unop op e =
        let op' =
          match op with Len -> assert false | Trim -> fun _v -> assert false
        in
        op' e

      let encode_binop op _e1 _e2 =
        let op' =
          match op with Nth -> assert false | Concat -> assert false
        in
        op'

      let encode_relop op =
        let op' = match op with Eq -> Term.eq | Ne -> Term.neq in
        op'

      let encode_triop op _e1 _e2 _e3 =
        let op' = match op with SubStr -> assert false in
        op'

      let encode_cvtop _op _e = assert false
    end

    module BV = struct
      open BvOp

      let encode_unop op e =
        let op' =
          match op with
          | Not -> Term.Bitv.neg
          | Clz -> failwith "I32: Clz not supported yet"
        in
        op' e

      let encode_binop op e1 e2 =
        let op' =
          match op with
          | Add -> Term.Bitv.add
          | Sub -> Term.Bitv.sub
          | Mul -> Term.Bitv.mul
          | DivS -> Term.Bitv.sdiv
          | DivU -> Term.Bitv.udiv
          | And -> Term.Bitv.and_
          | Xor -> Term.Bitv.xor
          | Or -> Term.Bitv.or_
          | Shl -> Term.Bitv.shl
          | ShrS -> assert false
          | ShrU -> assert false
          | RemS -> Term.Bitv.srem
          | RemU -> Term.Bitv.urem
          | ExtendS -> assert false
          | ExtendU -> assert false
          | Rotl | Rotr -> failwith "z3_mappings: rotl|rotr not implemented!"
        in
        op' e1 e2

      let encode_relop op e1 e2 =
        let op' =
          match op with
          | Eq -> Term.eq
          | Ne -> Term.neq
          | LtU -> Term.Bitv.ult
          | LtS -> Term.Bitv.slt
          | LeU -> Term.Bitv.ule
          | LeS -> Term.Bitv.sle
          | GtU -> Term.Bitv.ugt
          | GtS -> Term.Bitv.sgt
          | GeU -> Term.Bitv.uge
          | GeS -> Term.Bitv.sge
        in
        op' e1 e2
    end

    module I32 :
      Op_intf.S
        with type v := int32
         and type t := expr
         and type unop := Types.I32.unop
         and type binop := Types.I32.binop
         and type relop := Types.I32.relop
         and type cvtop := Types.I32.cvtop
         and type triop := Types.I32.triop = struct
      open Types.I32

      let encode_val i =
        Term.Bitv.mk
          (Dolmen_type.Misc.Bitv.parse_decimal ("bv" ^ Int32.to_string i) 32)

      let encode_unop = BV.encode_unop
      let encode_binop = BV.encode_binop
      let encode_relop = BV.encode_relop

      let encode_cvtop op e =
        let op' =
          match op with
          | WrapI64 -> assert false
          | TruncSF32 | TruncSF64 ->
            Term.Float.to_sbv 32 Term.Float.roundTowardZero
          | TruncUF32 | TruncUF64 ->
            Term.Float.to_ubv 32 Term.Float.roundTowardZero
          | ReinterpretFloat -> Term.Float.ieee_format_to_fp 8 24
          | ToBool -> encode_relop Ne (encode_val 0l)
          | OfBool -> fun e -> Term.ite e (encode_val 1l) (encode_val 0l)
          | ExtendSI32 | ExtendUI32 -> assert false
        in
        op' e

      let encode_triop _op _e1 _e2 _e3 = assert false
    end

    module I64 :
      Op_intf.S
        with type v := int64
         and type t := expr
         and type unop := Types.I64.unop
         and type binop := Types.I64.binop
         and type relop := Types.I64.relop
         and type cvtop := Types.I64.cvtop
         and type triop := Types.I64.triop = struct
      open Types.I64

      let encode_val i =
        Term.Bitv.mk
          (Dolmen_type.Misc.Bitv.parse_decimal ("bv" ^ Int64.to_string i) 64)

      let encode_unop = BV.encode_unop
      let encode_binop = BV.encode_binop
      let encode_relop = BV.encode_relop

      let encode_cvtop op e =
        let op' =
          match op with
          | ExtendSI32 -> Term.Bitv.sign_extend 32
          | ExtendUI32 -> Term.Bitv.zero_extend 32
          | TruncSF32 | TruncSF64 ->
            Term.Float.to_sbv 64 Term.Float.roundTowardZero
          | TruncUF32 | TruncUF64 ->
            Term.Float.to_ubv 64 Term.Float.roundTowardZero
          | ReinterpretFloat -> Term.Float.ieee_format_to_fp 11 51
          | ToBool -> encode_relop Ne (encode_val 0L)
          | OfBool -> fun e -> Term.ite e (encode_val 1L) (encode_val 0L)
          | WrapI64 -> assert false
        in
        op' e

      let encode_triop _op _e1 _e2 _e3 = assert false
    end

    module Float = struct
      open FloatOp

      let encode_unop op e =
        let op' =
          match op with
          | Neg -> Term.Float.neg
          | Abs -> Term.Float.abs
          | Sqrt -> Term.Float.sqrt Term.Float.roundNearestTiesToEven
          | Nearest ->
            Term.Float.roundToIntegral Term.Float.roundNearestTiesToEven
          | IsNan -> Term.Float.isNaN
          | Ceil -> assert false
          | Floor -> assert false
        in
        op' e

      let encode_binop op e1 e2 =
        let op' =
          match op with
          | Add -> Term.Float.add Term.Float.roundNearestTiesToEven
          | Sub -> Term.Float.sub Term.Float.roundNearestTiesToEven
          | Mul -> Term.Float.mul Term.Float.roundNearestTiesToEven
          | Div -> Term.Float.div Term.Float.roundNearestTiesToEven
          | Min -> Term.Float.min
          | Max -> Term.Float.max
          | Rem -> Term.Float.rem
        in
        op' e1 e2

      let encode_relop op e1 e2 =
        let op' =
          match op with
          | Eq -> Term.eq
          | Ne -> Term.neq
          | Lt -> Term.Float.lt
          | Le -> Term.Float.leq
          | Gt -> Term.Float.gt
          | Ge -> Term.Float.geq
        in
        op' e1 e2
    end

    module F32 :
      Op_intf.S
        with type v := int32
         and type t := expr
         and type unop := Types.F32.unop
         and type binop := Types.F32.binop
         and type relop := Types.F32.relop
         and type cvtop := Types.F32.cvtop
         and type triop := Types.F32.triop = struct
      open Types.F32

      let encode_val n = Term.Float.ieee_format_to_fp 8 24 (I32.encode_val n)
      let encode_unop = Float.encode_unop
      let encode_binop = Float.encode_binop
      let encode_relop = Float.encode_relop

      let encode_cvtop op e =
        let op' =
          match op with
          | DemoteF64 -> Term.Float.ieee_format_to_fp 8 24
          | ConvertSI32 | ConvertSI64 ->
            Term.Float.sbv_to_fp 8 24 Term.Float.roundNearestTiesToEven
          | ConvertUI32 | ConvertUI64 ->
            Term.Float.ubv_to_fp 8 24 Term.Float.roundNearestTiesToEven
          | ReinterpretInt -> assert false
          | ToString -> fun v -> Term.apply_cst f32_to_string [] [ v ]
          | OfString -> fun v -> Term.apply_cst string_to_f32 [] [ v ]
          | PromoteF32 -> assert false
        in
        op' e

      let encode_triop _op _e1 _e2 _e3 = assert false
    end

    module F64 :
      Op_intf.S
        with type v := int64
         and type t := expr
         and type unop := Types.F64.unop
         and type binop := Types.F64.binop
         and type relop := Types.F64.relop
         and type cvtop := Types.F64.cvtop
         and type triop := Types.F64.triop = struct
      open Types.F64

      let encode_val n = Term.Float.ieee_format_to_fp 11 53 (I64.encode_val n)
      let encode_unop = Float.encode_unop
      let encode_binop = Float.encode_binop
      let encode_relop = Float.encode_relop

      let encode_cvtop op e =
        let op' =
          match op with
          | DemoteF64 -> Term.Float.ieee_format_to_fp 11 51
          | ConvertSI32 | ConvertSI64 ->
            Term.Float.sbv_to_fp 11 51 Term.Float.roundNearestTiesToEven
          | ConvertUI32 | ConvertUI64 ->
            Term.Float.ubv_to_fp 11 51 Term.Float.roundNearestTiesToEven
          | ReinterpretInt -> assert false
          | ToString -> fun v -> Term.apply_cst f64_to_string [] [ v ]
          | OfString -> fun v -> Term.apply_cst string_to_f64 [] [ v ]
          | PromoteF32 -> assert false
        in
        op' e

      let encode_triop _op _e1 _e2 _e3 = assert false
    end

    let num i32 i64 f32 f64 : Num.t -> expr = function
      | I32 x -> i32 x
      | I64 x -> i64 x
      | F32 x -> f32 x
      | F64 x -> f64 x

    let encode_val : Value.t -> expr = function
      | Int v -> I.encode_val v
      | Real v -> Real.encode_val v
      | Bool v -> Boolean.encode_val v
      | Str _ -> assert false
      | Num v ->
        num I32.encode_val I64.encode_val F32.encode_val F64.encode_val v

    let encode_unop : Types.unop -> expr -> expr =
      Types.op I.encode_unop Real.encode_unop Boolean.encode_unop
        Str.encode_unop I32.encode_unop I64.encode_unop F32.encode_unop
        F64.encode_unop

    let encode_binop : Types.binop -> expr -> expr -> expr =
      Types.op I.encode_binop Real.encode_binop Boolean.encode_binop
        Str.encode_binop I32.encode_binop I64.encode_binop F32.encode_binop
        F64.encode_binop

    let encode_triop : Types.triop -> expr -> expr -> expr -> expr =
      Types.op I.encode_triop Real.encode_triop Boolean.encode_triop
        Str.encode_triop I32.encode_triop I64.encode_triop F32.encode_triop
        F64.encode_triop

    let encode_cvtop : Types.cvtop -> expr -> expr =
      Types.op I.encode_cvtop Real.encode_cvtop Boolean.encode_cvtop
        Str.encode_cvtop I32.encode_cvtop I64.encode_cvtop F32.encode_cvtop
        F64.encode_cvtop

    let encode_relop : Types.relop -> expr -> expr -> expr =
      Types.op I.encode_relop Real.encode_relop Boolean.encode_relop
        Str.encode_relop I32.encode_relop I64.encode_relop F32.encode_relop
        F64.encode_relop

    let symbol_to_var v =
      Expr.Term.Var.mk (Symbol.to_string v) (tty_of_etype (Symbol.type_of v))

    let encode_unviversal_quantifier (vars_list : Symbol.t list) (body : expr)
      (_patterns : expr list) : expr =
      (* TODO: support triggers *)
      let vars = List.map symbol_to_var vars_list in
      Term.all ([], vars) body

    let encore_existential_quantifier (vars_list : Symbol.t list) (body : expr)
      (_patterns : expr list) : expr =
      (* TODO: support triggers *)
      let vars = List.map symbol_to_var vars_list in
      Term.ex ([], vars) body

    let encore_expr_aux ?(record_sym = fun _ -> ()) (e : Expression.t) : expr =
      let open Expression in
      let rec aux e =
        match e with
        | Val v -> encode_val v
        | SymPtr (base, offset) ->
          let base' = encode_val (Num (I32 base)) in
          let offset' = aux offset in
          Term.Bitv.add base' offset'
        | Unop (op, e) ->
          let e' = aux e in
          encode_unop op e'
        | Binop (I32 ExtendS, Val (Num (I32 n)), e) ->
          let e' = aux e in
          Term.Bitv.sign_extend (Int32.to_int n) e'
        | Binop (I32 ExtendU, Val (Num (I32 n)), e) ->
          let e' = aux e in
          Term.Bitv.zero_extend (Int32.to_int n) e'
        | Binop (op, e1, e2) ->
          let e1' = aux e1
          and e2' = aux e2 in
          encode_binop op e1' e2'
        | Triop (op, e1, e2, e3) ->
          let e1' = aux e1
          and e2' = aux e2
          and e3' = aux e3 in
          encode_triop op e1' e2' e3'
        | Relop (op, e1, e2) ->
          let e1' = aux e1
          and e2' = aux e2 in
          encode_relop op e1' e2'
        | Cvtop (op, e) ->
          let e' = aux e in
          encode_cvtop op e'
        | Symbol s ->
          let cst = tcst_of_symbol s in
          record_sym cst;
          Term.of_cst cst
        | Extract (e, h, l) ->
          let e' = aux e in
          Term.Bitv.extract ((h * 8) - 1) (l * 8) e'
        | Concat (e1, e2) ->
          let e1' = aux e1
          and e2' = aux e2 in
          Term.Bitv.concat e1' e2'
        | Quantifier (t, vars, body, patterns) -> (
          let body' = aux body in
          let encode_pattern (p : t list) =
            Term.multi_trigger (List.map aux p)
          in
          let patterns' = List.map encode_pattern patterns in
          match t with
          | Forall -> encode_unviversal_quantifier vars body' patterns'
          | Exists -> encore_existential_quantifier vars body' patterns' )
      in
      aux e

    let () =
      let term_app1 env s f =
        Dolmen_loop.Typer.T.builtin_term
          (Dolmen_type.Base.term_app1
             (module Dolmen_loop.Typer.T)
             env s
             (fun a -> Expr.Term.apply_cst f [ a.Expr.term_ty ] [ a ]) )
      in
      Expr.add_builtins (fun env s ->
        match s with
        | Dolmen_loop.Typer.T.Id { ns = Term; name = Simple "StringToInt" } ->
          term_app1 env s string_to_int
        | Dolmen_loop.Typer.T.Id { ns = Term; name = Simple "RealToString" } ->
          term_app1 env s real_to_string
        | Dolmen_loop.Typer.T.Id { ns = Term; name = Simple "StringToReal" } ->
          term_app1 env s string_to_real
        | Dolmen_loop.Typer.T.Id { ns = Term; name = Simple "TrimString" } ->
          term_app1 env s trim_string
        | Dolmen_loop.Typer.T.Id { ns = Term; name = Simple "F32ToString" } ->
          term_app1 env s f32_to_string
        | Dolmen_loop.Typer.T.Id { ns = Term; name = Simple "StringToF32" } ->
          term_app1 env s string_to_f32
        | Dolmen_loop.Typer.T.Id { ns = Term; name = Simple "F64ToString" } ->
          term_app1 env s f64_to_string
        | Dolmen_loop.Typer.T.Id { ns = Term; name = Simple "StringToF64" } ->
          term_app1 env s string_to_f64
        | _ -> `Not_found )

    let add_default_axioms env =
      (* string_to_alpha (alpha_to_string x) = x
         alpha_to_string (string_to_alpha x) = x *)
      let add_string_axiom =
        let convert ~subst env =
          Colibri2_theories_quantifiers.Subst.convert ~subst_new:subst env
        in
        let mk_eq env subst t1 t2 =
          let n1 = convert ~subst env t1 in
          let n2 = convert ~subst env t2 in
          Egraph.register env n1;
          Egraph.register env n2;
          let eq = Colibri2_theories_bool.Equality.equality env [ n1; n2 ] in
          Egraph.register env eq;
          Colibri2_theories_bool.Boolean.set_true env eq
        in
        fun env to_string of_string ty ->
          let x_str = Term.Var.mk "x_str" string_ty in
          let xt_str = Term.of_var x_str in
          let term_str =
            Term.apply_cst to_string []
              [ Term.apply_cst of_string [] [ xt_str ] ]
          in
          let x = Term.Var.mk "x" ty in
          let xt = Term.of_var x in
          let term =
            Term.apply_cst of_string [] [ Term.apply_cst to_string [] [ xt ] ]
          in
          let pattern_1 =
            Colibri2_theories_quantifiers.Pattern.of_term_exn term_str
          in
          let pattern_2 =
            Colibri2_theories_quantifiers.Pattern.of_term_exn term
          in
          let run_1 env subst = mk_eq env subst xt_str term_str in
          let run_2 env subst = mk_eq env subst xt term in
          Colibri2_theories_quantifiers.InvertedPath.add_callback env pattern_1
            run_1;
          Colibri2_theories_quantifiers.InvertedPath.add_callback env pattern_2
            run_2
      in
      add_string_axiom env int_to_string string_to_int Ty.int;
      add_string_axiom env real_to_string string_to_real Ty.real;
      add_string_axiom env f32_to_string string_to_f32 float32_ty;
      add_string_axiom env f64_to_string string_to_f64 float64_ty

    let encode_expr e = encore_expr_aux e
    let expr_to_smtstring _ _ = ""

    let mk_scheduler () : Scheduler.t =
      let scheduler = Scheduler.new_solver ~learning:false () in
      Scheduler.init_theories
        ~theories:
          ( LRA.LRA.th_register :: Colibri2_theories_fp.Fp.th_register
          :: Colibri2_core.ForSchedulers.default_theories () )
        scheduler;
      scheduler

    let mk_solver () : solver =
      let scheduler = mk_scheduler () in
      let ctx = Scheduler.get_context scheduler in
      { scheduler
      ; pushpop = []
      ; state = `Search
      ; status_colibri = Context.Ref.create ctx `No
      ; decls = Term.Const.S.empty
      }

    let interrupt () = ()

    let translate ({ pushpop; state; status_colibri; decls; _ } : solver) :
      solver =
      let scheduler = mk_scheduler () in
      { scheduler; pushpop; state; status_colibri; decls }

    let push (st : solver) : unit =
      st.pushpop <- Scheduler.push st.scheduler :: st.pushpop

    let rec pop (st : solver) (i : int) : unit =
      assert (0 <= i);
      match (i, st.pushpop) with
      | 0, _ -> ()
      | _, [] -> assert false
      | 1, bp :: l ->
        st.pushpop <- l;
        Scheduler.pop_to st.scheduler bp
      | n, _ :: l ->
        st.pushpop <- l;
        pop st (n - 1)

    let reset (s : solver) : unit =
      let scheduler = mk_scheduler () in
      let ctx = Scheduler.get_context scheduler in
      s.scheduler <- scheduler;
      s.pushpop <- [];
      s.state <- `Search;
      s.status_colibri <- Context.Ref.create ctx `No;
      s.decls <- Term.Const.S.empty

    let add_solver (s : solver) (es : Expression.t list) : unit =
      Scheduler.add_assertion s.scheduler (fun d ->
        let es' =
          List.map
            (encore_expr_aux ~record_sym:(fun c ->
               s.decls <- Term.Const.S.add c s.decls ) )
            es
        in
        List.iter
          (fun e ->
            let n = Colibri2_core.Ground.convert d e in
            Colibri2_core.Egraph.register d n;
            Colibri2_theories_bool.Boolean.set_true d n )
          es' )

    let check (s : solver) (es : Expression.t list) : status =
      add_solver s es;
      Scheduler.check_sat s.scheduler

    let get_model (s : solver) : model option =
      match Scheduler.check_sat s.scheduler with
      | `Sat d | `Unknown d ->
        let l =
          Term.Const.S.fold_left
            (fun acc c ->
              let e = Expr.Term.of_cst c in
              let v = Interp.interp d e in
              (c, v) :: acc )
            [] s.decls
        in
        Some (d, l)
      | `Unsat -> assert false
      | `StepLimitReached -> assert false
      | `Search -> assert false

    let mk_opt () : optimize = Sim.Core.empty ~is_int:false ~check_invs:false
    let add_opt (_o : optimize) (_es : Expression.t list) : unit = assert false
    let maximize (_o : optimize) (_e : Expression.t) : handle = assert false
    (* Sim.Solve.maximize o (Sim.Core.P.from_list [ (encore_expr_aux e, A.one) ]) *)

    let minimize (_o : optimize) (_e : Expression.t) : handle = assert false

    let get_opt_model (o : optimize) : model Option.t =
      match Sim.Result.get None o with
      | Sim.Core.Sat s ->
        let _model = (Lazy.force s).Sim.Core.main_vars in
        (* let l = List.map (fun (n, av) -> (n, LRA.RealValue.of_value av)) model in
           Some l *)
        None
      | Sim.Core.Unknown | Sim.Core.Unsat _ | Sim.Core.Unbounded _
      | Sim.Core.Max (_, _) ->
        None

    let c2value_to_value (ty : Types.expr_type) (v : Colibri2_core.Value.t) =
      match ty with
      | `BoolType -> (
        match
          Colibri2_core.Value.value Colibri2_theories_bool.Boolean.BoolValue.key
            v
        with
        | Some b -> Some (Value.Bool b)
        | None -> None )
      | `IntType | `RealType -> (
        match
          Colibri2_core.Value.value Colibri2_theories_LRA.RealValue.key v
        with
        | Some a when A.is_integer a -> Some (Value.Int (A.to_int a))
        | Some a when A.is_real a ->
          Some (Value.Real (Stdlib.Float.of_string (A.to_string a)))
        | Some _ | None -> None )
      | `I32Type | `I64Type -> assert false
      | `F32Type | `F64Type -> assert false
      | `StrType -> assert false

    let value_of_const ((d, _l) : model) (e : Expression.t) : Value.t option =
      let e' = encore_expr_aux e in
      let v = Colibri2_core.Interp.interp d e' in
      c2value_to_value (Expression.type_of e) v

    let value_binds ?(symbols : Symbol.t list option) ((_, model) : model) :
      Model.t =
      let m = Base.Hashtbl.create (module Symbol) in
      match symbols with
      | Some symbols ->
        List.iter
          (fun sy ->
            let c = tcst_of_symbol sy in
            match List.assoc_opt c model with
            | Some v -> (
              match c2value_to_value (tty_to_etype c.Expr.id_ty) v with
              | Some data -> Base.Hashtbl.set m ~key:(tcst_to_symbol c) ~data
              | None -> () )
            | _ -> () )
          symbols;
        m
      | None ->
        List.iter
          (fun (c, v) ->
            match c2value_to_value (tty_to_etype c.Expr.id_ty) v with
            | Some data -> Base.Hashtbl.set m ~key:(tcst_to_symbol c) ~data
            | None -> () )
          model;
        m

    let satisfiability =
      let open Mappings_intf in
      function
      | `Sat _ -> Satisfiable
      | `Unknown _ -> Unknown
      | `Unsat -> Unsatisfiable
      | `Search -> assert false
      | `StepLimitReached -> assert false

    let set_default_axioms s =
      Scheduler.add_assertion s.scheduler add_default_axioms

    let set_debug = Colibri2_stdlib.Debug.set_info_flags
  end
end

include Fresh.Make ()
