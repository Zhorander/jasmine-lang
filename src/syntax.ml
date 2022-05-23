(** Module Syntax
 * Implementations for an abstract syntax tree, and a well-typed syntax tree.
 *)

(* Currently, type checking returns is not implemented *)

open Core

(* Moule Untyped Represents the Abstract Syntax Tree *)
module Untyped = struct
  (* Abstract Expression *)
  type expression =
    | Int of int
    | Bool of bool
    | Unit of unit
    | Ident of string
    | Group of expression
    | Plus of expression * expression
    | Sub of expression * expression
    | Mult of expression * expression
    | Div of expression * expression
    | Equal of expression * expression
    | Not_equal of expression * expression
    | Not of expression
    | Funcall of string * (expression list)
    [@@deriving sexp]

  (* Abstract Statement *)
  type stmt =
    | Exp of expression
    | Vardec of string * Types.uty * expression
    | Compound of stmt list
    | Fun_def of {
      name: string;
      params: (string * Types.uty) list;
      ret_t: Types.uty option;
      body: stmt
      }
    | While of expression * stmt
    | If of expression * stmt * (stmt option)
    | Mutate of string * expression
    | Return of expression option
    [@@deriving sexp]
end

(* Module Well_typed Represents a Well-Typed Syntax Tree *)
module Well_typed = struct
  (* Future, include an int_value type for different int sizes
   * Then turn Plus,Sub,... into
   * 'a int_value expr * 'a int_value expr -> 'a int_value expr
   *)
  type _ value =
    | Int_val : int -> int value
    | Bool_val : bool -> bool value
    | Unit_val : unit -> unit value
  and
  _ expr =
    | Value : 'a value -> 'a expr
    | Ident : string -> 'a expr
    | Group : 'a expr -> 'a expr
    | Plus : int expr * int expr -> int expr
    | Sub : int expr * int expr -> int expr
    | Mult : int expr * int expr -> int expr
    | Div : int expr * int expr -> int expr
    | Equal : 'a expr * 'a expr -> bool expr
    | Not_equal : 'a expr * 'a expr -> bool expr
    | Not : bool expr -> bool expr
    | Funcall : string * (param list) -> 'a expr
  and
  (* type param
   **)
  param =
    Parameter : 'a expr -> param
  and
  (* type some_texpr
   * type to represent an existential well typed expression
   **)
  some_texpr = Expr : 'a expr * 'a Types.ty -> some_texpr

  (* type stmt
   * type to represent a well typed statement
   **)
  type stmt =
    | Exp : 'a expr -> stmt
    | Vardec : string * 'a Types.ty * 'a expr -> stmt
    | Compound : stmt list -> stmt
      (* fun name(param list): type body return *)
    | Fun_def :
      { name: string;
        params: (string * Types.some_ty) list;
        ret_t: 'a Types.ty;
        body: stmt
      } -> stmt
    | While : (bool expr) * stmt -> stmt
    | If : (bool expr) * stmt * (stmt option) -> stmt
    | Mutate : string * 'a expr -> stmt
    | Return : 'a expr -> stmt
end

(** uexpr_to_texpr : Structs.Symtable.t -> Untyped.expression -> Well_typed.some_expr
 * convert an untyped expression to a well typed expression
 *)
let rec uexpr_to_texpr: Structs.Scope.t -> Untyped.expression -> Well_typed.some_texpr =
  fun scope expr ->
  let open Well_typed in
  match expr with
  (* Value Expressions *)
  | Untyped.Bool b -> Expr (Value (Bool_val b), Bool)
  | Untyped.Int i -> Expr (Value (Int_val i), Int)
  | Untyped.Unit u -> Expr (Value (Unit_val u), Unit)
  (* Identifiers ask the symbol table for their type *)
  | Untyped.Ident s ->
    let id_ty =
      Structs.Scope.find ~scope s
      |> Types.check_ty
    in
    let (Types.Ty ident_ty) = id_ty in
    Expr (Ident s, ident_ty)
  (* Group Expression *)
  | Untyped.Group e ->
    let (Expr (e_texpr, e_ty)) = uexpr_to_texpr scope e in
    Expr (Group e_texpr, e_ty)
  (* Binary Expressions
   * - extract the type of each type
   * - compare the types of both sides
   *)
  (* Addition *)
  | Untyped.Plus (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uexpr_to_texpr scope lhe in
    let (Expr (rtexpr, rty)) = uexpr_to_texpr scope rhe in
    (* type check *)
    let Types.Refl = Types.eq_types lty Types.Int in
    let Types.Refl = Types.eq_types lty rty in
    Expr (Plus (ltexpr, rtexpr), Types.Int)
  (* Subtraction *)
  | Untyped.Sub (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uexpr_to_texpr scope lhe in
    let (Expr (rtexpr, rty)) = uexpr_to_texpr scope rhe in
    (* type check *)
    let Types.Refl = Types.eq_types lty Types.Int in
    let Types.Refl = Types.eq_types lty rty in
    Expr (Sub (ltexpr, rtexpr), Types.Int)
  (* Multiplication *)
  | Untyped.Mult (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uexpr_to_texpr scope lhe in
    let (Expr (rtexpr, rty)) = uexpr_to_texpr scope rhe in
    (* type check *)
    let Types.Refl = Types.eq_types lty Types.Int in
    let Types.Refl = Types.eq_types lty rty in
    Expr (Mult (ltexpr, rtexpr), Types.Int)
  (* Division *)
  | Untyped.Div (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uexpr_to_texpr scope lhe in
    let (Expr (rtexpr, rty)) = uexpr_to_texpr scope rhe in
    (* type check *)
    let Types.Refl = Types.eq_types lty Types.Int in
    let Types.Refl = Types.eq_types lty rty in
    Expr (Div (ltexpr, rtexpr), Types.Int)
  (* Equality *)
  | Untyped.Equal (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uexpr_to_texpr scope lhe in
    let (Expr (rtexpr, rty)) = uexpr_to_texpr scope rhe in
    (* type check - only that the args are type equivalent *)
    let Types.Refl = Types.eq_types lty rty in
    Expr (Equal (ltexpr, rtexpr), Types.Bool)
  (* Not Equals *)
  | Untyped.Not_equal (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uexpr_to_texpr scope lhe in
    let (Expr (rtexpr, rty)) = uexpr_to_texpr scope rhe in
    (* type check *)
    let Types.Refl = Types.eq_types lty rty in
    Expr (Not_equal (ltexpr, rtexpr), Types.Bool)
  (* Not *)
  | Untyped.Not e ->
    let (Expr (e_texpr, e_ty)) = uexpr_to_texpr scope e in
    let Types.Refl = Types.eq_types e_ty Types.Bool in
    Expr (Not e_texpr, e_ty)
  (* Function call *)
  | Untyped.Funcall (name, e_list) ->
    (* get type of function *)
    let id_ty =
      Structs.Scope.find ~scope name
      |> Types.check_ty
    in
    (* ident_ty is concrete type of the function *)
    let (Types.Ty ident_ty) = id_ty in
    (* Turn the uty list into a well-typed list *)
    let texpr_list: some_texpr list =
      List.map ~f:(uexpr_to_texpr scope) e_list
    in
    let texpr_ty_list: Types.some_ty list =
      List.map ~f:(fun (Expr (_, param_ty)) -> Types.Ty param_ty) texpr_list
    in
    let ret_t: Types.some_ty = match id_ty with
      | Ty (Types.Fun (_, fun_ret)) -> Types.Ty fun_ret
      | Ty (_) -> raise (Exceptions.TypeError (name ^ " is not a function."))
    in
    let (Types.Ty ret_t) = ret_t in
    let Types.Refl = Types.eq_types ident_ty (Types.Fun (texpr_ty_list, ret_t)) in
    (* Construct the well-typed function call expression *)
    let param_list: param list =
      List.map ~f:(fun (Expr (tparam,_)) -> Parameter tparam) texpr_list
    in
    Expr (Funcall (name, param_list), ret_t)
  (* | _ -> raise Exceptions.Not_implemented *)

(** ustmt_to_tstmt: Structs.Scope.t -> Untyped.stmt -> Well_typed.stmt
 * Convert an abstract statement into a well-typed statement
 * Generally the first call is where the global scope is passed.
 *)
let rec ustmt_to_tstmt (scope: Structs.Scope.t) ustmt =
  let open Well_typed in
  match ustmt with
  | Untyped.Exp expr ->
    let (Expr (texpr, _)) = uexpr_to_texpr scope expr in
    Exp texpr
  | Untyped.Vardec (name, uty, expr) ->
    let (Ty ty) = Types.check_ty uty in
    let (Expr (texpr, expr_ty)) = uexpr_to_texpr scope expr in
    let Refl = Types.eq_types ty expr_ty in
    (* Add new variable to the scope *)
    Structs.Scope.add_symbol ~scope name uty; 
    Vardec (name, ty, texpr)
  | Untyped.Compound stmts ->
    let child_scope = Structs.Scope.create ~par:(Some scope) () in
    let tstmt_list = List.map ~f:(ustmt_to_tstmt child_scope) stmts in
    Compound tstmt_list
  | Untyped.Fun_def {
      name: string;
      params: (string * Types.uty) list;
      ret_t: Types.uty option;
      body: Untyped.stmt
    } ->
    (* Add the function to the symbol table *)
    let ret_t = match ret_t with
      | Some ret_concrete -> ret_concrete
      | None -> Types.T_unit
    in
    let param_utypes = List.map ~f:(fun (_, puty) -> puty) params in
    let fun_uty = Types.T_fun (param_utypes, ret_t) in
    Structs.Scope.add_symbol ~scope name fun_uty;
    (* Map the parameters to well-typed parameters *)
    let tparams: (string *Types.some_ty) list = List.map
      ~f:(fun (name,name_uty) -> (name, Types.check_ty name_uty))
      params
    in
    (* Create a well-typed body *) 
    let child_scope = Structs.Scope.create ~par:(Some scope) () in
    List.iter
      ~f:(fun (sym,symt) -> Structs.Scope.add_symbol ~scope:child_scope sym symt)
      params;
    let tbody: stmt = ustmt_to_tstmt child_scope body in
    (* Create the well-typed function definition *)
    let (Types.Ty ret_ty) = Types.check_ty ret_t in
    Fun_def {
      name; params=tparams; ret_t=ret_ty; body=tbody
    }
  | Untyped.While (expr, body) ->
    let (Expr (typed_expr, expr_ty)) = uexpr_to_texpr scope expr in
    let Types.Refl = Types.eq_types expr_ty Types.Bool in
    let child_scope = Structs.Scope.create ~par:(Some scope) () in
    let tstmt = ustmt_to_tstmt child_scope body in
    While (typed_expr, tstmt)
  | Untyped.If (expr, then_stmt, else_stmt) ->
    let (Expr (typed_expr, expr_ty)) = uexpr_to_texpr scope expr in
    let Types.Refl = Types.eq_types expr_ty Types.Bool in
    let child_scope = Structs.Scope.create ~par:(Some scope) () in
    let typed_then_stmt = ustmt_to_tstmt child_scope then_stmt in
    let typed_else_stmt = match else_stmt with
      | None -> None
      | Some stmt ->
        let child_scope = Structs.Scope.create ~par:(Some scope) () in
        Some (ustmt_to_tstmt child_scope stmt)
    in
    If (typed_expr, typed_then_stmt, typed_else_stmt)
  | Untyped.Mutate (loc_expr, expr) ->
    let (Types.Ty id_ty) =
      Structs.Scope.find ~scope loc_expr
      |> Types.check_ty
    in
    let (Expr (typed_expr, expr_ty)) = uexpr_to_texpr scope expr in
    let Types.Refl = Types.eq_types expr_ty id_ty in
    Mutate (loc_expr, typed_expr)
  | Untyped.Return expr ->
    begin match expr with
      | None -> Return (Value (Unit_val ()))
      | Some uexpr ->
        let (Expr (texpr, _)) = uexpr_to_texpr scope uexpr in
        Return texpr
    end