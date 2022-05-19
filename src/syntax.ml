(** Module Syntax
 * Implementations for an abstract syntax tree, and a well-typed syntax tree.
 *)

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
    | Mutate of expression * expression
    | Return of expression
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
        params: param list;
        ret_t: 'a Types.ty; body: stmt
      } -> stmt
    | While : (bool expr) * stmt -> stmt
    | If : (bool expr) * stmt * (stmt option) -> stmt
    | Mutate : 'a expr * 'a expr -> stmt
    | Return : 'a expr -> stmt
end

(** uty_to_texp : Structs.Symtable.t -> Untyped.expression -> Well_typed.some_expr
 * convert an untyped expression to a well typed expression
 *)
let rec uty_to_texp: Structs.Symtable.t -> Untyped.expression -> Well_typed.some_texpr =
  fun symtbl expr ->
  let open Well_typed in
  match expr with
  (* Value Expressions *)
  | Untyped.Bool b -> Expr (Value (Bool_val b), Bool)
  | Untyped.Int i -> Expr (Value (Int_val i), Int)
  | Untyped.Unit u -> Expr (Value (Unit_val u), Unit)
  (* Identifiers ask the symbol table for their type *)
  | Untyped.Ident s ->
    let id_ty =
      Structs.Symtable.find ~symtbl:symtbl s
      |> (function Some x -> x | None -> raise (Exceptions.Undeclared_Variable "s"))
      |> Types.check_ty
    in
    let (Types.Ty ident_ty) = id_ty in
    Expr (Ident s, ident_ty)
  (* Group Expression *)
  | Untyped.Group e ->
    let (Expr (e_texpr, e_ty)) = uty_to_texp symtbl e in
    Expr (Group e_texpr, e_ty)
  (* Binary Expressions
   * - extract the type of each type
   * - compare the types of both sides
   *)
  (* Addition *)
  | Untyped.Plus (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uty_to_texp symtbl lhe in
    let (Expr (rtexpr, rty)) = uty_to_texp symtbl rhe in
    (* type check *)
    let Types.Refl = Types.eq_types lty Types.Int in
    let Types.Refl = Types.eq_types lty rty in
    Expr (Plus (ltexpr, rtexpr), Types.Int)
  (* Subtraction *)
  | Untyped.Sub (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uty_to_texp symtbl lhe in
    let (Expr (rtexpr, rty)) = uty_to_texp symtbl rhe in
    (* type check *)
    let Types.Refl = Types.eq_types lty Types.Int in
    let Types.Refl = Types.eq_types lty rty in
    Expr (Sub (ltexpr, rtexpr), Types.Int)
  (* Multiplication *)
  | Untyped.Mult (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uty_to_texp symtbl lhe in
    let (Expr (rtexpr, rty)) = uty_to_texp symtbl rhe in
    (* type check *)
    let Types.Refl = Types.eq_types lty Types.Int in
    let Types.Refl = Types.eq_types lty rty in
    Expr (Mult (ltexpr, rtexpr), Types.Int)
  (* Division *)
  | Untyped.Div (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uty_to_texp symtbl lhe in
    let (Expr (rtexpr, rty)) = uty_to_texp symtbl rhe in
    (* type check *)
    let Types.Refl = Types.eq_types lty Types.Int in
    let Types.Refl = Types.eq_types lty rty in
    Expr (Div (ltexpr, rtexpr), Types.Int)
  (* Equality *)
  | Untyped.Equal (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uty_to_texp symtbl lhe in
    let (Expr (rtexpr, rty)) = uty_to_texp symtbl rhe in
    (* type check - only that the args are type equivalent *)
    let Types.Refl = Types.eq_types lty rty in
    Expr (Equal (ltexpr, rtexpr), Types.Bool)
  (* Not Equals *)
  | Untyped.Not_equal (lhe, rhe) ->
    let (Expr (ltexpr, lty)) = uty_to_texp symtbl lhe in
    let (Expr (rtexpr, rty)) = uty_to_texp symtbl rhe in
    (* type check *)
    let Types.Refl = Types.eq_types lty rty in
    Expr (Not_equal (ltexpr, rtexpr), Types.Bool)
  (* Not *)
  | Untyped.Not e ->
    let (Expr (e_texpr, e_ty)) = uty_to_texp symtbl e in
    let Types.Refl = Types.eq_types e_ty Types.Bool in
    Expr (Not e_texpr, e_ty)
  (* Function call *)
  | Untyped.Funcall (name, e_list) ->
    (* get type of function *)
    let id_ty =
      Structs.Symtable.find ~symtbl:symtbl name
      |> (function Some x -> x | None -> raise (Exceptions.Undeclared_Variable name))
      |> Types.check_ty
    in
    (* ident_ty is concrete type of the function *)
    let (Types.Ty ident_ty) = id_ty in
    (* Turn the uty list into a well-typed list *)
    let texpr_list: some_texpr list =
      List.map ~f:(uty_to_texp symtbl) e_list
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
(* 
let rec ustmt_to_tystmt ustmt =
  match ustmt with
  | *)