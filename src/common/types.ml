(* Representations of Jasmine types *)

open Core


(* Prove that two types are equal *)
type (_,_) eq = Refl : ('a, 'a) eq


(* Type representations of abstract types *)
module Untyped = struct
  type t =
  | Unit
  | Int
  | Bool
  | Fun of (t list) * t
  [@@deriving sexp]

  let rec to_string = function
  | Unit -> "unit"
  | Int -> "int"
  | Bool -> "bool"
  | Fun (utyl, ret_uty) ->
    let sparams = List.fold
      ~init:""
      ~f:(fun acc p -> Printf.sprintf "%s %s," acc (to_string p))
      utyl
    in
    let sret = to_string ret_uty in
    Printf.sprintf "Function %s -> %s" sparams sret 
end

(* Type representations of well-typed types *)
module Well_typed = struct
  type 'a t =
    | Unit : unit t
    | Int : int t
    | Bool : bool t
    | Poly : 'a t
    | Fun : (some_ty list) * 'a t -> 'a t
  (* Existential type of a well-typed type *)
  and some_ty =
    Ty : 'a t -> some_ty


  let rec to_string: type a. a t -> string = function
  | Unit -> "unit"
  | Int -> "int"
  | Bool -> "bool"
  | Poly -> "poly"
  | Fun (tyl, ret_ty) ->
    let sparams = List.fold
      ~init:""
      ~f:(fun acc p ->
        let (Ty pt) = p in
        Printf.sprintf "%s %s," acc (to_string pt))
      tyl
    in
    let sret = to_string ret_ty in
    Printf.sprintf "Function %s -> %s" sparams sret


let eq_poly_types: 'a t -> 'b t -> ('a,'b) eq =
  fun ta tb ->
  match  (ta,tb) with
  | _ -> Refl

  (* eq_types : type a b. a ty -> b ty -> (a,b) eq
  * Show that two types are equal, or raise exception
  **)
  let rec eq_types: type a b. a t -> b t -> (a,b) eq =
    fun ta tb -> match (ta,tb) with
    | (Unit, Unit) -> Refl
    | (Int, Int) -> Refl
    | (Bool, Bool) -> Refl
    | (Fun (ti1, tr1),Fun (ti2, tr2)) ->
      let rec eq_params params1 params2 =
        match params1, params2 with
        | (Ty hd1) :: tl1, (Ty hd2) :: tl2 ->
          let Refl = eq_types hd1 hd2 in
          eq_params tl1 tl2
        | [], [] -> ()
        | _ ->
          let str_ty_1 = to_string ta in
          let str_ty_2 = to_string tb in
          let msg =
            Printf.sprintf "'%s' incompatable with '%s'\n" str_ty_1 str_ty_2
          in
          raise (Exceptions.TypeError msg)
      in
      let () = eq_params ti1 ti2 in
      let Refl = eq_types tr1 tr2 in
      Refl
    | _, _ ->
      let str_ty_1 = to_string ta in
      let str_ty_2 = to_string tb in
      let msg =
        Printf.sprintf "'%s' incompatable with '%s'\n" str_ty_1 str_ty_2
      in
      raise (Exceptions.TypeError msg)


  (* check_ty : uty -> some_ty
  * Convert an abstract type into a concrete existential type
  * Note: Function types become function chains (fun a,b,c -> d becomes fun a -> fun b -> fun c -> d)
  **)
  let rec check_ty : Untyped.t -> some_ty = fun uty ->
  match uty with
  | Untyped.Unit-> Ty Unit
  | Untyped.Int -> Ty Int
  | Untyped.Bool -> Ty Bool
  | Untyped.Fun (tl,rt) ->
    let checked_ret = check_ty rt in
    let params: some_ty list =
      List.rev tl
      |> List.map ~f:check_ty
    in
    let (Ty some_ret) = checked_ret in
    Ty (Fun (params, some_ret))
end
