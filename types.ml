open Core

(* Type representations of abstract types *)
type uty =
  | T_unit
  | T_int
  | T_bool
  | T_fun of (uty list) * uty
  [@@deriving sexp]

(* Type representations of well-typed types *)
type 'a ty =
  | Unit : unit ty
  | Int : int ty
  | Bool : bool ty
  | Fun : 'a ty * 'b ty -> ('a -> 'b) ty
(* Existential type of a well-typed type *)
and some_ty =
  Ty : 'a ty -> some_ty

(* Prove that two types are equal *)
type (_,_) eq = Refl : ('a, 'a) eq

(* eq_types : type a b. a ty -> b ty -> (a,b) eq
 * Show that two types are equal, or raise exception
 **)
let rec eq_types: type a b. a ty -> b ty -> (a,b) eq =
  fun ta tb -> match (ta,tb) with
  | (Unit, Unit) -> Refl
  | (Int, Int) -> Refl
  | (Bool, Bool) -> Refl
  | (Fun (ti1, tr1),Fun (ti2, tr2)) ->
    let Refl = eq_types ti1 ti2 in
    let Refl = eq_types tr1 tr2 in
    Refl
  | _, _ -> raise (Exceptions.Incompatible_Types "")

(* check_ty : uty -> some_ty
 * Convert an abstract type into a concrete existential type
 * Note: Function types become function chains (fun a,b,c -> d becomes fun a -> fun b -> fun c -> d)
 **)
let rec check_ty : uty -> some_ty = fun uty ->
  match uty with
  | T_unit -> Ty Unit
  | T_int -> Ty Int
  | T_bool -> Ty Bool
  | T_fun (tl,rt) ->
    let checked_ret = check_ty rt in
    let fun_chain =
      List.rev tl
      |> List.map ~f:check_ty
      |> List.fold
        ~init:checked_ret
        ~f:(fun (Ty out_t) (Ty inp_t) -> Ty (Fun (inp_t, out_t)))
    in
    fun_chain
