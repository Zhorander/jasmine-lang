(* Three Address Form Optimizations *)


module Symtable = Common.Structs.Make_symbol_table(struct
  type t = Three_addr.expression
  let to_string = Three_addr.string_of_expression   
end)

module Scope = Common.Structs.Scope(Symtable)

module Taddr = Three_addr

open Core


(* The simplest optimization for this form is constant-propogation
  since temporary variables are created throughout the process
 *)

(* Check whether a value is a temporary variable *)
let is_tmp_string s = String.contains ~pos:0 ~len:1 s '@'

let is_tmp_val e =
  match e with
  | Taddr.Value v ->
    begin match v with
    | Taddr.Identifier i -> is_tmp_string i
    | _ -> false
    end
  | _ -> false

let expression_is_value = function
  | Taddr.Value _ -> true
  | _ -> false

let replace_tmp_val scope value =
  match value with
  | Taddr.Identifier i ->
    if is_tmp_string i then
      let expr = Scope.find ~scope i in
      begin match expr with Value v -> v | _ -> value end
    else
      value
  | _ -> value

let get_tmp_string_from_val v =
  match v with
  | Taddr.Identifier i -> i
  | _ ->
    let expr_str = Taddr.string_of_value v in
    raise (Common.Exceptions.Compiler_error (expr_str ^ " is not a temp variable"))

let constant_propogation_expr scope expr =
  let propogate_binary lh rh bin =
    let lh_val = replace_tmp_val scope lh in
    let rh_val = replace_tmp_val scope rh in
    bin lh_val rh_val
  in
  let propogate_unary v un =
    replace_tmp_val scope v |> un
  in
  match expr with
  | Taddr.Value v ->
    if is_tmp_val expr then
      let tmp_id = get_tmp_string_from_val v in
      Scope.find ~scope tmp_id
    else
      expr
  | Taddr.Add (lh,rh) -> propogate_binary lh rh (fun a b -> Taddr.Add (a,b))
  | Taddr.Sub (lh,rh) -> propogate_binary lh rh (fun a b -> Taddr.Sub (a,b))
  | Taddr.Mult (lh,rh) -> propogate_binary lh rh (fun a b -> Taddr.Mult (a,b))
  | Taddr.Div (lh,rh) -> propogate_binary lh rh (fun a b -> Taddr.Div (a,b))
  | Taddr.Equal (lh,rh) -> propogate_binary lh rh (fun a b -> Taddr.Equal (a,b))
  | Taddr.Not_equal (lh,rh) -> propogate_binary lh rh (fun a b -> Taddr.Not_equal (a,b))
  | Taddr.Not e -> propogate_unary e (fun a -> Taddr.Not a)
  | _ -> expr

let constant_propogation_stmt (scope,acc) stmt =
  match stmt with
  | Taddr.Assign (name,expr) ->
    let prop_expr = constant_propogation_expr scope expr in
    (* If the location is a temporary variable, then add the expression to the symbol table *)
    if is_tmp_string name then Scope.add_symbol ~scope name prop_expr;

    let new_stmt = Taddr.Assign (name, prop_expr) in
    scope, new_stmt :: acc
  | Taddr.If (expr,label) ->
    let prop_expr = constant_propogation_expr scope expr in
    let new_stmt = Taddr.If (prop_expr, label) in
    scope, new_stmt :: acc
  | Taddr.Return expr ->
    let prop_expr = constant_propogation_expr scope expr in
    let new_stmt = Taddr.Return prop_expr in
    scope, new_stmt :: acc
  | Taddr.Call_param v ->
    let new_val = replace_tmp_val scope v in
    let new_stmt = Taddr.Call_param new_val in
    scope, new_stmt :: acc
  | _ -> scope, (stmt :: acc)


(* Remove un-used temporary variables *)
let collect_temps_from_expr expr =
  let tmps_from_binary lh rh =
    let lh_tmp = if is_tmp_val (Value lh) then [get_tmp_string_from_val lh] else [] in
    let rh_tmp = if is_tmp_val (Value rh) then [get_tmp_string_from_val rh] else [] in
    lh_tmp @ rh_tmp
  in
  match expr with
  | Taddr.Value v ->
    if is_tmp_val expr then
      let tmp_id = get_tmp_string_from_val v in
      [tmp_id]
    else
      []
  | Taddr.Add (lh,rh)
  | Taddr.Sub (lh,rh)
  | Taddr.Mult (lh,rh)
  | Taddr.Div (lh,rh)
  | Taddr.Equal (lh,rh)
  | Taddr.Not_equal (lh,rh) ->
    tmps_from_binary lh rh
  | Taddr.Not v -> if is_tmp_val (Value v) then [get_tmp_string_from_val v] else []
  | _ -> []

let elide_temps (used,acc) stmt =
  match stmt with
  | Taddr.Assign (name,expr) ->
    if (is_tmp_string name) && not (List.exists used ~f:(String.equal name)) then
      used, acc
    else
      let used_tmps = collect_temps_from_expr expr in
      (used_tmps @ used), stmt :: acc
  | Taddr.If (expr,_) ->
    let used_tmps = collect_temps_from_expr expr in
    (used_tmps @ used), stmt :: acc
  | Taddr.Return expr ->
    let used_tmps = collect_temps_from_expr expr in
    (used_tmps @ used), stmt :: acc
  | Taddr.Call_param v ->
    let used_tmps = collect_temps_from_expr (Value v) in
    (used_tmps @ used), stmt :: acc
  | _ -> used, (stmt :: acc)


let constant_propogation stmts =
  let scope = Scope.create () in
  List.fold ~init:(scope,[]) ~f:constant_propogation_stmt stmts
  |> fun (_,prop_stmts) -> prop_stmts
  |> List.fold ~init:([],[]) ~f:elide_temps
  |> fun (_, elided_stmts) -> elided_stmts