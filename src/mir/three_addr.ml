(* Three Address IR *)

open Core

module Wt = Syntax.Well_typed

type value =
  | Int of int
  | Bool of bool
  | Unit of unit
  | Identifier of string

let string_of_value = function
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | Unit () -> "()"
  | Identifier id -> Printf.sprintf "Ident<%s>" id

type expression =
  | Value of value
  | Add of value * value
  | Sub of value * value
  | Mult of value * value
  | Div of value * value
  | Equal of value * value
  | Not_equal of value * value
  | Not of value
  (* | Less_than of value * value
  | Greather_than of value * value
  | Less_or_equal of value * value
  | Greater_or_equal of value * value *)
  | Funcall of string

let string_of_expression = function
  | Value v -> string_of_value v
  | Add (lh,rh) -> Printf.sprintf "%s + %s" (string_of_value lh) (string_of_value rh)
  | Sub (lh,rh) -> Printf.sprintf "%s - %s" (string_of_value lh) (string_of_value rh)
  | Mult (lh, rh) -> Printf.sprintf "%s * %s" (string_of_value lh) (string_of_value rh)
  | Div (lh, rh) -> Printf.sprintf "%s / %s" (string_of_value lh) (string_of_value rh)
  | Equal (lh, rh) -> Printf.sprintf "%s == %s" (string_of_value lh) (string_of_value rh)
  | Not_equal (lh, rh) -> Printf.sprintf "%s != %s" (string_of_value lh) (string_of_value rh)
  | Not v -> Printf.sprintf "!%s" (string_of_value v)
  | Funcall name -> "CALL " ^ name

type statement =
  | Assign of string * expression
  | Label of string
  | Goto of string
  | Return of expression
  | If of value * string
  | Start_call of string
  | Call_param of value
  | Function_start of string
  | Function_end of string
  | Function_param of string
  | Function_ret_type of string

let string_of_statement = function
  | Assign (name, expr) ->
    Printf.sprintf "%s := %s" name (string_of_expression expr)
  | Label name -> "LABEL " ^ name
  | Goto name -> "GOTO " ^ name
  | Return expr -> "RETURN " ^ (string_of_expression expr)
  | If (v,name) -> "IF " ^ (string_of_value v) ^ " GOTO " ^ name
  | Start_call name -> "START_CALL " ^ name
  | Call_param v -> "PARAM " ^ (string_of_value v)
  | Function_start name -> "FUNCTION_START " ^ name
  | Function_end name -> "FUNCTION_END " ^ name
  | Function_param name -> "IN " ^ name
  | Function_ret_type name -> "RETURNS_TYPE " ^ name

(* Environment *)
type environment = {
  curr_tmp: int
  ; curr_label: int
}

let new_environment () = {curr_tmp=0; curr_label=0}

let inc_tmp e = e.curr_tmp + 1, {e with curr_tmp=e.curr_tmp+1}

let inc_label e = e.curr_label + 1, {e with curr_label=e.curr_label+1}

(* ----------- *)

(* Convert a well-typed syntax into a three address structure *)
let value_of_wt_val : type a. a Wt.value -> value =
  fun v ->
  match v with
  | Int_val i -> Int i
  | Bool_val b -> Bool b
  | Unit_val u -> Unit u

let make_tmp_name i =
  Printf.sprintf "_%d" i

let make_loop_name i =
  Printf.sprintf "L%d" i

let rec t_of_expression : type a. environment * (statement list) -> a Wt.expr -> environment * (statement list)
  = fun (env,acc) expr ->
  (* Helper function to make a binary statement *)
  let make_binary lhe rhe (make_expr: value -> value -> expression) =
    (* turn the left hand side into three-address structs, take the resulting tmp var *)
    let env,lh_t = t_of_expression (env,acc) lhe in
    let lh_tmp_var = Identifier (make_tmp_name env.curr_tmp) in
    (* same for the right hand side *)
    let env,rh_t = t_of_expression (env,lh_t) rhe in
    let rh_tmp_var = Identifier (make_tmp_name env.curr_tmp) in
    (* we increment the tmp var in the environment to create a new temp variable *)
    let binary_tmp_var,env = inc_tmp env in
    (* our new temp variable is the result of the binary expression between the
       previous temp variables *)
    let new_stmt = Assign (make_tmp_name binary_tmp_var, (make_expr lh_tmp_var rh_tmp_var)) in
    (env,new_stmt :: rh_t)
  in
  (* Helper function to make a unary statement *)
  let make_unary e make_expr =
    let env,t = t_of_expression (env,acc) e in
    let t_tmp_var = Identifier (make_tmp_name env.curr_tmp) in
    let unary_tmp_var, env = inc_tmp env in
    let new_stmt = Assign (make_tmp_name unary_tmp_var, (make_expr t_tmp_var)) in
    (env,new_stmt :: t)
  in
  match expr with
  | Wt.Value v ->
    (* Create a new temp variable and assign it to the value of the syntax *)
    (* tree value *)
    let tmp_var, env = inc_tmp env in
    let tmp = make_tmp_name tmp_var in
    let val_expr = Value (value_of_wt_val v) in
    let new_stmt = Assign (tmp, val_expr) in
    (env, new_stmt :: acc)
  | Wt.Ident i ->
    (* Same as for Value *)
    let tmp_var, env = inc_tmp env in
    let tmp = make_tmp_name tmp_var in
    let val_expr = Value (Identifier i) in
    let new_stmt = Assign (tmp, val_expr) in
    (env, new_stmt :: acc)
  | Wt.Group g ->
    t_of_expression (env,acc) g
  | Wt.Plus (lhe, rhe) -> make_binary lhe rhe (fun lh rh -> Add (lh, rh))
  | Wt.Sub (lhe, rhe) -> make_binary lhe rhe (fun lh rh -> Sub (lh, rh))
  | Wt.Mult (lhe, rhe) -> make_binary lhe rhe (fun lh rh -> Mult (lh, rh))
  | Wt.Div (lhe, rhe) -> make_binary lhe rhe (fun lh rh -> Div (lh, rh))
  | Wt.Equal (lhe, rhe) -> make_binary lhe rhe (fun lh rh -> Equal (lh, rh))
  | Wt.Not_equal (lhe, rhe) -> make_binary lhe rhe (fun lh rh -> Not_equal (lh, rh))
  | Wt.Not exp -> make_unary exp (fun x -> Not x)
  | Wt.Funcall (name,params) ->
    let accumulate_values (env,acc) param =
      let (Wt.Parameter pexpr) = param in
      let env,t = t_of_expression (env,acc) pexpr in
      begin match t with
      | _ :: _ ->
        let operand_tmp, env = inc_tmp env in
        let param_stmt = Call_param (Identifier (make_tmp_name operand_tmp)) in
        env, param_stmt :: t
      | [] ->
        let result_tmp, env = inc_tmp env in
        let call_stmt = Assign ((make_tmp_name result_tmp), Funcall name) in
        env, call_stmt :: acc
      end
    in
    let start_call_stmt = Start_call name in
    let acc = start_call_stmt :: acc in
    let env,acc = List.fold ~init:(env,acc) ~f:accumulate_values params in
    (env,acc)

let rec t_of_statement (env,acc) stmt =
  match stmt with
  | Wt.Exp e ->
    t_of_expression (env,acc) e
  | Wt.Vardec (vname,_,vexpr) ->
    let env,t = t_of_expression (env,acc) vexpr in
    (* Result of the expression *)
    let res_tmp = Identifier (make_tmp_name env.curr_tmp) in
    let new_stmt = Assign (vname, Value res_tmp) in
    (env, new_stmt :: t)
  | Wt.Compound cs ->
    List.fold ~init:(env,acc) ~f:t_of_statement cs
  | Wt.While (cond,wstmt) ->
    let loop_label_num, env = inc_label env in
    let loop_label_stmt = Label (make_loop_name loop_label_num) in
    let acc = loop_label_stmt :: acc in

    (* Make the conditional statement list with the accumulator *)
    let (env,acc) = t_of_expression (env,acc) cond in
    let cond_res_tmp = Identifier (make_tmp_name env.curr_tmp) in

    (* Create the loop body statement list with an empty accumulator *)
    (* So we can stitch it back later *)
    let (env,loop_acc) = t_of_statement (env,[]) wstmt in
    let end_loop_label_num, env = inc_label env in
    let end_loop_label = Label (make_loop_name end_loop_label_num) in
    let loop_acc = end_loop_label :: loop_acc in

    (* Make the conditional now that we know the end loop number *)
    let cond_stmt = If (cond_res_tmp,make_loop_name end_loop_label_num) in

    (* Put everything together*)
    (env, loop_acc @ (cond_stmt :: acc))
    | Wt.If (cond,then_stmt,else_stmt) ->
      let (env,acc) = t_of_expression (env,acc) cond in
      let res_tmp = Identifier (make_tmp_name env.curr_tmp) in

      let (env,else_acc) = match else_stmt with
      | None -> (env,[])
      | Some else_stmt ->
        let (env,else_acc) = t_of_statement (env,[]) else_stmt in
        (env,else_acc)
      in

      let then_loop_num, env = inc_label env in
      let then_loop_stmt = Label (make_loop_name then_loop_num) in
      let (env, then_acc) = t_of_statement (env,[then_loop_stmt]) then_stmt in
      let end_loop_num, env = inc_label env in
      let end_loop_stmt = Label (make_loop_name end_loop_num) in
      let then_acc = end_loop_stmt :: then_acc in

      let jump_then_stmt = If (res_tmp,make_loop_name then_loop_num) in
      let acc = jump_then_stmt :: acc in

      let jump_end_stmt = Goto (make_loop_name end_loop_num) in
      let else_acc = jump_end_stmt :: else_acc in

      (env,then_acc @ else_acc @ acc)
    | Wt.Mutate (name, expr) ->
      let (env,acc) = t_of_expression (env,acc) expr in
      let exp_tmp = Value (Identifier (make_tmp_name env.curr_tmp)) in
      let new_stmt = Assign (name, exp_tmp) in
      (env, new_stmt :: acc)
    | Wt.Return expr ->
      let (env,acc) = t_of_expression (env,acc) expr in
      let exp_tmp = Value (Identifier (make_tmp_name env.curr_tmp)) in
      let new_stmt = Return exp_tmp in
      (env,new_stmt :: acc)
    | Wt.Fun_def { name; params; ret_t; body} ->
      let fun_start_stmt = Function_start name in
      let acc = fun_start_stmt :: acc in
      (* Add function parameter info *)
      let (env,acc) = List.fold
        ~init:(env,acc)
        ~f:(fun (env,acc) (param_name,_) ->
          let fun_param_stmt = Function_param param_name in
          (env,fun_param_stmt :: acc))
        params
      in
      (* Add return type information *)
      let ret_type_stmt = Function_ret_type (Syntax.Types.ty_to_string ret_t) in
      let acc = ret_type_stmt :: acc in
      (* Turn body into statement list *)
      let (env,acc) = t_of_statement (env,acc) body in
      (env,acc)

let t_of_syntax_tree st =
  let env = new_environment () in
  let (_,acc) = t_of_statement (env,[]) st in
  acc