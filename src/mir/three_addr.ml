(* Three Address IR *)

open Core

module Wt = Syntax.Well_typed
module Ty = Common.Types.Well_typed
module Uty = Common.Types.Untyped
module Types = Common.Types
module Symtable = Common.Structs.Make_symbol_table(struct
  type t = Ty.some_ty
  let to_string = fun (Ty.Ty ty) -> Ty.to_string ty
end)
module Scope = Common.Structs.Scope(Symtable)

(* Environment definition *)
module Env = struct
  type t = {
    curr_tmp: int
    ; curr_label: int
    ; scope : Scope.t
  }

  let create () = {curr_tmp=0; curr_label=0; scope=Scope.create ()}

  let inc_tmp e = e.curr_tmp + 1, {e with curr_tmp=e.curr_tmp+1}

  let inc_label e = e.curr_label + 1, {e with curr_label=e.curr_label+1}

  let push_child_scope e = {e with scope=Scope.create ~par:(Some e.scope) ()}

  let pop_child_scope e = {
    e with scope = match e.scope.parent with
    Some par -> par | None -> raise (Common.Exceptions.Compiler_error "Scope is not a child scope.")}
end


module Location = struct
  type t =
    | Identifier of string
    | Temporary of int

  let to_string = function
    | Identifier i -> i
    | Temporary i -> Printf.sprintf "@%d" i

  let register_tmp: type a. Env.t -> a Ty.t -> (t * Env.t) = fun env ty ->
    let (tmp_i,env) = Env.inc_tmp env in
    let tmp = Temporary tmp_i in
    Scope.add_symbol ~scope:env.scope (to_string tmp) (Ty.Ty ty);
    tmp,env

end

module Value = struct
  type _ t =
    | Int : int -> int t
    | Bool : bool -> bool t
    | Unit : unit -> unit t
    | Loc : Location.t * 'a Ty.t -> 'a t

  let to_string: type a. a t -> string = function
    | Int i -> string_of_int i
    | Bool b -> string_of_bool b
    | Unit () -> "()"
    | Loc (loc,_) -> Location.to_string loc

  let to_ty : type a. a t -> a Ty.t = fun t ->
    match t with
    | Int _ -> Ty.Int
    | Bool _ -> Ty.Bool
    | Unit _ -> Ty.Unit
    | Loc (_,ty) -> ty

  let eq_types: type a b. a t -> b t -> (a,b) Common.Types.eq
  = fun va vb ->
    match (va,vb) with
    | (Int _, Int _) -> Types.Refl
    | (Bool _, Bool _) -> Types.Refl
    | (Unit (), Unit ()) ->Types.Refl
    | _ -> raise (Common.Exceptions.TypeError "")
end

module Statement = struct
  type t =
    | Decl : string * 'a Ty.t -> t
    | Assign : Location.t * 'a Value.t -> t
    | Label : int -> t
    (* Jump statements *)
    | Goto : int -> t
    | Return : 'a Value.t -> t
    | If : bool Value.t * int -> t
    (* Function stuff *)
    | Start_call : string -> t
    | Call_param : 'a Value.t -> t
    | Function_start : string -> t
    | Function_end : t
    | Function_param : string * 'a Ty.t -> t
    | Function_ret_type : 'a Ty.t -> t
    | Function_call : string * Location.t -> t
    (* Expressions *)
    | Add : int Value.t * int Value.t * Location.t -> t
    | Sub : int Value.t * int Value.t * Location.t -> t
    | Mult : int Value.t * int Value.t * Location.t -> t
    | Div : int Value.t * int Value.t * Location.t -> t
    | Equal : 'a Value.t * 'a Value.t * Location.t -> t
    | Not_equal : 'a Value.t * 'a Value.t * Location.t -> t
    | Not : bool Value.t * Location.t -> t

  let string_of_binary: type a b. a Value.t -> b Value.t -> Location.t -> string -> string =
    fun lhv rhv loc op ->
    let lhs = Value.to_string lhv in
    let rhs = Value.to_string rhv in
    let loc_s = Location.to_string loc in
    Printf.sprintf "%s := %s %s %s;" loc_s lhs op rhs

  let string_of_unary: type a . a Value.t -> Location.t -> string -> string
    = fun v loc op ->
    Printf.sprintf "%s := %s %s;"
    (Location.to_string loc)
    (Value.to_string v)
    op

  let to_string = function
    | Decl (name,ty) -> Printf.sprintf "let %s: %s;" name (Ty.to_string ty)
    | Assign (loc, v) ->
      Printf.sprintf "%s := %s;" (Location.to_string loc) (Value.to_string v)
    | Label i -> "L" ^ (string_of_int i) ^ ":"
    | Goto i -> "goto L" ^ (string_of_int i) ^ ";"
    | Return v -> "return " ^ (Value.to_string v) ^ ";"
    | If (bv,i) ->
      Printf.sprintf "if %s -> L%d;" (Value.to_string bv) i
    | Start_call name -> "start_call " ^ name ^ ";"
    | Call_param v -> "param " ^ (Value.to_string v) ^ ";"
    | Function_start name -> "function " ^ name
    | Function_end -> "end"
    | Function_param (name,ty) -> Printf.sprintf "in %s : %s" name (Ty.to_string ty)
    | Function_ret_type ty -> "out " ^ (Ty.to_string ty)
    | Function_call (name,loc) -> Printf.sprintf "%s := %s;" name (Location.to_string loc)
    | Add (lhv,rhv,loc) -> string_of_binary lhv rhv loc "+"
    | Sub (lhv,rhv,loc) -> string_of_binary lhv rhv loc "-"
    | Mult (lhv,rhv,loc) -> string_of_binary lhv rhv loc "*"
    | Div (lhv,rhv,loc) -> string_of_binary lhv rhv loc "/"
    | Equal (lhv,rhv,loc) -> string_of_binary lhv rhv loc "=="
    | Not_equal (lhv,rhv,loc) -> string_of_binary lhv rhv loc "!="
    | Not (v,loc) -> string_of_unary v loc "!"
end


(* Convert a Well-typed expression into a statement list *)
let rec t_of_expression : type a. Env.t * (Statement.t list) -> a Wt.expr -> Env.t * (Statement.t list)
  = fun (env,acc) expr ->
  (* Helper function to make a binary statement *)
  let make_binary: type b. b Ty.t -> b Wt.expr -> b Wt.expr ->
    (b Value.t -> b Value.t -> Location.t -> Statement.t) ->
    Env.t * (Statement.t list)
    = fun ty lhe rhe make_stmt ->
    (* turn the left hand side into three-address structs, take the resulting tmp var *)
    let env,acc = t_of_expression (env,acc) lhe in
    let lh_tmp_var = Value.Loc (Location.Temporary env.curr_tmp, ty) in
    (* same for the right hand side *)
    let env,acc = t_of_expression (env,acc) rhe in
    let rh_tmp_var = Value.Loc (Location.Temporary env.curr_tmp, ty) in
    (* we increment the tmp var in the environment to create a new temp variable *)
    let (res_tmp,env) = Location.register_tmp env ty in
    let res_decl = Statement.Decl (Location.to_string res_tmp, ty) in
    (* our new temp variable is the result of the binary expression between the
       previous temp variables *)
    let new_stmt = make_stmt lh_tmp_var rh_tmp_var res_tmp in
    (env, new_stmt :: res_decl :: acc)
  in
  (* Helper function to make a unary statement *)
  let make_unary: type b. b Ty.t -> b Wt.expr -> (b Value.t -> Location.t -> Statement.t) ->
    Env.t * (Statement.t list)
    = fun ty e make_stmt ->
    let env,acc = t_of_expression (env,acc) e in
    let t_tmp_var = Value.Loc (Location.Temporary env.curr_tmp, ty) in
    let unary_tmp_var, env = Env.inc_tmp env in
    let res_tmp = Location.Temporary unary_tmp_var in
    let res_decl = Statement.Decl (Location.to_string res_tmp, ty) in
    let new_stmt = make_stmt t_tmp_var res_tmp in
    (env, new_stmt :: res_decl :: acc)
  in
  (* Helper function to turn a value expression into a statement *)
  let make_value : type b. b Value.t -> b Ty.t -> Env.t * (Statement.t list)
    = fun bv bty ->
    let (tmp_loc, env) = Location.register_tmp env bty in
    let decl_tmp = Statement.Decl (Location.to_string tmp_loc, bty) in
    let new_stmt = Statement.Assign (tmp_loc, bv) in
    (env, new_stmt :: decl_tmp :: acc)
  in
  match expr with
  | Wt.Unit u -> make_value (Value.Unit u) (Ty.Unit)
  | Wt.Int i -> make_value (Value.Int i) (Ty.Int)
  | Wt.Bool b -> make_value (Value.Bool b) (Ty.Bool)
  | Wt.Ident i ->
    (* Similar to other values, but need to ask symtable for type *)
    let (Ty.Ty id_ty) = Scope.find ~scope:env.scope i in
    make_value (Value.Loc ((Location.Identifier i), id_ty)) (id_ty)
  | Wt.Group g ->
    t_of_expression (env,acc) g
  | Wt.Plus (lhe, rhe) ->
    make_binary Ty.Int lhe rhe (fun lh rh loc -> Add (lh, rh, loc))
  | Wt.Sub (lhe, rhe) ->
    make_binary Ty.Int lhe rhe (fun lh rh loc -> Sub (lh, rh, loc))
  | Wt.Mult (lhe, rhe) ->
    make_binary Ty.Int lhe rhe (fun lh rh loc -> Mult (lh, rh, loc))
  | Wt.Div (lhe, rhe) ->
    make_binary Ty.Int lhe rhe (fun lh rh loc -> Div (lh, rh, loc))
  | Wt.Equal (lhe, rhe) ->
    make_binary Ty.Bool lhe rhe (fun lh rh loc -> Equal (lh, rh, loc))
  | Wt.Not_equal (lhe, rhe) ->
    make_binary Ty.Bool lhe rhe (fun lh rh loc -> Not_equal (lh, rh, loc))
  | Wt.Not exp -> make_unary Ty.Bool exp (fun x loc -> Not (x, loc))
  | Wt.Funcall (name,params) ->
    let accumulate_values (env,acc) param =
      let (Wt.Parameter pexpr) = param in
      let env,t = t_of_expression (env,acc) pexpr in
      begin match t with
      | _ :: _ ->
        let (Ty.Ty ty) = Location.Temporary (env.curr_tmp)
          |> Location.to_string
          |> Scope.find ~scope:env.scope
        in
        let param_stmt = Statement.Call_param (Value.Loc ((Location.Temporary env.curr_tmp), ty)) in
        env, param_stmt :: t
      | [] ->
        (env,acc)
      end
    in
    let start_call_stmt = Statement.Start_call name in
    let acc = start_call_stmt :: acc in
    let env,acc = List.fold ~init:(env,acc) ~f:accumulate_values params in
    (* result *)
    let result_tmp, env = Env.inc_tmp env in
    let call_stmt = Statement.Function_call (name, Location.Temporary result_tmp) in
    env, call_stmt :: acc

let rec t_of_statement (env,acc) stmt =
  match stmt with
  | Wt.Exp e ->
    let (Wt.Expr (e,_)) = e in
    t_of_expression (env,acc) e
  | Wt.Vardec (vname,some_vexpr) ->
    let Expr (vexpr, expr_ty) = some_vexpr in
    (* Add variable to the symbol table *)
    Scope.add_symbol ~scope:env.scope vname (Ty.Ty expr_ty);
    (* Declare the variable *)
    let decl_var = Statement.Decl (vname, expr_ty) in
    (* Expand the expression *)
    let env,acc = t_of_expression (env,acc) vexpr in
    (* Result of the expression *)
    let res_tmp = Location.Temporary env.curr_tmp in
    let new_stmt = Statement.Assign (Location.Identifier vname, Value.Loc (res_tmp, expr_ty)) in
    (env, new_stmt :: decl_var :: acc)
  | Wt.Compound cs ->
    let env = Env.push_child_scope env in
    List.fold ~init:(env,acc) ~f:t_of_statement cs
  | Wt.While (cond,wstmt) ->
    let loop_label_num, env = Env.inc_label env in
    let loop_label_stmt = Statement.Label loop_label_num in
    let acc = loop_label_stmt :: acc in

    (* Make the conditional statement list with the accumulator *)
    let (env,acc) = t_of_expression (env,acc) cond in
    let cond_res_tmp = Value.Loc (Location.Temporary env.curr_tmp, Ty.Bool) in

    (* Create the loop body statement list with an empty accumulator *)
    (* So we can stitch it back later *)
    let (env,loop_acc) = t_of_statement (env,[]) wstmt in
    let end_loop_label_num, env = Env.inc_label env in
    let end_loop_label = Statement.Label end_loop_label_num in

    (* Make the conditional now that we know the end loop number *)
    let cond_stmt = Statement.If (cond_res_tmp,end_loop_label_num) in

    (* Jump back to the cond at end of loop *)
    let jump_start_stmt = Statement.Goto loop_label_num in
    let loop_acc = jump_start_stmt :: loop_acc in

    (* Add the end loop label at the end *)
    let loop_acc = end_loop_label :: loop_acc in

    (* Put everything together*)
    (env, loop_acc @ (cond_stmt :: acc))
  | Wt.If (cond,then_stmt,else_stmt) ->
    let (env,acc) = t_of_expression (env,acc) cond in
    let (Ty.Ty ty) = Location.Temporary (env.curr_tmp)
      |> Location.to_string
      |> Scope.find ~scope:env.scope
    in
    let Types.Refl = Ty.eq_types ty Ty.Bool in
    let res_tmp = Value.Loc (Location.Temporary env.curr_tmp, ty) in

    let (env,else_acc) = match else_stmt with
    | None -> (env,[])
    | Some else_stmt ->
      let (env,else_acc) = t_of_statement (env,[]) else_stmt in
      (env,else_acc)
    in

    let then_loop_num, env = Env.inc_label env in
    let then_loop_stmt = Statement.Label then_loop_num in
    let (env, then_acc) = t_of_statement (env,[then_loop_stmt]) then_stmt in
    let end_loop_num, env = Env.inc_label env in
    let end_loop_stmt = Statement.Label end_loop_num in
    let then_acc = end_loop_stmt :: then_acc in

    let jump_then_stmt = Statement.If (res_tmp, then_loop_num) in
    let acc = jump_then_stmt :: acc in

    let jump_end_stmt = Statement.Goto end_loop_num in
    let else_acc = jump_end_stmt :: else_acc in

    (env,then_acc @ else_acc @ acc)
  | Wt.Mutate (name, expr) ->
    Scope.dump ~scope:env.scope;
    let (env,acc) = t_of_expression (env,acc) expr in
    let (Ty.Ty ty) = Location.Temporary (env.curr_tmp)
      |> Location.to_string
      |> Scope.find ~scope:env.scope
    in
    let exp_tmp = Value.Loc (Temporary env.curr_tmp, ty) in
    let new_stmt = Statement.Assign (Location.Identifier name, exp_tmp) in
    (env, new_stmt :: acc)
  | Wt.Return expr ->
    let (Wt.Expr (expr,ety)) = expr in
    let (env,acc) = t_of_expression (env,acc) expr in
    let (Ty.Ty ty) = Location.Temporary (env.curr_tmp)
      |> Location.to_string
      |> Scope.find ~scope:env.scope
    in
    let Types.Refl = Ty.eq_types ty ety in
    let exp_tmp = Value.Loc (Location.Temporary env.curr_tmp, ty) in
    let new_stmt = Statement.Return exp_tmp in
    (env,new_stmt :: acc)
  | Wt.Fun_def { name; params; ret_t; body} ->
    (* Function starts a new scope *)
    let env = Env.push_child_scope env in
    let fun_start_stmt = Statement.Function_start name in
    (* Add function parameter info *)
    let (env,new_acc) = List.fold
      ~init:(env,acc)
      ~f:(fun (env,acc) (param_name,(Ty.Ty pty)) ->
        (* Add the param name to the symbol table *)
        Scope.add_symbol ~scope:env.scope param_name (Ty.Ty pty);
        (* Create the function param statement *)
        let fun_param_stmt = Statement.Function_param (param_name,pty) in
        (env,fun_param_stmt :: acc))
      params
    in
    (* Type check returns *)
    List.iter ~f:(function
      | Statement.Return v ->
        let Common.Types.Refl = Ty.eq_types (Value.to_ty v) ret_t in ()
      | _ -> ()
    )
    new_acc;
    let acc = new_acc @ fun_start_stmt :: acc in
    (* Add return type information *)
    let ret_type_stmt = Statement.Function_ret_type ret_t in
    let acc = ret_type_stmt :: acc in
    (* Turn body into statement list *)
    let (env,acc) = t_of_statement (env,acc) body in
    (* Mark the end of the function *)
    let end_fun_stat = Statement.Function_end in
    let acc = end_fun_stat :: acc in
    (* Now that we've processed the body, we can pop the child scope *)
    let env = Env.pop_child_scope env in
    (env,acc)

let t_of_syntax_tree_list st_list =
  let st_list = List.rev st_list in
  let env = Env.create () in
  let (_,acc) = List.fold
    ~init:(env,[])
    ~f:(fun (env,acc) stat ->
      t_of_statement (env,[]) stat
      |> fun (env,new_acc) -> env, new_acc @ acc)
    st_list
  in
  List.rev acc