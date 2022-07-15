(* Three Address Form Optimizations *)

module Ta = Three_addr

module Types = Common.Types

type some_value = Some_val : 'a Ta.Value.t * 'a Types.Well_typed.t -> some_value

module Symtable = Common.Structs.Make_symbol_table(struct
  type t = some_value
  let to_string = fun (Some_val (v,_)) -> Ta.Value.to_string v
end)

module Scope = Common.Structs.Scope(Symtable)

open Core


module Env = struct
  type t = {
    valuescope: Scope.t;
    symscope: Ta.Scope.t
  }

  let create () = {
    valuescope = Scope.create ();
    symscope = Ta.Scope.create ()
  }

  let add_value ~env name v = Scope.add_symbol ~scope:env.valuescope name v

  let add_symbol ~env name s = Ta.Scope.add_symbol ~scope:env.symscope name s

  let get_symbol ~env name = Ta.Scope.find ~scope:env.symscope name
end


(* The simplest optimization for this form is constant-propogation
  since temporary variables are created throughout the process
 *)

let is_loc_tmp = function
  | Ta.Location.Temporary _ -> true
  | _ -> false

let is_tmp_val = function
  | Ta.Value.Loc (l,_) -> is_loc_tmp l
  | _ -> false

let is_tmp_string name = String.contains ~pos:0 name '@'

let replace_tmp_val : type b. Env.t -> b Ta.Value.t -> b Ta.Value.t option
  = fun env value ->
  match value with
  | Ta.Value.Loc (Ta.Location.Temporary i, loc_ty) ->
    let i_str = Ta.Location.to_string (Ta.Location.Temporary i) in
    if Scope.symbol_exists ~scope:env.valuescope i_str then
      let (Some_val (v,otherty)) = Scope.find ~scope:env.valuescope i_str in
      let Types.Refl = Types.Well_typed.eq_types otherty loc_ty in
      Some v
    else
      None
  | _ -> None


let constant_propogation_stmt ((env:Env.t),acc) stmt =
  let propogate_binary: type a. a Ta.Value.t -> a Ta.Value.t ->
  a Ta.Value.t * a Ta.Value.t
  = fun lh rh ->
    let lh_val = replace_tmp_val env lh
      |> Option.value ~default:lh
    in
    let rh_val = replace_tmp_val env rh
      |> Option.value ~default:rh
    in
    (lh_val,rh_val)
  in
  let propogate_unary: type a. a Ta.Value.t -> a Ta.Value.t
  = fun v ->
    let v_val = match replace_tmp_val env v with Some v -> v | None -> v in
    v_val
  in
  match stmt with
  | Ta.Statement.Assign (loc,v) ->
    let ty = Ta.Value.to_ty v in
    let v = match replace_tmp_val env v with Some v -> v | None -> v in
    (* If the location is a temporary variable, then add the expression to the symbol table *)
    if is_loc_tmp loc then Scope.add_symbol ~scope:env.valuescope (Ta.Location.to_string loc) (Some_val (v,ty));

    let new_stmt = Ta.Statement.Assign (loc, v) in
    env, new_stmt :: acc
  | Ta.Statement.If (v,lbl) ->
    let v = replace_tmp_val env v
      |> Option.value ~default:v
    in
    let new_stmt = Ta.Statement.If (v, lbl) in
    env, new_stmt :: acc
  | Ta.Statement.Return v ->
    let v = replace_tmp_val env v
      |> Option.value ~default:v
    in
    let new_stmt = Ta.Statement.Return v in
    env, new_stmt :: acc
  | Ta.Statement.Call_param v ->
    let v = replace_tmp_val env v
      |> Option.value ~default:v
    in
    let new_stmt = Ta.Statement.Call_param v in
    env, new_stmt :: acc

  | Ta.Statement.Add (lh,rh,loc) ->
    let (lh_val,rh_val) = propogate_binary lh rh in
    let new_stmt = Ta.Statement.Add (lh_val, rh_val, loc) in
    env, new_stmt :: acc
  | Ta.Statement.Sub (lh,rh,loc) ->
    let (lh_val,rh_val) = propogate_binary lh rh in
    let new_stmt = Ta.Statement.Sub (lh_val, rh_val, loc) in
    env, new_stmt :: acc
  | Ta.Statement.Mult (lh,rh,loc) ->
    let (lh_val,rh_val) = propogate_binary lh rh in
    let new_stmt = Ta.Statement.Mult (lh_val, rh_val, loc) in
    env, new_stmt :: acc
  | Ta.Statement.Div (lh,rh,loc) ->
    let (lh_val,rh_val) = propogate_binary lh rh in
    let new_stmt = Ta.Statement.Div (lh_val, rh_val, loc) in
    env, new_stmt :: acc
  | Ta.Statement.Equal (lh,rh,loc) ->
    let (lh_val,rh_val) = propogate_binary lh rh in
    let new_stmt = Ta.Statement.Equal (lh_val, rh_val, loc) in
    env, new_stmt :: acc
  | Ta.Statement.Not_equal (lh,rh,loc) ->
    let (lh_val,rh_val) = propogate_binary lh rh in
    let new_stmt = Ta.Statement.Not_equal (lh_val, rh_val, loc) in
    env, new_stmt :: acc
  | Ta.Statement.Not (v,loc) ->
    let v_val = propogate_unary v in
    let new_stmt = Ta.Statement.Not (v_val, loc) in
    env, (new_stmt :: acc)
  | _ -> env, (stmt :: acc)


let collect_temps stmts =
  List.filter_map
    ~f:(function
      | Ta.Statement.Decl (name,_) -> Some name
      | _ -> None)
    stmts
  |> List.filter ~f:is_tmp_string


let register_decls env stmts =
  List.iter ~f:(function
    | Ta.Statement.Decl (name, ty) ->
      Env.add_symbol ~env name (Types.Well_typed.Ty ty)
    | _ -> ()
    )
    stmts;
  env


let elide_temps (used,acc) stmt =
  let collect_temps_from_vals vals =
    List.filter ~f:is_tmp_val vals
    |> List.map ~f:Ta.Value.to_string
  in
  match stmt with
  | Ta.Statement.Decl (name,_) ->
    if (is_tmp_string name)
      && not (List.exists used ~f:(String.equal name))
    then
      used, acc
    else
      used, stmt :: acc
  | Ta.Statement.Assign (loc,v) ->
    if (is_loc_tmp loc)
      && not (List.exists used ~f:(String.equal (Ta.Location.to_string loc)))
    then
      used, acc
    else
      let used_tmps = collect_temps_from_vals [v] in
      (used_tmps @ used), stmt :: acc
  | Ta.Statement.If (v,_) ->
    let used_tmps = collect_temps_from_vals [v] in
    (used_tmps @ used), stmt :: acc
  | Ta.Statement.Return v ->
    let used_tmps = collect_temps_from_vals [v] in
    (used_tmps @ used), stmt :: acc
  | Ta.Statement.Call_param v ->
    let used_tmps = collect_temps_from_vals [v] in
    (used_tmps @ used), stmt :: acc
  | _ -> used, (stmt :: acc)


let optimize stmts =
  let () =
    List.map ~f:Ta.Statement.to_string stmts
    |> List.iter ~f:print_endline
  in
  print_endline "========================";
  let env = register_decls (Env.create ()) stmts in
  Ta.Scope.dump ~scope:env.symscope;
  List.fold ~init:(env,[]) ~f:constant_propogation_stmt stmts
  |> fun (_,prop_stmts) -> prop_stmts
  |> List.rev
  |> List.fold ~init:([],[]) ~f:elide_temps
  |> fun (_, elided_stmts) -> elided_stmts