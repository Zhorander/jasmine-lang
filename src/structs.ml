open Core

module Symtable = struct
  type t = (string, Types.uty) Hashtbl.t

  let create: unit -> t = fun () ->
    Hashtbl.create ~growth_allowed:true (module String)
  
  let add_symbol ~(symtbl:t) (sym: string) (symtype: Types.uty) =
    match Hashtbl.add symtbl ~key:sym ~data:symtype with
    | `Duplicate ->
      let err_str = (Printf.sprintf "Shadowed Symbol '%s'" sym) in
      raise (Exceptions.Shadowed_Symbol err_str)
    | `Ok -> ()
  
  (*get the symbol type from the table*)
  let find ~(symtbl: t) (sym: string) = Hashtbl.find symtbl sym

  (*does a symbol exist in the table?*)
  let exists ~(symtbl: t) (sym: string) =
    match Hashtbl.find symtbl sym with
    | Some _ -> true
    | None -> false

  let dump ~(symtbl: t) =
    let print_entry ~key ~data =
      Printf.printf "%s : %s\n" key (Types.uty_to_string data)
    in
    Printf.printf "SYMTABLE DUMP\n=============\n";
    Hashtbl.iteri ~f:print_entry symtbl;
    Printf.printf "=============\n";
end

module Scope = struct
  type t = {
    symtbl: Symtable.t;   (* symbol table *)
    parent: t option
  }

  let create ?par:(p=None) () =
    { symtbl = Symtable.create ();
      parent = p }

  let rec find ~scope sym =
    match scope.parent,(Symtable.find ~symtbl:scope.symtbl sym) with
    | _, (Some ty) -> ty
    | (Some par),None -> find ~scope:par sym
    | None,None -> raise (Exceptions.Undeclared_Variable sym)

  let add_symbol ~scope sym sym_t =
    let symtbl = scope.symtbl in
    Symtable.add_symbol ~symtbl sym sym_t
end
