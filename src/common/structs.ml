open Core

module type Symbol = sig
  type t

  val to_string : t -> string
end

module type Symbol_table = sig
  type key = string
  type symbol
  type t = (key,symbol) Hashtbl.t

  val create : unit -> t

  val add_symbol : symtbl:t -> key -> symbol -> unit

  val find : symtbl:t -> key -> symbol option

  val exists : symtbl:t -> key -> bool

  val dump : symtbl:t -> unit

  val remove: symtbl:t -> key -> unit
end

module Make_symbol_table(Sym : Symbol)
: (Symbol_table with type symbol = Sym.t) = struct

  type key = string
  type symbol = Sym.t
  type t = (key,symbol) Hashtbl.t

  let create () =
    Hashtbl.create ~growth_allowed:true (module String)
  
  let add_symbol ~(symtbl:t) (sym:string) (symtype:symbol) =
    match Hashtbl.add symtbl ~key:sym ~data:symtype with
    | `Duplicate ->
      let err_str = (Printf.sprintf "Shadowed Symbol '%s'" sym) in
      raise (Exceptions.Shadowed_Symbol err_str)
    | `Ok -> ()

  (*get the symbol type from the table*)
  let find ~symtbl sym = Hashtbl.find symtbl sym

  (*does a symbol exist in the table?*)
  let exists ~(symtbl:t) (sym:key) =
    match Hashtbl.find symtbl sym with
    | Some _ -> true
    | None -> false

  let dump ~(symtbl:t) =
    let print_entry ~key ~data =
      Printf.printf "%s : %s\n" key (Sym.to_string data)
    in
    Printf.printf "SYMTABLE DUMP\n-------------\n";
    Hashtbl.iteri ~f:print_entry symtbl;
    Printf.printf "=============\n"

  let remove ~(symtbl:t) (sym:key) =
    Hashtbl.remove symtbl sym
end

module Scope (Symtbl : Symbol_table with type key = string) = struct
  type t = {
    symtbl: Symtbl.t;   (* symbol table *)
    parent: t option
  }

  let create ?par:(p=None) () =
    { symtbl = Symtbl.create ();
      parent = p }

  let rec find ~scope sym =
    match scope.parent,(Symtbl.find ~symtbl:scope.symtbl sym) with
    | _, (Some ty) -> ty
    | (Some par),None -> find ~scope:par sym
    | None,None -> raise (Exceptions.Undeclared_Variable sym)

  let add_symbol ~scope sym sym_t =
    let symtbl = scope.symtbl in
    Symtbl.add_symbol ~symtbl sym sym_t

  let symbol_exists ~scope sym =
    Symtbl.exists ~symtbl:scope.symtbl sym

  let rec dump ~scope =
    Symtbl.dump ~symtbl:scope.symtbl;
    match scope.parent with
    | None -> ()
    | Some par -> dump ~scope:par

  let remove ~scope sym =
    Symtbl.remove ~symtbl:scope.symtbl sym
end
