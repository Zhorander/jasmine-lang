open Lexer
open Lexing

open Core

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let rec parse_and_print acc scope lexbuf =
  match parse_with_error lexbuf with
  | Some value ->
    begin try
      let syntax_tree = Syntax.ustmt_to_tstmt scope value in
      parse_and_print (syntax_tree :: acc) scope lexbuf
    
    with
        Syntax.Exceptions.TypeError s as te ->
          fprintf stderr "Type Error: %s %a\n" s print_position lexbuf;
          raise te
      | Syntax.Exceptions.Undeclared_Variable s as uv ->
          Printf.fprintf stderr "Undeclared Variable: %s %a\n" s print_position lexbuf;
          raise uv
    end
  | None -> acc

let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let global_scope = Syntax.Structs.Scope.create () in
  let tree_list: Syntax.Well_typed.stmt list = parse_and_print [] global_scope lexbuf in
  let three_addrs =
    Mir.Three_addr.t_of_syntax_tree_list tree_list
    |> List.map ~f:Mir.Three_addr.string_of_statement
  in
  List.iter ~f:print_endline three_addrs;
  In_channel.close inx

let _ =
  let len = Array.length (Sys.get_argv ()) in
  if len = 2 then
    loop (Sys.get_argv ()).(1) ()
  else
    print_endline "usage: test filename"