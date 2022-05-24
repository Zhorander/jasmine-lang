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

let rec parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | Some value ->
    begin try
      let global_scope = Structs.Scope.create () in
      let _ = Syntax.ustmt_to_tstmt global_scope value in
      (* let _ = Mir.Basic_block.create 1 in *)
      parse_and_print lexbuf
    
    with
        Exceptions.TypeError s ->
          fprintf stderr "Type Error: %s %a\n" s print_position lexbuf
      | Exceptions.Undeclared_Variable s ->
          Printf.fprintf stderr "Undeclared Variable: %s %a\n" s print_position lexbuf
    end
  | None -> ()

let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  In_channel.close inx

let _ =
  let len = Array.length (Sys.get_argv ()) in
  if len = 2 then
    loop (Sys.get_argv ()).(1) ()
  else
    print_endline "usage: test filename"