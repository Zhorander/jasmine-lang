open Lexer
open Lexing

let print_position outx lexbuf =
  let open Core in
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  let open Core in
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | Some value ->
    let pos = lexbuf.lex_curr_p in
    Printf.printf "%d\n" pos.pos_lnum;
    List.map Syntax.Untyped.sexp_of_stmt value
      |> List.map Core.Sexp.to_string
      |> List.iter print_endline
    (* (try
      parse_and_print lexbuf
    with
        Jasmine.TypeError s ->
          Printf.fprintf stderr "Type Error: %s\nline: %d\n" s pos.pos_lnum
      | Jasmine.Incompatible_Types s ->
          Printf.fprintf stderr "Incompatible Types: %s\nline: %d\n" s pos.pos_lnum
      | Jasmine.Invalid_Operation s ->
          Printf.fprintf stderr "Invalid Operation: %s\nline: %d\n" s pos.pos_lnum
      | Jasmine.Undeclared_Variable s ->
          Printf.fprintf stderr "Undeclared Variable: %s\nline: %d\n" s pos.pos_lnum
      | Jasmine.Unkown_Type s ->
          Printf.fprintf stderr "Unkown Type: %s\nline: %d\n" s pos.pos_lnum
    ) *)
  | None -> ()

let loop filename () =
  let open Core in
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  In_channel.close inx

let _ =
  let len = Array.length Sys.argv in
  if len = 2 then
    loop Sys.argv.(1) ()
  else
    print_endline "usage: test filename"