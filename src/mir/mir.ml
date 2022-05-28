(* The Mid-Level Intermmediate Representation  *)

(* open Core *)

module Basic_block = struct
  type t = int * Three_addr.statement
end

module Function = struct
  type t = {
    name: string
    ; 
  }
end

type t = (int * Basic_block.t) list
