type register =
  | Acc_reg
  | X_reg
  | Y_reg
  | Stack_reg
  | Base_ptr

type location =
  | Register of register
  | Memory_location of int

type value =
  | Location of location
  (* ptr, offset *)
  | Indirect of location * int
  | Constant of int

type t =
  | Push of value
  | Pop of location
  (* Arithmetic operates on accumulator *)
  | Add of value
  | Sub of value
  | Mult of value
  | Div of value
  | Transfer of location * location
  | Label of string
  | Jump of string
  | Jeq of string
  | Jneq of string
  | Mov of value * location
  | Jsr of string
  | Rts