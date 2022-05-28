(* Three Address  *)

type value =
  | Int of int
  | Bool of bool
  | Identifier of string

type expression =
  | Add of value * value
  | Sub of value * value
  | Less_than of value * value
  | Greather_than of value * value
  | Less_or_equal of value * value
  | Greater_or_equal of value * value
  | Funcall of value list

type statement =
  | Assign of string * expression
  | Goto of int
  | Return
  | If of expression * int
