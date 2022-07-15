
type expression = U

type statement = T

type terminator = Goto of int | Return of expression

type t = {
  label: int
  ; statements: statement list
  ; terminator: terminator
}

type bb_function = {
  name: string
  ; ret_type: string
  ; operands: expression list
  ; body: t list
}