; Calling convention is first operand in register acc, then y, and the rest in the stack
; The stack, for the callee, looks like [param3,param4,...,ret_address]
; The return value is stored in the accumulator

; function fizzbuzz(x: int) -> unit
fizzbuzz:
pull_param %r1
push $0
mov %r1, %acc
mod $3
cmp $0
jneq L1
pop %acc
add $1
push %acc
L1:
mov %r1, %acc
mod $5
cmp $0
jneq L2
pop %acc
add $2
push %acc
L2:
push_param (sptr,1) ; stack grows down
call color_screen
ret

main:
push $1
loop:
mov (sptr), %acc
cmp $100
jeq loop_end
push_param (sptr)
call fizzbuzz
pop %acc
add $1
push %acc
jmp loop