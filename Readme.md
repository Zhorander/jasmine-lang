# Jasmine Language

Compiler implementation for my language, Jasmine. The goal of this project is
to create a well-typed language that can be compiled into various targets, such as 6502 and z80 assembly for making games for older consoles.

## Milestones

- [ x ] Implement the scanner and parser
- [ x ] Create an abstract syntax tree
- [ x ] Turn the abstract syntax tree into a well-typed syntax tree
- [   ] Lambda lifting?
- [   ] Polymorphism and Monomorphization?
- [   ] Optimization passes
- [   ] Compile into an intermmediate representation(s)
- [   ] Compile IR into target language(s)

## Early thoughts on syntax and structure

### Strong Static Typing

Jasmine will use a strong typing system that will hopefully not undermine its
potential use in low-level systems such as the Gameboy and NES.

```
fun main(): int {
  // This is an error
  let x: int = 24 * true;

  // # Specifies that the following number literal is an address literal
  let y: &int = #0x0f;

  // Type error
  let y: &int = 0x0f;

  // Perhaps (+) will be polymorphic in addessr<a> -> int -> address<a>
  // Where 'a' is a parametric parameter

  // Type error
  let y: int = #23;
}
```

### Immutability by Default

Jasmine will start with no mutability rules, but the goal is to have immutability
be the default behavior, with a 'mut' tag similar to Rust's.

```
let x: int = 3;

// error
x = 2;

let mut x: int = 3;

// ok
x = 2;
```

### Specific Int Sizes

Since one of the goals of this project is to target different old console systems,
fine grain -- and explicit -- control of integer sizes will be crucial for
reasoning about the output. Names such as short, int, long, ... are too ambiguous.

For prototyping, however, Jasmine will only use an ambiguous 'int' type.

### Feature Specification

Not yet sure how to proceed on this. Some older systems (like the Atari) don't
have support for floating point numbers. How should Jasmine treat compilation
of these numbers? Implicitly convert to u8s? Refuse to compile? Or something
else altogether?

### Variable Shadowing

For a language that exhibits immutability by default, it may be more ergonomic to shadow a variable declaration rather than defining multiple, slightly different, variables.

```
fun some_function(a: int): bool { ... }

fun main(): int {
  let x: int = 3;
  let x: bool = some_function(x);

  // however, note that this would be an error
  let x: int = 3;
  x = some_function(x);
}
```

### Other Features

While the other mentioned aspects of the language are simple, and generally easy to reason about the resulting assembly -- an important consideration for its intended targets -- there are other lanugage features that would be nice to have, such as higher order functions, traits, and polymorphism.

#### Higher Order Functions

Higher order functions may be easy to reason about W.R.T. assembly output, and even a parametricly polymorphic function. However, the code size may increase unreasonably so for a smaller target system, such as the Atari.

#### Sum Types

Most languages have some way to represent a sum type. Some even have ways to generically pack information into them (Some[a]|None, Result[a]|Error[string], ...). Representing a simple sum type would be simple and easy to see how it translates to its target, but are there simple, compact ways to represent the following type declaration?:

$ type\ t = Int\ of\ int\ | Bool\ of\ bool\ | Float\ of\ float$

