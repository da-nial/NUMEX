# NUMEX: Number-Expression Programming Language

This project involves the design and implementation of an interpreter for the Number-Expression Programming Language (
NUMEX). NUMEX programs are written in Racket using constructors defined by the structs. The language supports various
expressions, including arithmetic operations, logical operations, conditional expressions, functions, and more. The
project assumes that NUMEX programs are syntactically correct and free of type errors.

The project is explained in detail in the [docs/instructions.pdf](docs/instructions.pdf) file, in English.

### Syntax

- Variables, numbers, booleans
- Arithmetic (+, -, *, /), logical (`andalso`, `orelse`), and comparison (`iseq`) operations
- Conditionals (`cnd`, `ifnzero`, `ifleq`)
- Functions (`lam`), function application (`apply`)
- Let bindings (with)
- Pairs (`apair`) and list operations (`1st`, `2nd`)
- Recursion (`letrec`)
- Records (`key`, `record`, `value`)

### Tasks

1. **Warm-Up**: Implement two Racket functions:
    - `racketlist->numexlist`: Converts a Racket list to a NUMEX list.
    - `numexlist->racketlist`: Converts a NUMEX list to a Racket list.

2. **Implementing NUMEX**: Implementing NUMEX consists of the following tasks.
    1. Implement NUMEX interpreter (`eval-exp`) as a Racket function: takes a NUMEX expression
       and returns the NUMEX value it evaluates to under the empty environment or calls Racket's error if evaluation
       encounters a run-time NUMEX type error or unbound NUMEX variables.
    2. Implement simple NUMEX type system (`infer-exp`)
    3. Write NUMEX macros for NUMEX extensions: Example Racket functions that produce NUMEX expressions that could then
       be put inside larger NUMEX expressions. (`ifmunit`, `with*`, `ifneq`)
    4. Example usage of NUMEX functions by writing NUMEX functions for list filtering (`numex-filter`) and
       comparison `numex-all-gt`.
    5. Experiment with type system limitations:
        1. `type-error-but-evaluates-ok`: An example expression that the type system infer it as a type error but the
           interpreter evaluates it fine.
        2. `type-ok-but-evaluates-error`: An example expression that the type system infer it fine but the interpreter
           evaluates it to an error.
    6. Optimize interpreter with free variable analysis (`eval-exp-c`): Building closures with smaller environments by
       holds only variables that are free variables in the function part of the closure. This is achieved via a utility
       function `compute-free-vars`

## Course Information

- **Course**: Programming Languages
- **University**: Amirkabir University of Technology
- **Semester**: Fall 2022

Let me know if you have any questions.
