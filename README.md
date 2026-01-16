# caprice-lang

This repo implements the Caprice programming language.

Caprice is a semantically typed functional language with types as values.

## Installation

Caprice is built with OCaml 5.4.0.

Via opam, install OCaml 5.4.0 and then install the dependencies. Answer y/yes to all questions:

```cmd
opam switch create 5.4.0
opam install .
```

Then, build the repository with dune:

```cmd
dune build
make test
```

The installation is tested on WSL2 for Windows 11. To use the landmarks profiling tool, see the recent [pull request](https://github.com/LexiFi/landmarks/pull/45) for compatibility with ppxlib >= 0.36.0. It may require a local opam pin to use landmarks in caprice-lang until that pull request is merged.

## Developing

Develop in the caprice-lang repository with the following developer tools:

```cmd
opam install ocaml-lsp-server
```

If you are using VS Code, use the OCaml Platform extension.

To write programs in the Caprice language, it's suggested to install the VS Code language extension. Navigate to the `caprice-language-extension` directory and follow the instructions in `README.md` there.

## Programming with Caprice

Write Caprice programs in `.caprice` files. With the project built, you can run the type checker with the `./typecheck.exe` executable. For example,

```cmd
./typecheck.exe filename.caprice -s
```

type checks `filename.caprice` by type splaying (`-s`) to encourage termination. The output may contain one of several messages:
- `Exhausted`: every possible program path was run and exhausted, and **the program is well-typed**.
- `Found error`: the type checker found some type refutation, so **the program is ill-typed**.
- `Exhausted pruned tree`: many program paths were run, and the tree was exhausted up to some depth without error, but the program may still be ill-typed.
- `Timeout`: no error was found within the allowed time, so the program may still be ill-typed.
- `Unknown`: the SMT solver failed to return an answer quickly, so some program path was skipped, but no error was found otherwise; the program may still be ill-typed.
