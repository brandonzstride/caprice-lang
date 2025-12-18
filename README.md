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
dune test
```

The installation is tested on WSL2 for Windows 11. To use the landmarks profiling tool, see the recent [pull request](https://github.com/LexiFi/landmarks/pull/45) for compatibility with ppxlib >= 0.36.0. It may require a local opam pin to use landmarks in caprice-lang until that pull request is merged.

## Developing

Develop in the caprice-lang repository with the following developer tools:

```cmd
opam install ocaml-lsp-server
```

If you are using VS Code, use the OCaml Platform extension.

To write programs in the Caprice language, it's suggested to install the VS Code language extension. Navigate to the `caprice-language-extension` directory and follow the instructions in `README.md` there.
