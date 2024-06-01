# ocamllvm

This project is a transpiler that converts LLVM bitcode into OCaml source code. While the practical applications of this transpilation may be limited, it offers an exploration into the interoperability between low-level and high-level programming languages.

The primary motivation behind this project was to investigate the feasibility of utilising js_of_ocaml, a compiler from OCaml to JavaScript, on a project with a significant dependency on a C library. By transpiling the C library to OCaml and modifying the project to utilise the generated OCaml code, the project can be transformed into a pure OCaml project, thereby enabling the use of js_of_ocaml.

 Currently, this transpiler is suitable for small to medium-sized C libraries.

 ## Example

 The repository includes scripts that demonstrate the transpilation process using Intel's XED library as an example. These scripts "build" an example binary from the XED library, showcasing the capabilities of the transpiler.

 ## Limitations and Future Work

 It is important to note that the transpiler is still a work in progress and has certain limitations, such as some LLVM opcodes are not yet implemented, which may lead to compatibility issues with certain C libraries. And that some I/O operations are mostly unimplemented, which may restrict the functionality of the transpiled code.

 Despite these limitations, the example binary generated from the XED library has been successfully tested and works as expected. However, it is possible that different versions of Clang may generate slightly different bitcode, which could contain unimplemented or buggy opcodes.

 ## Requirements

The transpiler has been developed and tested with the following specifications:

LLVM 8: The transpiler is compatible with LLVM 8, but minor issues may arise with other versions of the LLVM IR.

OCaml 4.08.0: The transpiler works with OCaml 4.08.0, but it should also be compatible with older versions of OCaml, provided that the necessary adjustments are made to account for renamed standard library functions.
