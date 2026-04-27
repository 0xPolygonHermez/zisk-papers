// TODO: Talk about the extension we support

== RISC-V Transpilation <sec:transpilation>

// TODO: Add more details about the transpilation process, e.g. how the RISC-V instruction set maps to ZisK instructions, how control flow is handled, how precompiles are invoked, etc.

ZisK programs are typically written in Rust and compiled to RISC-V ELF binaries using the standard LLVM/Rust toolchain. The ZisK _transpiler_ converts RISC-V instructions to ZisK instructions at load time, before execution or proof generation.

The translation process works as follows:
+ Load the RISC-V ELF file and extract code and data sections.
+ For each RISC-V instruction, emit the corresponding ZisK instruction(s). Most RV64IM instructions map to a single ZisK instruction; a few multi-step RISC-V idioms expand to short sequences.
+ Precompile calls are expressed as RISC-V `ecall` instructions with a specific calling convention that the transpiler recognises and maps to the appropriate ZisK precompile opcode.
+ The resulting ZisK instruction stream is loaded into the program ROM.

This transpilation layer is what makes ZisK compatible with the Rust ecosystem: developers can use Rust, link against the ZisK system library, and call precompiles through a thin guest library without writing ZisK assembly.
