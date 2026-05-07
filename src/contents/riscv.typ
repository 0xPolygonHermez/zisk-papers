ZisK enables developers to write guest programs in standard Rust, compiled through the LLVM toolchain, without modifying their development environment. LLVM's native support for 64-bit RISC-V serves as the compilation target: a Rust program compiled for `riscv64gc-unknown-none-elf` produces a RISC-V ELF binary that ZisK's transpiler can convert and prove directly. ZisK supports the RV64IMACFD instruction set, which corresponds exactly to the `riscv64gc` target architecture used by the Rust toolchain.

== RISC-V Transpilation <sec:transpilation>

The _ZisK transpiler_ converts a RISC-V Executable and Linkable Format (ELF) file into a ZisK executable at load time, before execution or proof generation begins. A ZisK executable comprises:

- *Program ROM*: the transpiled ZisK instruction stream.
- *Initial program counter*: the entry point of the program.
- *Initial data memory*: the data and BSS segments from the ELF, mapped into the ZisK address space (@tbl:address-space).

This executable specifies the initial guest VM state, as discussed in @sec:state.

The translation proceeds in four steps:
+ Load the RISC-V ELF file and extract code and data sections.
+ For each RISC-V instruction or instruction sequence, emit the corresponding ZisK instruction(s). Most RV64IM instructions map one-to-one to a single ZisK instruction; a small number of multi-instruction RISC-V idioms expand to short ZisK sequences.
+ Recognize precompile dispatch sequences ---`ecall` instructions conforming to ZisK's calling convention--- and replace them with the corresponding ZisK precompile opcode (@sec:precompiles).
+ Load the resulting instruction stream into the program ROM and the initial data into the input data region.

=== RV64IMACFD Extension

ZisK provides full zkVM support for the RV64IMACFD instruction set: the 64-bit base integer ISA (I), integer multiplication and division (M), atomics (A), compressed 16-bit instructions (C), single-precision floating-point (F), and double-precision floating-point (D). This is achieved by defining a mapping from every RV64IMACFD instruction to one or more ZisK instructions. The combination of transpiler and ZisK circuit constrains program execution to fully conform to the RISC-V ISA specification for this instruction subset, including integer overflow semantics, atomic read-modify-write semantics, the full set of 16-bit compressed encodings, and IEEE 754 @IEEE754 floating-point arithmetic.

One notable structural difference from standard RISC-V concerns the register file. Standard RISC-V defines 32 general-purpose registers as a separate architectural state; in ZisK they are memory-mapped into the system region of the address space (see @tbl:address-space). As a result, the memory consistency argument covers registers and data memory uniformly ---no separate register-file constraint is needed--- while preserving full compatibility with the RISC-V ABI @RISCVABI.

=== Precompile Integration <sec:precompiles>

ZisK takes advantage of the RISC-V design's inherent support for custom ISA extensions to integrate precompiles. Precompile calls are expressed as standard RISC-V `ecall` instructions following a fixed calling convention: the precompile identifier is placed in register `a7` and addresses for inputs and outputs in the remaining argument registers (`a0`--`a6`). The transpiler recognizes this pattern and replaces each `ecall` with the corresponding ZisK precompile phantom instruction (@sec:isa).

This approach differs from designs that introduce new custom RISC-V opcodes: `ecall` is a standard instruction that requires no toolchain modification. Precompiles can therefore be integrated without forking the compiler, using only the standard Rust inline assembly interface exposed by the guest library.

== Rust Toolchain

The Rust compiler supports 64-bit RISC-V as a first-class target. A Rust `no_std` program compiled for `riscv64gc-unknown-none-elf` produces a RISC-V ELF binary that can be transpiled into a ZisK executable and proved by any ZisK instance. No changes to the Rust compiler or LLVM are required.

Programs that call precompiles do so through Rust function bindings provided by the ZisK guest library. The library uses Rust's `asm!` macro to emit `ecall` instructions with the correct calling convention, hiding all assembly from the application developer. Precompile authors can therefore ship idiomatic Rust APIs ---plain function calls--- without exposing any RISC-V assembly to end users.

=== Standard Library Support

Rust programs using the standard library (`std`) are supported with some limitations. Standard library functionality that traditionally relies on OS system calls ---file I/O, threading, process management--- is not available in the sandboxed guest environment. Functionality that does not require OS support ---heap allocation, string formatting, collections, iterators--- works without modification.

Guest programs interact with the ZisK host exclusively through the interfaces described in @sec:execution_environment: public inputs and outputs are accessed via dedicated ZisK phantom instructions wrapped by the guest library, and hints are consumed from the hint stream on demand.
