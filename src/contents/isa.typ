#import "../lib.typ": definition, remark

The ZisK instruction set architecture (ZisK ISA) specifies the computational model that ZisK proves correct: the execution model, the memory layout, the instruction format, and the full set of operations. Because the ZisK ISA is a _virtual_ ISA --- not targeting any physical hardware --- its design can prioritize properties that simplify zero-knowledge proof generation rather than properties that suit a particular microarchitecture.

The ZisK ISA is designed around two goals. The first is compatibility: ZisK targets the RISC-V ISA so that programs written in standard languages and compiled with existing toolchains can be run without modification. The second goal is efficiency: operations that would be expensive to constrain step-by-step in the main execution circuit ---elliptic-curve arithmetic, hash functions, bulk memory transfers--- are exposed as _precompile instructions_, each handled by a dedicated, optimized sub-circuit. This combination gives the developer accessibility of a standard ISA with the proving performance of a custom one.

#remark(title: "RISC-V to ZisK transpilation")[
  Although programs are written and compiled as standard RISC-V binaries, ZisK does not constrain RISC-V execution directly. Before proving begins, the binary is _transpiled_ off-chain into an equivalent program in the ZisK ISA, and it is the transpiled program that is committed to and executed by the VM. The transpilation is a deterministic, one-to-one rewriting from RISC-V instructions into one or more ZisK instructions; it is performed by a trusted off-chain tool and is not itself part of the proof. We therefore treat the transpiler as part of the trusted computing base.

  // This means that the security guarantees of ZisK rest on the correctness of the transpiler in addition to the proving system: a bug in the transpiler that produces a ZisK program with semantics differing from the original RISC-V binary would not be caught by the proof, even though the proof would still attest to a correct execution of the transpiled program.

  // A full description of the supported RISC-V subset, the transpilation rules, and the precompile-call ABI is deferred to a later revision of this document.
]

The rest of this section describes the execution environment (@sec:execution_environment), the machine state (@sec:state), and the formal execution model (@sec:execution_model).

== Execution Environment <sec:execution_environment>

Programs in ZisK are executed inside a _virtual machine_ (VM). The VM is a _state machine_: execution proceeds as a sequence of discrete steps, each step transforming the current _guest state_ according to one instruction. The VM is hosted on a physical machine, called the _host_, that maintains an external _host state_ separate from the guest. The ZisK ISA provides specific interfaces through which the guest program can read from and write to the host state.

This host/guest separation is central to ZisK's trust model. The guest program runs in a fully deterministic, sandboxed environment: every value it operates on is either derived from the initial program ROM (@sec:program), loaded from memory, or explicitly received from the host through a typed channel. The host can supply:
- *Public Inputs*. Values known to both prover and verifier, written into the input data region at the start of execution and read-only thereafter.
- *Private Inputs (Hints)*. Non-deterministic values provided by the host at runtime. The guest may request a hint and use its value, but must verify any properties it relies on ---ZisK treats hints as unconstrained. A hint that is never verified proves nothing.

The key property of this model is that _everything the guest touches is constrained by the VM's arithmetization_. Memory accesses are constrained by the memory argument; program code is validated by the ROM bus on every fetch; and public outputs become explicit proof data. The host state, by contrast, lies outside and is trusted by convention.

== State <sec:state>

As defined before, the VM execution state is everything that changes from one step to the next. It is divided into the _guest state_ ---manipulated by the program--- and the _host state_ ---maintained externally and supplied before or during execution. The guest state comprises the program ROM (read-only), the program counter `pc`, data memory (read/write), and the public outputs. The host state comprises the input stream and the hint stream.

=== Program ROM <sec:program>

ZisK can execute any program compiled to its ISA. A program consists of two parts:
- *The Program Code*. The program code maps 32-bit instruction addresses to ZisK instructions. It is loaded into the VM before execution begins.
- *The ROM Data*. The ROM data is an immutable data segment holding program constants (e.g., string literals, lookup tables, and static data embedded in the binary). It occupies a dedicated region of the address space and can be read but never written by the program.

Both parts are determined entirely by the program binary: they are identical across every execution of that program, regardless of the inputs provided. Once the program is fixed, neither the code nor the ROM data can change --- no instruction can modify them and they play no role in the per-step state transitions of the machine. This separation of code from mutable data is the classical _Harvard architecture_: code and data live in distinct address spaces and are governed by different access rules.

From the proving system's perspective, the two parts are committed to and validated by distinct mechanisms. The program code is organised as a fixed table of instructions indexed by their addresses. Before any execution begins, this table is hashed into a _program commitment_ that is included in the verifier's context. At every step, the main circuit performs a table lookup against this committed table ---retrieving the instruction at the current program counter and verifying it belongs to the ROM. No instruction can be substituted or forged without invalidating the commitment.

The ROM data is validated through a different mechanism. Rather than a separate lookup, it is treated as a region of _immutable memory_ within a dedicated address space (@sec:memory). At initialization, the ROM data region is written once to establish its contents; thereafter only reads are permitted. From the running program's point of view, reads from ROM data are indistinguishable from reads from writable RAM --- the immutability is a property enforced by the arithmetization, not by the ISA.

=== Instruction Format <subsec:instruction_format>

ZisK instructions are specified by:
- An _opcode_ determining the operation to perform.
- A _source_ for a first input ($a$), specifying how to obtain its value.
- A _source_ for a second input ($b$), specifying how to obtain its value.
- A _store_ for the output ($c$), specifying where to write the result.

Each instruction performs an operation over two input operands, producing an output and a _flag_:
$
  (c, "flag") = "op"(a, b)
$
where $a, b, c in [0, 2^(64))$ and $"flag" in {0, 1}$. In essence, each instruction is a single execution step that transforms two 64-bit inputs into a 64-bit output and a boolean flag. The full ZisK instruction set is described in detail in #link("https://github.com/0xPolygonHermez/zisk/blob/main/core/src/zisk_ops.rs")[zisk_ops.rs].

=== Phantom Instructions

The opcode determines the operation performed by the instruction. Most instructions correspond to a single provable opcode and generate a proof obligation for that operation. Some instructions, however, are _phantom instructions_: they leave the guest state unchanged --- acting as no-ops from the VM's perspective --- but may trigger side effects in the host state, such as advancing the input or hint streams or emitting debug information. Phantom instructions appear in the main execution trace but carry no proof obligation of their own.

Two notable cases:
- *Precompile dispatch*: Instructions that implement the calling convention for invoking precompiles ---passing parameters, triggering the call, and retrieving results. What gets proven is the precompile computation itself.

- *Halting*: This instruction terminates the emulator immediately with an error condition. Its opcode cannot appear in a valid execution trace ---if it is ever reached, proof generation fails. It is present in the ISA as a sentinel for invalid or unreachable code paths.

// === Input Source

// The source of an input register determines how its value is obtained before the operation executes:
// #table(
//   stroke: 0.5pt,
//   columns: (auto, auto, auto),
//   align: (center, center, auto),
//   table.header([*Source*], [*Applies to*], [*Description*]),
//   [`SRC_C`], [$a$, $b$], [Previous value of the $c$ register],
//   [`SRC_IMM`], [$a$, $b$], [Immediate (constant) value encoded in the instruction],
//   [`SRC_REG`], [$a$, $b$], [Value read from a constant register index],
//   [`SRC_MEM`], [$a$, $b$], [Value read from memory at a fixed address],
//   // [`SRC_STEP`], [$a$], [Current execution step counter],
//   [`SRC_IND`], [$b$], [Value read from memory at indirect address],
// )

// ==== Output Store

// The store of the output register determines how its value is persisted after the operation executes:

// #table(
//   stroke: 0.5pt,
//   columns: (auto, 1fr),
//   table.header([*Store*], [*Description*]),
//   [`STORE_NONE`], [Value is discarded],
//   [`STORE_REG`], [Value is stored at a constant register index],
//   [`STORE_MEM`], [Value is stored to memory at a fixed address],
//   [`STORE_IND`], [Value is stored to memory at indirect address],
// )

=== Program Counter

The program counter `pc`, which is seen as a special purpose register, stores the address of the instruction currently being executed. After each instruction, `pc` advances to the next instruction address unless the instruction explicitly modifies control flow (jumps, branches).

=== Data Memory <sec:memory>

Data memory is a _random access memory (RAM)_ which supports read and write operations. It is separate from the program ROM and is used for mutable state during execution. The ZisK ISA defines a 32-bit byte address space for data memory, but the native unit of access is a 64-bit word (8 bytes). Memory cells are aligned to 8-byte boundaries, so valid addresses are multiples of 8. ZisK supports sub-word accesses (1, 2, or 4 bytes) by decomposing them into aligned 8-byte operations (@sec:memory-chip).

To support execution of programs with different data assumptions and properties within the same architecture, we separate data memory into distinct regions, each with its own access semantics. @tbl:address-space summarises the address space layout and the semantics of each region.

#figure(
  table(
    stroke: 0.5pt,
    columns: (auto, auto, 1fr),
    align: (center + horizon, center + horizon, auto),
    table.header([*Region*], [*Address Range*], [*Semantics*]),
    [Input Data], [`[0x4000_0000, 0x8000_0000)`], [[1GB] Written once at initialization, read-only thereafter],
    [ROM Data], [`[0x8000_0000, 0x8800_0000)`], [[128MB] Program constants, read-only],
    table.cell(rowspan: 3, align: center + horizon)[Writable RAM],
    [`[0xA000_0000, 0xA001_0000)`], [[64KB] System region: registers, UART and CSR registers],
    [`[0xA001_0000, 0xA003_0000)`], [[128KB] Output data: public outputs written during execution],
    [`[0xA003_0000, 0xC000_0000)`], [[496MB] Program memory: general-purpose read/write RAM],
  ),
  caption: [Memory layout of the ZisK ISA. The address space is divided into three main regions: input data, ROM data, and writable RAM.],
  kind: table,
) <tbl:address-space>

The 32 general-purpose registers $x_0, dots, x_(31)$ occupy the start of the system region, each spanning 8 bytes, following the RISC-V ABI @RISCVABI. Register $x_0$ is hardwired to zero. From the ISA's perspective, registers are addressed in the same numerical address space as data memory: a load or store targeting the register region behaves exactly as if it targeted RAM, which keeps the ISA uniform and lets compiler-emitted code access registers through ordinary memory operations. Internally, however, ZisK handles the register region separately from the rest of memory for performance reasons; this distinction is invisible to the program but is described in @sec:chip-design.

=== Public Outputs

The guest program can explicitly expose values as public outputs. The values are written internally by a dedicated instruction and become part of the proof's public data that allow the verifier to check that the program produced specific results.
// ZisK handles up to $32$ public $64$-bit output values, i.e., $2048$ bits in total.

=== Inputs and Hints <sec:inputs_and_hints>

The host state maintains two streams through which the outside world communicates with the guest. The _input stream_ is a queue of public data loaded before execution begins. The _hint stream_ provides non-deterministic values at runtime ---the guest may request a hint and act on its value, but must verify any property it relies on, since ZisK treats hints as unconstrained. Both streams are consumed by copying data into guest memory via explicit instructions; any value received from the host is untrusted until the guest has verified it.

== Execution Model <sec:execution_model>

The execution model defines how the VM transitions between states, what constitutes a valid execution, and how the prover commits to the result. Since the program ROM is fixed before execution begins, the _guest state_ at step $t$ is defined as:
$
  S_t = ("pc"_t, c_t, "flag"_t, "mem"_(t)[])
$
comprising the program counter, the previous instruction's output and flag, and the data memory. The host state $H = ("in[]", "hint[]")$ is supplied externally. Execution proceeds in discrete steps according to the following rules:

*Initial state.* Execution begins at a designated boot address with memory initialised from the program binary: the ROM data region is populated with program constants, the input data region is loaded from the public host-supplied input stream, and all writable memory is zeroed. Formally:
$
  S_0 = ("pc"_0, 0, 0, "mem"_0 [])
$
where $"pc"_0$ is set to a designated boot address and $"mem"_0 []$ reflects the pre-loaded memory state.

*Transition function.* At each step, the VM fetches the instruction at the current program counter from the committed ROM, executes it, and advances the guest state. The host supplies hint values on demand. The single-step transition is:
$
  S_(t+1) = "Step"(S_t, "hint"_(t)[])
$
where $"hint"_(t)[]$ are the hint values supplied by the host at step $t$. The function $"Step"$ is fully determined by the ZisK ISA: it decodes the instruction at $"pc"_t$, evaluates the operation, updates $"mem"_(t+1)[]$, and sets $"pc"_(t+1)$ according to the instruction's control-flow semantics.

*Terminal condition.* A $T$-step execution is _successful_ if every transition is valid and the final program counter reaches a designated exit address.
Execution _fails_ if any step violates the ISA's invariants ---invalid opcode, out-of-bounds memory access, or an explicit halt instruction--- or if the program counter fails to reach the exit address at the end of execution.

*Public outputs.* The public outputs are not a separate component of the state but a designated region of writable RAM (see @tbl:address-space). The guest writes to this region through ordinary memory-store instructions during execution, and once the run terminates successfully, the contents of that region are extracted from $"mem"_T []$ and exposed as the proof's public output. In other words, the output buffer is filled in place over the course of execution rather than being accumulated as a separate stream at every step.
