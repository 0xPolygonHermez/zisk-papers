#import "../lib.typ": definition, remark

The ZisK instruction set architecture (ZisK ISA) specifies the computational model that ZisK proves correct: the execution model, the memory layout, the instruction format, and the full set of operations. Because the ZisK ISA is a _virtual_ ISA --- not targeting any physical hardware --- its design can prioritize properties that simplify zero-knowledge proof generation rather than properties that suit a particular microarchitecture.

The ZisK ISA is designed around two goals. The first is compatibility: ZisK targets the RISC-V ISA so that programs written in standard languages and compiled with existing toolchains can be run without modification. The second goal is efficiency: operations that would be expensive to constrain step-by-step in the main execution circuit ---elliptic-curve arithmetic, hash functions, bulk memory transfers--- are exposed as _precompile instructions_, each handled by a dedicated, optimized sub-circuit. This combination gives the developer accessibility of a standard ISA with the proving performance of a custom one.

#remark(title: "RISC-V to ZisK transpilation")[
  Although programs are written and compiled as standard RISC-V binaries, ZisK does not constrain RISC-V execution directly. Before proving begins, the binary is _transpiled_ off-chain into an equivalent program in the ZisK ISA, and it is the transpiled program that is committed to and executed by the VM. The transpilation is a deterministic, one-to-one rewriting from RISC-V instructions into one or more ZisK instructions; it is performed by a trusted off-chain tool and is not itself part of the proof. We therefore treat the transpiler as part of the trusted computing base.

  // This means that the security guarantees of ZisK rest on the correctness of the transpiler in addition to the proving system: a bug in the transpiler that produces a ZisK program with semantics differing from the original RISC-V binary would not be caught by the proof, even though the proof would still attest to a correct execution of the transpiled program. Accordingly, every statement proved by ZisK in this document (@sec:zisk-statement) is a statement about the _committed ZisK program_ $P$, and the connection to the original RISC-V binary is an explicit, separate assumption (@sec:transpiler-assumption). A full description of the supported RISC-V subset and of the transpilation rules is deferred to the ZisK documentation.
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

A ZisK program $P$ is a finite partial map from 32-bit _instruction addresses_ to _instructions_. An instruction is a fixed-format record; the program ROM stores exactly one such record per address, and the proof system commits to the whole table (@sec:program). Every instruction performs one operation over two 64-bit input operands, producing a 64-bit output and a boolean flag:
$
  (c, "flag") = "op"(a, b), quad a, b, c in [0, 2^(64)), "flag" in {0, 1}.
$
What varies between instructions is how $a$ and $b$ are obtained, where $c$ is stored, and how the program counter advances.

The record has the following fields; boolean fields are packed into a single `flags` word in the committed ROM (@sec:rom-bus).

/ `op` $in [0, 2^8)$: the opcode (@sec:operations, @appendix:opcodes).
/ `a_src` $in$ {`C`, `MEM`, `IMM`, `REG`}: how operand $a$ is obtained: the previous output $c$, an absolute memory address, an immediate, or a register.
/ `a_off`, `a_imm1` $in [0, 2^(32))$: for `REG` the register index; for `MEM` the absolute address; for `IMM` the low and high 32 bits of the immediate.
/ `b_src` $in$ {`C`, `MEM`, `IMM`, `REG`, `IND`}: how operand $b$ is obtained; `IND` is an indirect load at address $a + $ `b_off`.
/ `b_off` $in [-2^(31), 2^(31))$, `b_imm1` $in [0, 2^(32))$: register index, absolute address, low and high immediate bits, or the signed displacement of an indirect load.
/ `ind_w` $in$ {1, 2, 4, 8}: access width in bytes for `IND` loads and `IND` stores.
/ `store` $in$ {`NONE`, `REG`, `MEM`, `IND`}: destination of the stored value.
/ `store_off` $in [-2^(31), 2^(31))$: register index, absolute address, or signed displacement added to $a$ for an `IND` store.
/ `store_pc` $in$ {0, 1}: store the return address `pc + j2` instead of $c$.
/ `set_pc` $in$ {0, 1}: take the next program counter from $c$ (indirect jump).
/ `j1`, `j2` $in [-2^(31), 2^(31))$: jump offsets, `j1` for a taken branch or indirect jump and `j2` for fall-through. For precompile instructions `j1` is instead a static _extended argument_.
/ `m32` $in$ {0, 1}: the operation acts on the low 32 bits of the operands (the `_w` opcodes).
/ `end` $in$ {0, 1}: execution halts after this instruction.

The derived flags `is_external_op` (the operation is delegated to a sub-chip via the Operation Bus) and `is_precompiled` (the operation reads and writes memory itself) are functions of `op`.

The full ZisK instruction set is listed in @appendix:opcodes. The reference implementation is #link("https://github.com/0xPolygonHermez/zisk/blob/v0.16.1/core/src/zisk_ops.rs")[zisk_ops.rs]; the table is a faithful transcription of that file at v0.16.1 and is normative for this document.

=== Operations <sec:operations>

ZisK v0.16.1 has $54$ opcodes plus $6$ internal DMA variants. They fall into the following families, each proved by one instruction-executor chip (@sec:chip-design); the exact semantics of every opcode ---the formula for $c$ and for $"flag"$, including wrap-around, signedness, shift masking and division-by-zero conventions--- is listed in @appendix:opcodes, which is a faithful transcription of `zisk_ops.rs` at v0.16.1 and is normative for this document.

- *Internal* (proved by Main): `flag`, `copyb`, and the invalid-instruction sentinel `halt`.
- *Binary* (Binary and BinaryAdd chips): 64-bit and 32-bit comparisons, minimum/maximum, addition, subtraction and bitwise logic; the comparison opcodes set $"flag"$ to the comparison result.
- *Binary extension* (BinaryExtension chip): logical and arithmetic shifts in 64 and 32 bits, and sign extension from 8, 16 and 32 bits.
- *Arithmetic* (Arith chip): 64-bit and 32-bit multiplication with high and low halves, and division and remainder; division by zero sets $"flag"$.
- *Public output* (Main, bound globally): `pubout` declares public output word $a$ to be $b$ (@sec:statement).
- *Hints* (Main): the three `fcall_*` opcodes drive the host-side hint stream (@sec:inputs_and_hints).
- *Precompiles* (one chip each): Keccak-f, SHA-256 compression, Poseidon2, BLAKE2b, 256-bit addition, 256- and 384-bit modular arithmetic, secp256k1, secp256r1, BN254 and BLS12-381 curve and $FF_(p^2)$ operations, and the DMA bulk-memory operations. These read their operands from and write their results to memory (@sec:precompiles).

=== Phantom Instructions

Most opcodes carry a proof obligation for the operation they perform, discharged by the chip named for it in @appendix:opcodes. A few opcodes are _phantom_: they leave the guest state unchanged apart from the trivial effects $c = 0$ or $c = b$, but may trigger side effects in the host state, such as advancing the hint stream. Phantom instructions appear in the main execution trace but carry no proof obligation beyond the Main chip's own constraints. They are `flag`, `copyb`, and the three `fcall_*` hint instructions; `halt` is the invalid-instruction sentinel and cannot appear in a valid trace.

Precompile dispatch follows a calling convention: the caller writes the parameters to memory, then issues the precompile opcode with $b$ pointing to the parameter block. All parameter passing is done with ordinary instructions; only the precompile instruction itself carries a proof obligation, which is discharged by the corresponding precompile chip together with the memory argument.

=== Program Counter

The program counter `pc` is a 32-bit special-purpose register storing the address of the instruction currently being executed. Its update rule is part of the step semantics (@sec:execution_model): it advances by `j2` unless the instruction sets the flag (branch taken: advance by `j1`) or has `set_pc` set (indirect jump: $c$ + `j1`).

=== Data Memory <sec:memory>

Data memory is a _random access memory (RAM)_ which supports read and write operations. It is separate from the program ROM and is used for mutable state during execution. The ZisK ISA defines a 32-bit byte address space for data memory, but the native unit of access is a 64-bit word (8 bytes). Memory cells are aligned to 8-byte boundaries, so valid addresses are multiples of 8. ZisK supports sub-word accesses (1, 2, or 4 bytes) by decomposing them into aligned 8-byte operations (@sec:memory-chip).

To support execution of programs with different data assumptions and properties within the same architecture, we separate data memory into distinct regions, each with its own access semantics. @tbl:address-space summarises the address space layout and the semantics of each region.

#figure(
  table(
    stroke: 0.5pt,
    columns: (auto, auto, 1fr),
    align: (center + horizon, center + horizon, auto),
    table.header([*Region*], [*Address Range*], [*Semantics*]),
    [Input Data],
    [`[0x4000_0000, 0x8000_0000)`],
    [[1GB] Host-supplied input; read-only. The first word, `0x4000_0000`, is the _free-input port_ through which hints are delivered (@sec:inputs_and_hints).],
    [ROM Data], [`[0x8000_0000, 0x8800_0000)`], [[128MB] Program constants, read-only],
    table.cell(rowspan: 3, align: center + horizon)[Writable RAM],
    [`[0xA000_0000, 0xA001_0000)`], [[64KB] System region: registers, UART and CSR registers],
    [`[0xA001_0000, 0xA002_0000)`],
    [[64KB] Output data: public outputs written during execution; the following 64KB are reserved],
    [`[0xA003_0000, 0xC000_0000)`], [[496MB] Program memory: general-purpose read/write RAM],
  ),
  caption: [Memory layout of the ZisK ISA. The address space is divided into three main regions: input data, ROM data, and writable RAM.],
  kind: table,
) <tbl:address-space>

The 32 general-purpose registers $x_0, dots, x_(31)$ occupy the start of the system region, each spanning 8 bytes, following the RISC-V ABI @RISCVABI. Register $x_0$ is hardwired to zero. From the ISA's perspective, registers are addressed in the same numerical address space as data memory: a load or store targeting the register region behaves exactly as if it targeted RAM, which keeps the ISA uniform and lets compiler-emitted code access registers through ordinary memory operations. Internally, however, ZisK handles the register region separately from the rest of memory for performance reasons; this distinction is invisible to the program but is described in @sec:chip-design.

=== Public Outputs

The guest program can expose up to $32$ values of $64$ bits ($2048$ bits in total) as _public outputs_. During execution the guest writes them to the output-data region of RAM (@tbl:address-space) with ordinary stores; when the program returns to the boot code, the boot code reads the $32$ words back from that region and issues one `pubout` instruction per word (@appendix:opcodes), with $a = i in [0, 32)$ the index and $b$ the word. The `pubout` instructions are what binds the proof's public statement to the execution: the public statement contains exactly these $32$ words (@sec:statement), and nothing else about the input or the memory.

=== Inputs and Hints <sec:inputs_and_hints>

The host state maintains two streams through which the outside world communicates with the guest. The _input stream_ is loaded into the input-data region before execution begins; from the proof's point of view its contents are _not_ public: the public statement (@sec:statement) does not contain them, and a guest that wants to bind its outputs to its inputs must do so itself, e.g. by exposing a hash of the input as a public output. The _hint stream_ provides non-deterministic values at runtime: the guest requests a hint with the `fcall` instructions and then reads the result through the _free-input port_, a load of width $8$ at address `0x4000_0000` that returns the next hint value. The guest must verify any property of a hint it relies on, since ZisK treats hints as unconstrained. Formally, both streams are part of the host state $H$, and the only way their values enter the guest state is through memory reads of the input-data region, whose values the arithmetization leaves free (@sec:memory-relation).

== Execution Model <sec:execution_model>

The execution model defines how the VM transitions between states, what constitutes a valid execution, and which parts of an execution are exposed to the verifier. The W1 version of this document described the single-step map $"Step"$ as a black box "fully determined by the ISA"; here we spell it out, since the soundness statement of @sec:statement quantifies over it.

*Memory as a function.* We model data memory as a total function $"mem" : [0, 2^(32)) -> [0, 2^8)$ from byte addresses to bytes. For a width $w in {1, 2, 4, 8}$ and an address $x$ we write $"mem"[x]_w := sum_(i=0)^(w-1) 2^(8 i) dot "mem"(x + i) in [0, 2^(8 w))$ for the little-endian $w$-byte read, and $"mem"[x]_w <- v$ for the map that stores the $w$ low-order bytes of $v$ at $x, dots, x + w - 1$ and agrees with $"mem"$ elsewhere. Registers are memory: $x_i := "mem"["REG" + 8 i]_8$ for $i in [0, 32)$, where $"REG" =$ `0xA000_0000` is the start of the system region (@tbl:address-space). Register $x_0$ is hardwired to zero at transpilation time (every read of $x_0$ is rewritten to the immediate $0$ and every write to $x_0$ is dropped), so the program never accesses it.

*Guest state.* Since the program ROM is fixed before execution begins, the _guest state_ at step $t$ is
$
  S_t = ("pc"_t, c_t, "mem"_t),
$
comprising the program counter, the previous instruction's output (which the next instruction may consume through the source `C`), and the data memory including the registers. The flag produced by an instruction is consumed only by the same instruction's control-flow rule, so it is not part of the state. The host state $H = ("in"[], "hint"[])$ is supplied externally: $"in"[]$ is loaded into the input-data region before execution, and $"hint"_t$ is the sequence of hint words delivered through the free-input port during step $t$.

*Fetch.* The instruction executed at step $t$ is
$
  iota_t := "Fetch"_P (S_t) := P["pc"_t],
$
the instruction stored in the program ROM at the current program counter. Execution _fails_ if $"pc"_t$ is not in the domain of $P$.

*Operand resolution.* Given a state $S = ("pc", c, "mem")$ and an instruction $iota$, the operands are
$
  a := cases(
    c & "if" iota."a_src" = mono("C"),
    "mem"[iota."a_off"]_8 & "if" iota."a_src" = mono("MEM"),
    iota."a_off" + 2^(32) dot iota."a_imm1" & "if" iota."a_src" = mono("IMM"),
    x_(iota."a_off") & "if" iota."a_src" = mono("REG"),
  ) quad quad
  b := cases(
    c & "if" iota."b_src" = mono("C"),
    "mem"[iota."b_off"]_8 & "if" iota."b_src" = mono("MEM"),
    iota."b_off" + 2^(32) dot iota."b_imm1" & "if" iota."b_src" = mono("IMM"),
    x_(iota."b_off") & "if" iota."b_src" = mono("REG"),
    "mem"[(a + iota."b_off") mod 2^(32)]_(iota."ind_w") & "if" iota."b_src" = mono("IND"),
  )
$
where in the `IND` case the requirement $a < 2^(32)$ is part of the well-formedness of the step (the arithmetization enforces $a$'s high word to be zero whenever an indirect address is formed). Reads of the free-input port ---address `0x4000_0000` with width $8$--- return the next hint word $"hint"_t$ instead of the memory contents; this is the only non-deterministic input to a step.

*Operation.* $(c', "flag") := iota."op"(a, b)$ as specified in @appendix:opcodes. For precompile opcodes the operation additionally has a _memory effect_: it reads its parameter block from $"mem"$ at addresses derived from $b$ and writes its results back, as described in @appendix:opcodes and in detail in @sec:precompiles. We write $"mem"^"op" := "Eff"_(iota."op")("mem", a, b, iota."j1")$ for the memory after the precompile's effect (with $"Eff"$ the identity for all non-precompile opcodes); the fourth argument is the extended static argument that some DMA opcodes take from the `j1` field.

*Store.* The stored value is $v := (("pc" + iota."j2") mod 2^(32))$ if $iota."store_pc" = 1$ and $v := c'$ otherwise, and
$
  "mem"' := cases(
    "mem"^"op" & "if" iota."store" = mono("NONE"),
    "mem"^"op" ["REG" + 8 dot iota."store_off"]_8 <- v & "if" iota."store" = mono("REG"),
    "mem"^"op" [iota."store_off"]_8 <- v & "if" iota."store" = mono("MEM"),
    "mem"^"op" [(a + iota."store_off") mod 2^(32)]_(iota."ind_w") <- v & "if" iota."store" = mono("IND").
  )
$

*Control flow.* The next program counter is
$
  "pc"' := cases(
    (c' + iota."j1") mod 2^(32) & "if" iota."set_pc" = 1,
    ("pc" + iota."j1") mod 2^(32) & "if" iota."set_pc" = 0 and "flag" = 1,
    ("pc" + iota."j2") mod 2^(32) & "if" iota."set_pc" = 0 and "flag" = 0,
  )
$
and a valid instruction never has both $iota."set_pc" = 1$ and $"flag" = 1$ (the arithmetization enforces $"flag" dot "set_pc" = 0$). Note that `j1` doubles as the extended argument of precompile instructions; for those, $"flag" = 0$ and $"set_pc" = 0$, so `j1` never reaches the program counter.

#definition(title: "ZisK Step Predicate")[
  Fix a program $P$. The _step predicate_ $"Step"_P (S, iota, h, S')$ holds for states $S = ("pc", c, "mem")$, $S' = ("pc"', c', "mem"')$, instruction $iota$, and hint sequence $h$ if and only if $iota = P["pc"]$ and, with $a, b, c', "flag", "mem"', "pc"'$ computed from $(S, iota, h)$ by the operand-resolution, operation, store and control-flow rules above, the components of $S'$ are exactly those values. We write $"Step"_P (S, h) = S'$ for the (unique) $S'$ satisfying the predicate, when it exists.
] <def:step>

The predicate is total on well-formed inputs and deterministic given the hints: for every $S$ with $"pc" in "dom"(P)$ and every $h$ there is exactly one $S'$, and $S'$ does not depend on $h$ unless the instruction reads the free-input port. This is what makes ZisK's execution a function of $(P, "in", "hint")$.

*Initial state.* Execution begins at the boot address $"pc"_"BOOT" =$ `0x1000` with memory initialised from the program binary and the input:
$
  S_0 = ("pc"_"BOOT", 0, "mem"_0), quad "mem"_0 = "ROMDATA"_P union "in"[] union 0,
$
i.e. the ROM-data region holds the program constants, the input-data region holds the host-supplied input stream (word-aligned, preceded by the 8-byte free-input port), and every other address ---including all registers--- holds zero.

*Terminal condition.* Every ZisK program contains, at address $"pc"_"END" =$ `0x1004`, the unique instruction with the `end` field set. A $T$-step execution is _successful_ if $"pc"_T = "pc"_"END"$ and $"Step"_P$ holds at every step $t < T$; the boot code guarantees that $"pc"_"END"$ is reached with $c_T = 0$. Execution _fails_ if a step violates the ISA's invariants ---undefined program counter, out-of-range memory access, or the `halt` sentinel--- or if the program counter never reaches $"pc"_"END"$. Only successful executions are provable.

*Public outputs.* The public outputs are not a separate component of the state. The guest writes them to the output-data region of RAM with ordinary stores, and the boot code, after the guest returns, reads the $32$ words of that region and issues one `pubout` instruction per word (@appendix:opcodes). We write
$
  "out"_i (S_0, dots, S_T) := b_t quad "where" t "is the unique step with" iota_t."op" = mono("pubout") "and" a_t = i, quad i in [0, 32),
$
for the $i$-th public output of the execution; the boot code executes exactly one `pubout` per index. These $32$ words are the only execution-dependent data in the proof's public statement (@sec:statement).
