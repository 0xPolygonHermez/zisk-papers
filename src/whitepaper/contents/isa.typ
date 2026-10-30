#import "../../shared/lib.typ": definition, remark

The ZisK instruction set architecture (ZisK ISA) specifies the computational model that ZisK proves correct: the execution model, the memory layout, the instruction format, and the full set of operations. Because the ZisK ISA is a _virtual_ ISA---not targeting any physical hardware---its design can prioritize properties that simplify zero-knowledge proof generation rather than properties that suit a particular microarchitecture.

The ZisK ISA is designed around two goals. The first is compatibility: ZisK targets the RISC-V ISA so that programs written in standard languages and compiled with existing toolchains can be run without modification. The second goal is efficiency: operations that would be expensive to constrain step-by-step in the Main chip ---elliptic-curve arithmetic, hash functions, bulk memory transfers--- are exposed as _precompile instructions_, each handled by a dedicated, optimized chip. This combination gives the developer the accessibility of a standard ISA together with the proving performance of a custom one.

The rest of this section describes how RISC-V programs are translated into the ZisK ISA (@sec:transpilation), the execution environment (@sec:execution_environment), the machine state and instruction format (@sec:state), and the formal execution model (@sec:execution_model). The complete list of operations is given in @appendix:opcodes.

== RISC-V Support and Transpilation <sec:transpilation>

Although programs are written and compiled as standard RISC-V binaries, ZisK does not constrain RISC-V execution directly. Before proving begins, the binary is _transpiled_ off-chain into an equivalent program in the ZisK ISA, and it is the transpiled program that is committed to and executed by the VM. The transpilation is a deterministic rewriting of every RISC-V instruction into one or more ZisK instructions; it is performed by a trusted off-chain tool and is not itself part of the proof. We therefore treat the transpiler as part of the trusted computing base: every statement proved by ZisK is a statement about the committed ZisK program, and its connection to the original RISC-V binary rests on the correctness of the transpiler.

ZisK accepts 64-bit RISC-V binaries (RV64) using the following extensions:
- *RV64I*, the base integer instruction set. `fence` and `fence.i` are transpiled to no-ops, since the VM is single-threaded and has no caches; `ebreak` is also a no-op.
- *M*, all thirteen multiplication and division instructions, each mapped to a single ZisK opcode.
- *A*, the atomic instructions. Since execution is single-threaded, `lr` is a plain load, `sc` always succeeds, and every `amo` instruction is expanded into a load, the operation, and a store.
- *C*, the compressed instructions, which are transpiled exactly like their uncompressed equivalents.
- *Zicsr*, the control and status register instructions. Ordinary CSRs are plain words of the system region of memory (@tbl:address-space); a range of CSR numbers is reserved as the ports through which programs invoke precompiles and request hints (@sec:precompile-calls).
- *F* and *D*, the single- and double-precision floating-point instructions, which are emulated in software: floating-point loads and stores access a memory-resident floating-point register file, and every other floating-point instruction is transpiled into a call to a floating-point library that is embedded in every ZisK program.

`ecall` jumps to a trap handler that only implements the exit system call; the guest runtime uses it exclusively to terminate (@sec:execution_model). Any encoding outside these extensions is transpiled to the `halt` instruction, which cannot appear in a valid execution (@sec:operations), so a program that reaches an unsupported instruction cannot be proved.

When a RISC-V instruction at address $A$ expands into $k > 1$ ZisK instructions, the first is placed at $A$ and the others at intermediate addresses reserved for this purpose, and the last of them jumps to the address of the next RISC-V instruction. A RISC-V instruction therefore takes one or more ZisK steps. @tbl:transpilation shows representative translations, using the instruction fields of @subsec:instruction_format.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (1.1fr, 3fr),
      align: (left, left),
      table.header([*RISC-V*], [*ZisK instruction(s)*]),
      [`add rd, rs1, rs2`],
      [`add` with $a$ = `REG rs1`, $b$ = `REG rs2`, store `REG rd`; `j1` = `j2` = $4$. If `rs1` or `rs2` is `x0`, a `copyb` of the other register instead.],

      [`lw rd, imm(rs1)`],
      [`signextend_w` with $a$ = `REG rs1`, $b$ = `IND` with displacement `imm` and width $4$, store `REG rd`. `ld`, `lbu`, `lhu`, `lwu` use `copyb` instead, with the corresponding width.],

      [`sd rs2, imm(rs1)`],
      [`copyb` with $a$ = `REG rs1`, $b$ = `REG rs2`, store `IND` with displacement `imm` and width $8$.],

      [`beq rs1, rs2, off`],
      [`eq` with $a$ = `REG rs1`, $b$ = `REG rs2`, no store, `j1` = `off`, `j2` = $4$. `bne` swaps the offsets; `blt`/`bge` and `bltu`/`bgeu` use `lt` and `ltu`.],

      [`jal rd, off`],
      [`flag` with `store_pc`, store `REG rd`, `j1` = `off`, `j2` = the size of the RISC-V instruction: jumps to `pc + off` and stores the return address `pc + j2`.],

      [`jalr rd, imm(rs1)`],
      [`and` with $a$ = `IMM` $2^(64) - 2$, $b$ = `REG rs1`, `set_pc`, `store_pc`, store `REG rd`, `j1` = `imm`: jumps to $("rs1" and not 1) + "imm"$. A second instruction is needed when `imm` is not a multiple of $4$.],

      [`mulh rd, rs1, rs2`], [`mulh` with $a$ = `REG rs1`, $b$ = `REG rs2`, store `REG rd`.],
      [`amoadd.w rd, rs2, (rs1)`],
      [three instructions: `signextend_w` of the word at `rs1` into `rd`; `add_w` of the previous result and `rs2`; `copyb` of the previous result into the word at `rs1`.],

      [`csrs 0x800, rs1`],
      [`keccak` with $a$ = `IMM` $0$, $b$ = `REG rs1` (the address of the state), no store (@sec:precompile-calls).],
    )
  },
  caption: [Representative RISC-V to ZisK translations. Unless stated otherwise, `j2` advances to the next RISC-V instruction.],
  kind: table,
) <tbl:transpilation>

== Execution Environment <sec:execution_environment>

Programs in ZisK are executed inside a _virtual machine_ (VM). The VM is a _state machine_: execution proceeds as a sequence of discrete steps, each step transforming the current _guest state_ according to one instruction. The VM is hosted on a physical machine, called the _host_, that maintains an external _host state_ separate from the guest. The ZisK ISA provides specific interfaces through which the guest program can read from and write to the host state.

This host/guest separation is central to ZisK's trust model. The guest program runs in a fully deterministic, sandboxed environment: every value it operates on is either derived from the program (@sec:program), loaded from memory, or explicitly received from the host through a typed channel. The host can supply:
- *Inputs*. A byte string written into the input data region before execution starts and read-only thereafter.
- *Hints*. Non-deterministic values provided by the host at runtime, on the guest's request. The guest may use them, but must verify any properties it relies on.

Neither inputs nor hints are part of what the verifier sees: from the proof's point of view both are prover-chosen, and ZisK treats them as unconstrained. A guest that wants its result to be bound to its input must do so itself, for instance by exposing a hash of the input as a public output. The only data the verifier sees about an execution are the program commitment and the public outputs (@sec:zisk-statement).

The key property of this model is that _everything the guest touches is constrained by the VM's arithmetization_. Memory accesses are constrained by the memory argument; program code is validated by the ROM Bus on every fetch; and public outputs become explicit proof data. The host state, by contrast, lies outside the proof.

== State <sec:state>

The VM execution state is everything that changes from one step to the next. It is divided into the _guest state_ ---manipulated by the program--- and the _host state_ ---maintained externally and supplied before or during execution. The guest state comprises the program counter `pc`, the output $c$ of the previous instruction, the registers, and the data memory; the program itself is fixed. The host state comprises the input and the hint stream.

=== Program ROM <sec:program>

ZisK can execute any program compiled to its ISA. A program consists of two parts:
- *The Program Code*. The program code maps 32-bit instruction addresses to ZisK instructions. It is loaded into the VM before execution begins.
- *The ROM Data*. The ROM data is an immutable data segment holding program constants (e.g., string literals, lookup tables, and static data embedded in the binary). It occupies a dedicated region of the address space, is written only by the boot code, whose stores leave it unchanged (@sec:execution_model), and is otherwise only read.

Both parts are determined entirely by the program binary: they are identical across every execution of that program, regardless of the inputs provided. Once the program is fixed, neither the code nor the ROM data can change---no instruction can modify them and they play no role in the per-step state transitions of the machine. This separation of code from mutable data is the classical _Harvard architecture_: code and data live in distinct address spaces and are governed by different access rules.

From the proving system's perspective, the two parts are committed to and validated by distinct mechanisms. The program code is organized as a fixed table of instructions indexed by their addresses. Before any execution begins, this table is hashed into a _program commitment_ that is part of the public statement of every proof. At every step, the Main chip performs a table lookup against this committed table ---retrieving the instruction at the current program counter and verifying it belongs to the ROM. No instruction can be substituted or forged without invalidating the commitment.

The ROM data is validated through a different mechanism. Rather than a separate lookup, it is treated as a region of _immutable memory_ within a dedicated address space (@sec:memory). Every ZisK program starts with a _boot code_, generated by the transpiler, that writes the contents of the binary's data sections ---read-only and writable--- into memory with ordinary store instructions, one 8-byte word at a time. Since these instructions, including their immediate values, are part of the committed program code, the initial contents of data memory are bound to the program commitment as well. The ROM data region is written once by the boot code; thereafter only reads are permitted. From the running program's point of view, reads from ROM data are indistinguishable from reads from writable RAM---the immutability is a property enforced by the arithmetization, not by the ISA. The arithmetization groups the accesses to each read-only word but does not order them in time, so the execution model treats the ROM data as present from the start: every word holds, from the first step, the value that its boot-code store writes, or zero if it has none, and that store leaves the memory unchanged (@sec:execution_model).

=== Instruction Format <subsec:instruction_format>

A ZisK program $P$ is a finite partial map from 32-bit _instruction addresses_ to _instructions_. Every instruction performs one operation over two input operands, producing an output and a _flag_:
$
  (c, "flag") = "op"(a, b), quad a, b, c in [0, 2^(64)), "flag" in {0, 1}.
$
In essence, each instruction is a single execution step that transforms two 64-bit inputs into a 64-bit output and a boolean flag. What varies between instructions is how $a$ and $b$ are obtained, where $c$ is stored, and how the program counter advances. An instruction is a record with the following fields:

- / `op` $in [0, 2^8)$: the opcode, determining the operation (@sec:operations).
- / `a_src` $in$ {`C`, `REG`, `MEM`, `IMM`}: how $a$ is obtained ---the output $c$ of the previous instruction, a register, the 8-byte word at a fixed address, or an immediate.
- / `b_src` $in$ {`C`, `REG`, `MEM`, `IMM`, `IND`}: how $b$ is obtained; `IND` is an _indirect_ load at address $a$ plus a displacement.
- / `a_off`, `a_imm1` $in [0, 2^(32))$: the register index for `REG`, the address for `MEM`, and the low and high halves of the immediate for `IMM`.
- / `b_off`, `b_imm1`: as for $a$; for `IND`, `b_off` $in [-2^(31), 2^(31))$ is the signed displacement.
- / `ind_w` $in {1, 2, 4, 8}$: the width in bytes of an `IND` load or store.
- / `store` $in$ {`NONE`, `REG`, `MEM`, `IND`}: where the result is written ---nowhere, a register, the 8-byte word at a fixed address, or `ind_w` bytes at address $a$ plus a displacement.
- / `store_off` $in [0, 2^(32))$, or $in [-2^(31), 2^(31))$ for `IND`: the register index, the address, or the signed displacement of the store.
- / `store_pc` $in {0, 1}$: store the return address `pc + j2` instead of $c$.
- / `set_pc` $in {0, 1}$: take the next program counter from $c$ (indirect jump).
- / `j1`, `j2` $in [-2^(31), 2^(31))$: jump offsets, `j1` for a taken branch or an indirect jump and `j2` otherwise. Precompile instructions reuse `j1` as a static _extended argument_ of the operation.
- / `m32` $in {0, 1}$: the operation is a 32-bit operation and only reads the low 32 bits of its operands.
- / `end` $in {0, 1}$: marks the exit instruction at $"pc"_"END"$ and the `halt` sentinels (@sec:execution_model); it is not part of the ROM Bus message and plays no role in the step semantics.

Two further flags are functions of `op`: `is_external_op`, which states that the operation is proved by a chip other than Main (@sec:chip-design), and `is_precompiled`, which states that the operation reads and writes memory itself (@sec:precompiles).

Not every record of this shape is an instruction that the Main chip executes as specified, and the programs that ZisK proves are restricted accordingly.

#definition(title: "Valid Program")[
  A program $P$ is _valid_ if every one of its instructions has its fields in the domains above, takes `m32`, `is_external_op` and `is_precompiled` from its opcode, uses only register indices in $[1, 31]$ for the sources and the store of kind `REG`, and sets `set_pc` only for an opcode whose flag is always zero.
] <def:valid-program>

Every program produced by the transpiler is valid. Validity is not checked by the arithmetization: the Rom chip proves whatever table is committed (@sec:rom-bus), and a table that is not the ROM table of a valid program can be committed as well. A verifier therefore accepts a proof only for the program commitment of the valid program it expects.

=== Operations <sec:operations>

ZisK defines a set of opcodes, listed with their exact semantics in @appendix:opcodes, which transcribes the reference implementation#footnote[It can be found at #link("https://github.com/0xPolygonHermez/zisk/blob/v0.16.1/core/src/zisk_ops.rs")[https://github.com/0xPolygonHermez/zisk/blob/v0.16.1/core/src/zisk_ops.rs].]. They fall into the following families, each proved by one or more chips of @sec:chip-design:

- *Internal* (proved by Main): `flag` (sets the flag, used for unconditional jumps), `copyb` (copies $b$), and the `halt` sentinel.
- *Binary* (Binary and BinaryAdd): 64- and 32-bit comparisons, minimum and maximum, addition, subtraction and bitwise logic. Comparisons also return their result in the flag, which is how conditional branches are implemented.
- *Binary extension* (BinaryExtension): 64- and 32-bit shifts and sign extensions.
- *Arithmetic* (Arith): 64- and 32-bit multiplication (low and high halves), division and remainder.
- *Public output* (Main, bound to the public statement): `pubout` (@sec:public-outputs).
- *Hints* (Main): `fcall_param`, `fcall` and `fcall_get` (@sec:inputs_and_hints).
- *Precompiles* (one chip each, see @tbl:chip-inventory): the Keccak-f, SHA-256, Poseidon2 and BLAKE2b permutations or compression functions; 256-bit addition; 256- and 384-bit modular arithmetic; secp256k1, secp256r1, BN254 and BLS12-381 elliptic-curve addition and doubling; arithmetic in the quadratic extensions of the BN254 and BLS12-381 base fields; and the DMA bulk-memory operations (copy, compare, fill, and copy from the hint stream).

=== Phantom Instructions <sec:phantom>

Most instructions carry a proof obligation for the operation they perform, discharged by the chip in charge of their opcode. Some instructions, however, are _phantom_: their only effect on the guest state is the trivial one of `copyb`, $c = b$ ---for `fcall_get`, $b$ is the hint word read from the free-input port--- but they trigger side effects in the host state. These are the hint instructions `fcall_param`, `fcall` and `fcall_get` (@sec:inputs_and_hints): they appear in the main execution trace, where the Main chip proves them as plain `copyb` steps, but the host computation they trigger is not proved.

The `halt` instruction plays the opposite role: it is the sentinel into which invalid or unsupported code is transpiled (@sec:transpilation). The Main chip does not accept it, so it cannot appear in a valid execution trace, and a program that reaches it cannot be proved.

=== Program Counter

The program counter `pc`, which is seen as a special purpose register, stores the address of the instruction currently being executed. After each instruction, `pc` advances by `j2`, unless the instruction raises the flag (a taken branch, which advances by `j1`) or sets `set_pc` (an indirect jump to $c$ + `j1`). The exact rule is part of the step semantics of @sec:execution_model.

=== Registers <sec:isa-registers>

The guest has 32 general-purpose 64-bit registers $x_0, dots, x_(31)$, following the RISC-V ABI @RISCVABI, accessed through the `REG` source and store kinds. Register $x_0$ is hardwired to zero at transpilation time: every read of $x_0$ is replaced by the immediate $0$ and every write to it is dropped, so the VM's register state is $x_1, dots, x_(31)$. The system region of memory (@tbl:address-space) reserves 8-byte slots for the registers at its start, but these slots are not aliased with the registers: registers are only accessed through the `REG` source and store kinds, and ZisK handles them separately from the rest of memory for performance reasons (@sec:registers).

=== Data Memory <sec:memory>

Data memory is a _random access memory (RAM)_ which supports read and write operations. It is separate from the program ROM and is used for mutable state during execution. The ZisK ISA defines a 32-bit byte address space for data memory, but the native unit of access is a 64-bit word (8 bytes). Memory cells are aligned to 8-byte boundaries, so valid addresses are multiples of 8. ZisK supports sub-word and unaligned accesses (1, 2, 4 or 8 bytes at any address) by decomposing them into aligned 8-byte operations (@sec:memory-chip).

To support execution of programs with different data assumptions and properties within the same architecture, we separate data memory into distinct regions, each with its own access semantics. @tbl:address-space summarizes the address space layout and the semantics of each region; addresses outside these regions are invalid.

#figure(
  table(
    stroke: 0.5pt,
    columns: (auto, auto, 1fr),
    align: (center + horizon, center + horizon, auto),
    table.header([*Region*], [*Address Range*], [*Semantics*]),
    [Input Data],
    [`[0x4000_0000, 0x8000_0000)`],
    [[1GB] Read-only. The first word, `0x4000_0000`, is the _free-input port_ through which hints are delivered (@sec:inputs_and_hints); the input starts at `0x4000_0008`.],
    [ROM Data], [`[0x8000_0000, 0x8800_0000)`], [[128MB] Program constants, read-only],
    table.cell(rowspan: 3, align: center + horizon)[Writable RAM],
    [`[0xA000_0000, 0xA001_0000)`],
    [[64KB] System region: register slots, UART, control and status registers, floating-point registers],
    [`[0xA001_0000, 0xA002_0000)`], [[64KB] Output data: public outputs written during execution],
    [`[0xA003_0000, 0xC000_0000)`],
    [[$approx$512MB] Program memory: general-purpose read/write RAM, including the stack and heap],
  ),
  caption: [Memory layout of the ZisK ISA. The address space is divided into three main regions: input data, ROM data, and writable RAM. The 64KB between the output data and the program memory are unused.],
  kind: table,
) <tbl:address-space>

=== Public Outputs <sec:public-outputs>

The guest program exposes $32$ values of $64$ bits ($2048$ bits in total) as _public outputs_. During execution, the guest writes them to the output data region (@tbl:address-space) with ordinary stores. When the guest finishes, an _epilogue_ generated by the transpiler reads the $32$ words of that region back and issues one `pubout` instruction per word, with $a = i in [0, 32)$ the index of the output and $b$ its value. The `pubout` instructions are what binds the proof's public statement to the execution: the public outputs of the statement are exactly these $32$ words (@sec:zisk-statement), and nothing else about the input or the memory.

=== Inputs and Hints <sec:inputs_and_hints>

The host state maintains two streams through which the outside world communicates with the guest. The _input_ is a byte string, of length a multiple of $8$, that is loaded into the input data region at address `0x4000_0008` before execution begins; the guest reads it with ordinary loads. The _hint stream_ provides non-deterministic values at runtime. To obtain hints, the guest passes parameters to the host with `fcall_param`, requests a host computation with `fcall` ---whose operand $a$ identifies the function--- and then reads the result one word at a time with `fcall_get`, each of which reads the free-input port at `0x4000_0000`. Every read of the free-input port may return a different value: it is the only source of non-determinism in a step. Any value received from the host, input or hint, is untrusted until the guest has verified it.

=== Precompile Calls <sec:precompile-calls>

Precompiles are invoked through a calling convention based on CSR instructions, which are free for this purpose since ZisK has no privileged architecture. The caller writes the operands of the operation to memory with ordinary instructions ---typically a _parameter block_ of 8-byte-aligned words holding the operands or pointers to them--- and then executes `csrrs x0, csr, rs1` with `rs1` holding the address of the block. The transpiler maps CSR numbers `0x800` to `0x819` to the precompile opcodes, and turns the CSR instruction into a single ZisK instruction with that opcode, $a = 0$ and $b$ = `REG rs1`. The precompile reads its operands from memory and writes its results back to memory, as described for each opcode in @appendix:opcodes; apart from the DMA opcodes, which take $a$ and $b$ as plain values and return a value in $c$, only `add256` additionally returns a value in $c$, its carry out, which is stored in the destination register of the CSR instruction.

The hint instructions use the same mechanism: CSR numbers `0x8C0` to `0x8DF` encode `fcall` with the function identifier in the CSR number and immediate, `0x8F0` to `0x8FF` encode `fcall_param`, and `0xFFE` encodes `fcall_get`.

== Execution Model <sec:execution_model>

The execution model defines how the VM transitions between states, what constitutes a valid execution, and which parts of an execution are exposed to the verifier.

*Memory as a function.* We model data memory as a function $"mem" : [0, 2^(32)) -> [0, 2^8)$ from byte addresses to bytes. For a width $w in {1, 2, 4, 8}$ and an address $x$ we write $"mem"[x]_w := sum_(i=0)^(w-1) 2^(8 i) dot "mem"(x + i)$ for the little-endian $w$-byte read, and $"mem"[x]_w <- v$ for the memory that stores the $w$ low-order bytes of $v$ at $x, dots, x + w - 1$ and agrees with $"mem"$ elsewhere.

*Guest state.* Since the program is fixed before execution begins, the _guest state_ at step $t$ is
$
  S_t = ("pc"_t, c_t, bold(x)_t, "mem"_t),
$
comprising the program counter, the output of the previous instruction, the registers $bold(x)_t = (x_1, dots, x_(31))$, and the data memory. The host state $H = ("in", "hint")$ is supplied externally.

*Initial state.* Execution begins at a designated boot address $"pc"_"BOOT"$:
$
  S_0 = ("pc"_"BOOT", 0, bold(0), "mem"_0),
$
where $"mem"_0$ holds the input in the input data region, the values that the ROM data policy below prescribes in the ROM data region, and zero everywhere else. The boot code then initializes the data sections of the program (@sec:program), sets up the arguments of the guest's entry point and calls it.

*Step.* Let $iota = P["pc"]$ be the instruction at the current program counter; execution fails if `pc` is not an address of $P$. Given the state $S = ("pc", c, bold(x), "mem")$, one step proceeds as follows (we write $x_0 = 0$).
+ _Operands._ The operands are
  $
    a := cases(
      c & "if" iota."a_src" = mono("C"),
      x_(iota."a_off") & "if" iota."a_src" = mono("REG"),
      "mem"[iota."a_off"]_8 & "if" iota."a_src" = mono("MEM"),
      iota."a_off" + 2^(32) dot iota."a_imm1" & "if" iota."a_src" = mono("IMM"),
    ) quad quad
    b := cases(
      c & "if" iota."b_src" = mono("C"),
      x_(iota."b_off") & "if" iota."b_src" = mono("REG"),
      "mem"[iota."b_off"]_8 & "if" iota."b_src" = mono("MEM"),
      iota."b_off" + 2^(32) dot iota."b_imm1" & "if" iota."b_src" = mono("IMM"),
      "mem"[a + iota."b_off"]_(iota."ind_w") & "if" iota."b_src" = mono("IND"),
    )
  $
  where an indirect access requires $a < 2^(32)$. The $k$-th read of the free-input port in the step returns the $k$-th hint word of the step instead of the memory contents.
+ _Operation._ $(c', "flag") := iota."op"(a, b)$, as specified in @appendix:opcodes. Precompile opcodes additionally read and write memory, as specified there; we write $"mem"^"op"$ for the memory after this effect ($"mem"^"op" = "mem"$ for all other opcodes).
+ _Store._ The stored value is $v := "pc" + iota."j2"$ if $iota."store_pc" = 1$ and $v := c'$ otherwise. The new registers and memory are those of $"mem"^"op"$ and $bold(x)$, updated by $x_(iota."store_off") <- v$ if $iota."store" = mono("REG")$ (and $iota."store_off" != 0$), by $"mem"^"op" [iota."store_off"]_8 <- v$ if $iota."store" = mono("MEM")$, and by $"mem"^"op" [a + iota."store_off"]_(iota."ind_w") <- v$ if $iota."store" = mono("IND")$.
+ _Control flow._ The next program counter is
  $
    "pc"' := cases(
      (c' mod 2^(32)) + iota."j1" & "if" iota."set_pc" = 1,
      "pc" + iota."j1" & "if" iota."set_pc" = 0 and "flag" = 1,
      "pc" + iota."j2" & "if" iota."set_pc" = 0 and "flag" = 0,
    )
  $
  An instruction never has both $iota."set_pc" = 1$ and $"flag" = 1$; in particular, precompile instructions have $"flag" = 0$ and $"set_pc" = 0$, so their extended argument in `j1` never reaches the program counter.

The new state is $S' = ("pc"', c', bold(x)', "mem"')$. We write $S' = "Step"_P (S, h)$, where $h$ is the sequence of hint words that the step reads, in order. Given the hints, the step is deterministic, and the whole execution is a function of the program, the input and the hint stream. We write $a_t$ and $b_t$ for the operands of the step from $S_t$.

*Valid steps.* The step from $S = ("pc", c, bold(x), "mem")$ with hints $h$ is _valid_ if:
- $"pc"$ is an address of $P$, and $P["pc"]$ is not `halt`.
- Every memory access it makes covers $w$ bytes $x, dots, x + w - 1$ that lie in one region of @tbl:address-space.
- It writes nothing to the input data region.
- It reads exactly $abs(h)$ words from the free-input port.
An execution moreover respects the _ROM data policy_ if every write to the ROM data region leaves the memory unchanged, every $8$-byte word of the region is written at most once, and every word of the region that is never written is zero in $"mem"_0$. The contents of the region are thus fixed from the start by the stores of the boot code, which leave them unchanged, and a read of the region returns the same value whenever it happens.

*Terminal condition.* Every ZisK program contains, at the exit address $"pc"_"END"$, an _exit instruction_ with the `end` field set; the only other instructions with `end` set are `halt` sentinels. The guest terminates by returning from its entry point or by the exit system call; in both cases control passes to the epilogue, which emits the public outputs (@sec:public-outputs) and jumps to $"pc"_"END"$. A $T$-step execution is _successful_ if $"pc"_T = "pc"_"END"$ and $c_T = 0$, every step before $T$ is valid, and the execution respects the ROM data policy. Execution _fails_ otherwise: on an undefined program counter, an access outside the regions of @tbl:address-space, a write to the input data region, a write that changes the ROM data region or a second write to one of its words, the `halt` sentinel, or if the program counter never reaches $"pc"_"END"$. Only successful executions are provable, and ZisK bounds their length by $T <= 2^(36)$.

*Public outputs.* The public outputs are not a separate component of the state. For $i in [0, 32)$, the $i$-th public output of the execution is the operand $b$ of the unique step $t$ that executes `pubout` with $a = i$; since the epilogue reads them from the output data region, this is the word $"mem"_t [$`0xA001_0000`$+ 8 i]_8$ at the end of the guest's execution.

*The execution relation.* What a ZisK proof claims is a relation between the external statement ---the program commitment and the public outputs--- and a whole execution. Its witness contains the program itself, which the statement binds only through its commitment, the input, the hints and the sequence of states. We write $"RomRoot"(P)$ for the Merkle root of the Rom chip's cached columns for the program $P$ (@sec:rom-bus), which the setup computes from $P$.

#definition(title: "Execution Relation")[
  The statement is $bold(p)_"ext" = ("root"_"ROM", "out"_0, dots, "out"_(31))$, with $"root"_"ROM" in FF^4$ and $"out"_i in [0, 2^(64))$, and the witness is $w_"exec" = (P, "in", (h_t)_(t < T), (S_t)_(t <= T))$. Then $(bold(p)_"ext"; w_"exec") in cal(R)_"exec"$ if and only if:
  + _Program._ $P$ is valid (@def:valid-program) and $"RomRoot"(P) = "root"_"ROM"$.
  + _Initial state._ $S_0 = ("pc"_"BOOT", 0, bold(0), "mem"_0)$, where $"mem"_0$ holds $"in"$ from address `0x4000_0008` and is zero outside the input data and ROM data regions.
  + _Steps._ For every $t < T$, the instruction $P["pc"_t]$ is defined, the step from $S_t$ with hints $h_t$ is valid, and $S_(t+1) = "Step"_P (S_t, h_t)$.
  + _ROM data._ The execution respects the ROM data policy.
  + _Termination._ $"pc"_T = "pc"_"END"$, $c_T = 0$ and $T <= 2^(36)$.
  + _Public outputs._ Every step $t < T$ that executes `pubout` has $a_t < 32$ and $b_t = "out"_(a_t)$, and for every $i < 32$ exactly one step executes `pubout` with $a_t = i$.
] <def:r-exec>

The statement contains neither the input nor the hints, and the relation constrains them only through the execution they produce (@sec:execution_environment). The relation concerns the committed ZisK program; its connection to the original RISC-V binary is the transpiler correctness of @sec:transpilation, which is assumed. The companion security analysis @ZISK:RECURSION shows, under explicit assumptions, idealizations and obligations on the chips, that an accepting final proof for a statement $bold(p)_"ext"$ whose program commitment is that of a valid program yields, except with a stated probability, a witness of $cal(R)_"exec"$.
