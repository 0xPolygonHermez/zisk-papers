#import "../../lib.typ": definition

We describe the circuit architecture that constitutes the ZisK zkVM. The previous sections established the building blocks: the ISA defines what programs can run (@sec:isa), and the arithmetization framework defines how computations are represented as polynomial constraints (@sec:arithmetization). Here we describe how ZisK instantiates that framework into a concrete system.

#definition(title: "ZisK")[
  Given the ZisK ISA, the _ZisK zkVM_ is the collection of:
  + A host execution environment capable of executing every ZisK instruction.
  + A circuit $cal(C)$ (as in @sec:arithmetization) that constrains a finite sequence of guest state transitions to be valid with respect to a public commitment to a program ROM and an initial guest state. The circuit exposes the final guest public outputs as a public output.
  + Methods to generate the trace matrices from the guest state transitions necessary to generate a proof for $cal(C)$.
]

ZisK's circuit supports only a finite sequence of state transitions, whereas program execution is a priori unbounded. Fixing a single large trace height upfront is impractical: the height would have to be chosen conservatively enough to accommodate every possible program, inflating proof costs even for short executions, while still failing for programs that exceed it. _Continuations_ resolve this tension by organizing and partitioning the execution trace into fixed-height segments, each proved independently. We describe how ZisK implements this mechanism in @sec:continuations.

== Architecture Overview

The ZisK circuit is organized into _chips_, where each chip encapsulates a single AIR together with the methods to generate its trace matrix. Chips fall into two categories:

- *Instruction executor*: Owns the execution logic for a subset of the ZisK ISA. Each instruction is handled by exactly one chip, though a chip may handle multiple related instructions.

- *Table*: Provides auxiliary functionality ---lookup tables, range checks, or cached computation results--- shared by one or more instruction executors.

Chips communicate exclusively through _system buses_: shared channels through which chips exchange messages. The set of system buses used in ZisK is summarized in @tbl:buses. While there are globally shared buses, each chip may expose interfaces for communicating with other particular chips. This modular design means that new instructions can be supported by introducing a new chip and connecting it to the appropriate buses, without modifying any existing chip.

#figure(
  table(
    stroke: 0.3pt,
    columns: (auto, 1fr),
    table.header([*Bus*], [*Purpose*]),
    [Operation Bus], [Routes operations requiring dedicated constraints from some chip to other specialized chips],
    [ROM Bus], [Verifies each instruction fetch against the committed program ROM],
    [Memory Bus], [Enforces read/write consistency across all memory accesses],
    [Continuation Buses], [Carries chip state across segment boundaries],
    [Table Buses], [Connects instruction executor chips to shared lookup tables],
  ),
  caption: [Bus system in ZisK. Each bus serves a specific purpose in the architecture, enabling modular communication between chips and supporting the overall proof structure.],
  kind: table,
) <tbl:buses>

An instruction executor may delegate part of its computation to other chips via a bus, which may in turn query a table chip, and so on. This creates a layered dependency structure, illustrated in @fig:chip-hierarchy: each chip proves only its own local constraints, and bus balancing composes the correctness arguments upward into a global proof.

#figure(
  {
    set text(size: 8.5pt)

    let ex(body) = box(stroke: 0.5pt, inset: (x: 7pt, y: 4pt), radius: 1pt, body)
    let tbl(body) = box(
      stroke: (paint: luma(160), thickness: 0.5pt, dash: "dashed"),
      inset: (x: 7pt, y: 4pt),
      radius: 1pt,
      body,
    )
    let lbl(body) = text(fill: luma(110), size: 7pt, body)

    // A chip row with an optional right-side query to another chip
    let node(chip, side-chip: none, via: []) = {
      if side-chip == none {
        chip
      } else {
        grid(
          columns: (auto, auto, auto),
          align: horizon,
          chip, h(5pt) + lbl[#via →] + h(5pt), side-chip,
        )
      }
    }

    // Downward arrow with bus label, indented to align with chip content
    let dv(label) = pad(left: 9pt, lbl[↓ #label])

    grid(
      columns: (auto, auto),
      column-gutter: 32pt,
      align: top,

      // Left: Arith chain
      stack(
        dir: ttb,
        spacing: 6pt,
        align(center, strong(text(size: 8pt)[Arith chain])),
        node(ex[*Main*]),
        dv[Op Bus],
        node(ex[*Arith*], side-chip: tbl[*Arith Tables*], via: [Table Bus 1]),
        dv[Op Bus],
        node(ex[*Binary*], side-chip: tbl[*Binary Tables*], via: [Table Bus 2]),
      ),

      // Right: Precompile chain
      stack(
        dir: ttb,
        spacing: 6pt,
        align(center, strong(text(size: 8pt)[Keccak chain])),
        node(ex[*Main*]),
        dv[Op Bus],
        // Keccak-f queries two side chips simultaneously
        grid(
          columns: (auto, auto),
          align: (right + horizon, left + horizon),
          ex[*Keccak*],
          pad(left: 6pt, stack(
            dir: ttb,
            spacing: 4pt,
            lbl[Mem Bus →] + h(4pt) + tbl[*Memory*],
            lbl[Table Bus 3→] + h(4pt) + tbl[*Keccak Tables*],
          )),
        ),
      ),
    )
  },
  caption: [
    Two example chip dependency chains in ZisK. Solid borders denote instruction executor chips; dashed borders denote table chips.
    *Left*: the Main chip dispatches an arithmetic operation to Arith via the Operation Bus; Arith queries its own tables and further delegates to Binary, which queries its own tables.
    *Right*: Main dispatches a cryptographic operation to Keccak; the precompile simultaneously reads its inputs and writes its outputs via the Memory Bus and queries its own tables.
    In both cases each chip proves only its own local constraints, and bus balancing composes the arguments into a global proof.
  ],
) <fig:chip-hierarchy>

=== Chip Inventory <sec:chip-inventory>

@tbl:chip-inventory instantiates the abstract circuit $cal(C) = {(cal(A)_i, cal(I)_i)}_(i=1)^M$ of @sec:arithmetization for ZisK: it lists every AIR of the circuit together with its trace height $N_i$, its category, and what it proves. There are $M = 35$ AIRs. Several chips are realised by more than one AIR ---the Memory chip by one AIR per address region, the DMA precompile by twelve AIRs specialised by operation--- so the formal objects are the AIRs, and "chip" is a grouping used for exposition. Recall that the opcode handled by each instruction executor is listed in @appendix:opcodes.

The circuit is fixed: every AIR is part of every ZisK proof's setup. What varies between executions is the number of _instances_ of each AIR, i.e. the number of segments into which its trace is split (@sec:continuations). An execution uses $ceil(n_i \/ N_i)$ instances of AIR $i$, where $n_i$ is the number of rows its workload requires, and none at all of an AIR whose operations never occur. Main and Mem are the exception: their continuation chains are anchored unconditionally (@sec:continuation-bus), so every execution instantiates each of them at least once.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (1.45fr, 0.45fr, 0.8fr, 2.6fr),
      align: (left, center, left, left),
      table.header([*AIR*], [*$log_2 N_i$*], [*Category*], [*Proves*]),
      [Main],
      [22],
      [executor],
      [one instruction step per row: fetch, operand resolution, dispatch, store, control flow, registers],

      [Rom],
      [22],
      [table],
      [the program code, as a lookup table on the ROM Bus (cached columns, committed per program)],

      [Mem], [22], [memory], [sorted access trace of the writable RAM region],
      [RomData], [21], [memory], [sorted access trace of the read-only ROM data region],
      [InputData], [21], [memory], [sorted access trace of the input data region],
      [MemAlign], [21], [memory], [sub-word and unaligned accesses, decomposed into aligned ones],
      [MemAlignByte, MemAlignReadByte, MemAlignWriteByte],
      [22],
      [memory],
      [single-byte accesses (read and write, read only, write only)],

      [Arith], [21], [executor], [64- and 32-bit multiplication, division and remainder],
      [Binary], [22], [executor], [comparisons, minimum and maximum, addition and subtraction, bitwise logic],
      [BinaryAdd],
      [22],
      [executor],
      [64-bit addition (a cheaper alternative to Binary for the most frequent operation)],

      [BinaryExtension], [22], [executor], [shifts and sign extensions],
      [Add256], [20], [precompile], [256-bit addition with carry],
      [ArithEq],
      [20],
      [precompile],
      [256-bit modular arithmetic; secp256k1, secp256r1 and BN254 curve operations; $FF_(p^2)$ arithmetic over the BN254 base field],

      [ArithEq384],
      [20],
      [precompile],
      [384-bit modular arithmetic; BLS12-381 curve operations; $FF_(p^2)$ arithmetic over the BLS12-381 base field],

      [Keccakf], [17], [precompile], [Keccak-f[1600] permutation],
      [Sha256f], [18], [precompile], [SHA-256 compression function],
      [Poseidon2], [17], [precompile], [Poseidon2 permutation of width 16],
      [Blake2br], [18], [precompile], [BLAKE2b round function],
      [Dma, DmaMemCpy, DmaInputCpy],
      [21],
      [precompile],
      [DMA front-ends: decode a bulk memory copy, compare or fill into its phases],

      [Dma64Aligned, Dma64AlignedInputCpy, Dma64AlignedMemSet, Dma64AlignedMem, Dma64AlignedMemCpy],
      [21],
      [precompile],
      [the 8-byte-aligned body of a bulk operation],

      [DmaUnaligned],
      [21],
      [precompile],
      [the body of a bulk operation whose source and destination are not equally aligned],

      [DmaPrePost, DmaPrePostMemCpy, DmaPrePostInputCpy],
      [21],
      [precompile],
      [the partial head and tail words of a bulk operation],

      [SpecifiedRanges], [20], [table], [every range-check table of the circuit],
      [VirtualTable0, VirtualTable1],
      [21],
      [table],
      [the fixed lookup tables of the executors and precompiles (binary, binary extension, arithmetic, Keccak, MemAlign and DMA tables, dual-byte ranges) and the frequent-operation caches of @sec:freq-op-caches, packed into two AIRs],
    )
  },
  caption: [The $M = 35$ AIRs of the ZisK circuit. Rows that list several AIRs share the trace height shown.],
  kind: table,
) <tbl:chip-inventory>

Now we delve into the details of the design of the ZisK chips (@sec:chip-design) and bus system (@sec:bus-system).

== Chip Design <sec:chip-design>

We now turn to the chips themselves: the AIRs that, together with the bus system, implement the ZisK zkVM. The presentation roughly follows the dependency structure of @fig:chip-hierarchy, starting from the central spine and moving outwards. We begin with the _Main_ chip (@sec:main-chip), which materializes one row per instruction step and orchestrates the rest of the system: it fetches instructions, resolves operands, dispatches operations to specialized sub-chips, and writes back results. We then describe the _Memory_ chip (@sec:memory-chip), which centralizes the memory consistency argument that almost every other chip ultimately relies on. The remaining categories cover what the Main delegates: _base-operation_ chips (@sec:base-operations) handle classes of simple operations ---binary, arithmetic, comparisons--- through dedicated AIRs and lookup tables; _precompiles_ (@sec:precompiles) handle expensive or memory-intensive primitives such as elliptic-curve arithmetic, hash functions, and bulk transfers, each as an independent instruction executor with its own internal layout; and _frequent-operation caches_ (@sec:freq-op-caches) commit pre-computed results for the most commonly queried inputs of base operations, replacing constraint checking with a direct lookup wherever possible.

=== The Main <sec:main-chip>

ZisK uses a _Main_ chip as the central execution spine. Each row of the Main AIR corresponds to one instruction step and its trace materializes the full execution transcript. Recalling the notation from @subsec:instruction_format, the Main chip is responsible for:

+ *Instruction fetch*: At each step, the Main chip reads the instruction at the current program counter from the program ROM via the ROM Bus (@sec:rom-bus).

+ *Operand resolution*: The input operands $a$ and $b$ are resolved according to their source modes (immediate, memory, or indirect), with memory reads constrained through the Memory Bus.

+ *Operation dispatch*: Operations that are simple enough are computed directly in the Main chip (e.g., no-ops, jumps, and control flow). Operations requiring dedicated constraint systems ---binary operations, multiplications, cryptographic primitives--- are _delegated_: the Main chip sends the inputs and receives back the result $(c, "flag")$ via the Operation Bus, and a specialized sub-chip proves correctness.

+ *State update*: The output $c$ is written to its destination via the Memory Bus or directly in the Main trace.

==== Registers <sec:registers>

Although the ZisK ISA addresses the 32 general-purpose registers within the same numerical address space as data memory (@sec:memory), ZisK does _not_ route register accesses through the Memory chip. Forcing every register read and write into the sorted memory trace would inflate it ---registers are by far the most frequently accessed locations in any execution--- and would couple the cost of register access to the cost of generic RAM. Instead, the register region is carved out of the Memory chip's domain and handled by the Main chip itself, with a _linked-step argument_ on the Memory Bus whose messages are both sent and received by Main.

Register accesses use a dedicated operation tag $mono("REG")$ on the Memory Bus and the bare register index $i in [1, 31]$ as address, so they can never be confused with a RAM access. For every access to register $i$ at memory step $t_"mem"$ (@sec:timestamps) with value $v$, the Main row also carries the memory step $t_"prev"$ and value $v_"prev"$ of the previous access to the same register, and it
- consumes the message $(mono("REG"), i, t_"prev", 8, v_"prev")$, which certifies that the previous access left $v_"prev"$ in the register;
- emits the message $(mono("REG"), i, t_"mem", 8, v)$, which the next access to the register will consume;
- range-checks $t_"mem" - t_"prev" - 1 in [0, 2^(24))$, so the accesses to each register form a chain strictly increasing in time.
For a read $v = v_"prev"$; for a write $v_"prev"$ is a free column. The chain of every register is opened once per execution by a global term that emits $(mono("REG"), i, 0, 8, 0)$ for $i in [1, 31]$ ---registers start at zero--- and closed at the end of every segment: Main consumes the last message of each register's chain and, unless the segment is the last one, re-emits the same value at the final memory step of the segment, where the next segment picks it up. A chain link therefore never spans more than one segment, which is what keeps the $2^(24)$ bound sufficient. Register $x_0$ is not part of the chain: reads of $x_0$ are replaced by the immediate $0$ and writes to it are dropped.

==== Timestamps <sec:timestamps>

The circuit arithmetization does not inherently represent temporal order. On the other hand, the execution of instructions is inherently sequential. To encode it, ZisK discretizes time by attaching a _timestamp_ to every memory access, so that the memory consistency argument can verify that reads always observe the most recent write to each address.

Time is organized at two granularities. A _main step_ $t in [0, 2^(36))$ indexes one full instruction execution by the Main. Within the $j$-th Main segment ($j = 0, 1, dots$; @sec:continuations) the row $r in [0, N)$ executes step
$
  t = j dot N + r,
$
where the segment index $j$ is an AIR value of the segment, range-checked to $[0, 2^(36) \/ N)$. The step is thus a globally monotone counter: the instruction at step $t$ is executed before the instruction at step $t'$ whenever $t < t'$.

A single main step, however, is not atomic from the memory's perspective: operand resolution requires reads, storing the result requires a write, and a dispatched precompile may independently access memory to read its inputs and write its outputs. To order all of these accesses, each main step $t$ is subdivided into four _memory steps_
$
  t_"mem" = 1 + 4 dot t + s, quad s in {0, 1, 2, 3},
$
with the following fixed slot assignment: $s = 0$ for the read of operand $a$, $s = 1$ for the read of operand $b$, $s = 2$ for the store of $c$ and for the reads of a precompile dispatched at step $t$, and $s = 3$ for the writes of such a precompile and for the end-of-segment register reload of @sec:registers. Memory step $0$ is reserved for the initial state, so that every access of the execution is strictly later than it. Since $t < 2^(36)$, memory steps fit in $38$ bits.

These slots are the only ordering device: the address accessed at each slot is unconstrained and varies freely from instruction to instruction and from chip to chip. A precompile dispatched at step $t$ receives $t$ on the Operation Bus (@sec:operation-bus) and stamps all of its memory accesses with slots $2$ and $3$ of that step ---at addresses entirely different from those of the Main chip, and as many accesses as the operation needs--- so the memory argument orders them exactly where the precompile's effect takes place in the execution. Sub-word stores, which the MemAlign chips implement as a read followed by a write of the enclosing word, stamp the write at the following memory step.

=== Memory <sec:memory-chip>

The _Memory_ chip centralizes all memory access verification. It is realised by three AIRs built from the same template, one per region of @tbl:address-space: Mem for the writable RAM, RomData for the ROM data and InputData for the input data. Each collects the aligned 8-byte operations submitted on the Memory Bus for its region, verifies their consistency, and rejects any execution in which a memory access violates the region's rules.

To enforce correctness, all operations of a region are sorted globally by address, then by memory step within the same address. This reduces the global consistency requirement ---that every read observes the most recent prior write--- to a sequence of local, row-to-row checks. Each row holds a word address $"addr"$ (the byte address divided by $8$), a memory step $t_"mem"$, a value $(v_0, v_1)$ in the two-limb encoding of @sec:word-encoding, a write flag $"wr"$, an address-change flag $rho$ and a selector $"sel"$ indicating whether the row corresponds to an operation on the bus. Comparing each row with the previous one, the AIR enforces:
- _Address order_: if $rho = 1$ the address strictly increases; otherwise it is unchanged.
- _Time order_ (RAM only): within an address, the memory step strictly increases at every write and does not decrease at a read, so several reads of the same word may share a memory step. In the RAM AIR both orders are enforced by a single bounded increment: depending on $rho$, either the address difference or the step difference (adjusted by $1 - "wr"$), minus one, is decomposed into a $22$-bit and a $16$-bit range-checked limb. In the two read-only regions the value of an address never changes, so no time order is needed and only the address increment is range-checked.
- _No silent writes_: every write row has $"sel" = 1$, i.e. corresponds to an operation on the Memory Bus, so no memory modification can occur outside the scope of the consistency argument.
- _Region policy_, depending on the AIR:
  - _RAM_ (Mem): a read at an unchanged address returns the previous row's value, and a read at a new address returns zero, i.e. memory that has never been written reads as zero.
  - _ROM data_ (RomData): the first access to each address is a write and all later accesses are reads returning the same value, so each word is written exactly once.
  - _Input data_ (InputData): there are no writes; the value of each address is a prover-supplied constant shared by every access to it, and its four $16$-bit chunks are range-checked. The only exception is the _free-input port_, the first word of the region, whose value may differ at every read: it is the channel through which hints are delivered (@sec:inputs_and_hints).
- _Region bounds_: the first address of the region's trace is at least the region's base address and the last one at most its end address.

Each address is therefore a contiguous block of rows ordered in time, and the value continuity checks pin the value of every read to the most recent write of the same block. The connection with the requesters is a _permutation_ argument on the Memory Bus (@appendix:arguments): the multiset of operations proved by the Memory AIRs must equal the multiset of operations submitted by the rest of the chips. The trace of each region may span several segments; consecutive segments are chained by a continuation bus (@sec:continuation-bus) so that the sorted order, and with it the checks above, holds across segment boundaries.

==== Memory Access Paths

The access path for a memory operation depends on its width and alignment, as shown in @fig:memory-access-paths:

- *Aligned 8-byte access*: The requesting chip places the operation directly on the Memory Bus. The Memory chip processes it without further decomposition.

- *Sub-word or unaligned access* (1, 2, or 4 bytes): The requesting chip routes the operation to the _MemAlign_ chip instead. MemAlign identifies whether the access falls within a single aligned 8-byte word or spans two consecutive words, decomposes it accordingly, and issues one or two aligned 8-byte operations to the Memory Bus.

#figure(
  {
    set text(size: 8.5pt)
    let box_ex(body) = box(stroke: 0.5pt, inset: (x: 7pt, y: 4pt), radius: 1pt, body)
    let lbl(body) = text(fill: luma(110), size: 7pt, body)

    let box_tbl(body) = box(
      stroke: (paint: luma(160), thickness: 0.5pt, dash: "dashed"),
      inset: (x: 7pt, y: 4pt),
      radius: 1pt,
      body,
    )

    align(center, stack(
      dir: ltr,
      spacing: 0pt,
      stack(
        dir: ttb,
        spacing: 10pt,
        box_ex[*Memory User*],
        lbl[(aligned op)],
        lbl[↓ Mem Bus],
        box_ex[*Memory*],
      ),
      h(32pt),
      stack(
        dir: ttb,
        spacing: 10pt,
        box_ex[*Memory User*],
        lbl[(sub-word / unaligned)],
        lbl[↓ Mem Bus],
        grid(
          columns: (auto, auto),
          align: (right + horizon, left + horizon),
          box_ex[*MemAlign*],
          pad(left: 6pt, stack(
            dir: ttb,
            spacing: 4pt,
            lbl[Table Bus →] + h(4pt) + box_tbl[*MemAlign ROM*],
          )),
        ),
        lbl[(aligned ops)],
        lbl[↓ Mem Bus],
        box_ex[*Memory*],
      ),
    ))
  },
  caption: [Memory access paths. Aligned 8-byte operations go directly to Memory; sub-word and unaligned operations are first decomposed by MemAlign into aligned 8-byte operations.],
) <fig:memory-access-paths>

==== MemAlign

The MemAlign chip models a small processor (the MemAlign ROM) with eight byte-wide registers that hold one aligned 8-byte word, and executes one of four fixed subprograms depending on whether the access is a read or write and whether it fits within one aligned word or spans two:

+ *Read within one word* [One read]: MemAlign performs one aligned read to load the surrounding 8-byte word into its registers, then extracts the requested bytes and returns the value.

+ *Write within one word* [One read, One write]: MemAlign reads the surrounding word, patches the relevant byte positions with the new value, writes the modified word back, and confirms the result.

+ *Read spanning two words* [Two reads]: The requested bytes straddle an 8-byte boundary. MemAlign reads both words, combines the relevant bytes from each, and returns the assembled value.

+ *Write spanning two words* [Two reads, Two writes]: MemAlign reads both words, patches the relevant bytes in each, and writes both modified words back.

In every case, MemAlign issues only aligned 8-byte operations to the Memory Bus. This design allows MemAlign to support all possible sub-word and unaligned accesses with a small, fixed set of constraints, without needing to know the specific access patterns in advance.

=== Base Operations <sec:base-operations>

The _Base Operations_ chips prove the base instruction set operations ---bitwise logic, comparisons, shifts, sign extensions, and integer multiplication and division--- delegated from the Main chip via the Operation Bus.

These chips share a common structural profile that distinguishes them from the Main chip and from precompiles. First, they have no interaction with the Memory Bus: their inputs and outputs flow entirely through the Operation Bus, so they neither read from nor write to the memory state. Second, they carry no state across segment boundaries and therefore use no continuation bus; each segment's proof is self-contained. These two properties mean that Base Operations chips are the simplest kind of instruction executor in ZisK.

Base Operations chips together with the Main chip and Memory chip form the core execution engine of ZisK, responsible for executing every instruction in the ZisK ISA. These chips are not designed for any particular class of operations; rather, they are designed to be flexible enough to support the full range of operations in the ISA, and their constraints are structured to allow efficient delegation of complex operations to specialized sub-chips.

Precompiles, on the other hand, are designed to handle complex operations that would be expensive to constrain step-by-step in the Main chip.

=== Precompiles <sec:precompiles>

_Precompiles_ handle classes of operations ---elliptic curve arithmetic, cryptographic hash functions, bulk memory transfers--- whose decomposition into base operations would be inefficient. Each precompile is an independent instruction executor chip that owns the full proof obligation for its operation.

What distinguishes precompiles from basic operation chips is the complexity of their interface with the rest of the system. A precompile typically reads its inputs and writes its outputs directly from the memory state through the Memory Bus, rather than receiving them as simple 64-bit operands on the Operation Bus. Its computation may span many internal rows ---for example, a hash permutation iterates over multiple rounds--- so its trace height is sized to the operation's intrinsic complexity, independently of the Main chip. Some precompiles (such as DMA) even carry their own internal state across segment boundaries via a continuation bus.

At the ISA level, invoking a precompile follows the calling convention of @sec:precompile-calls: the caller writes the operands to memory with ordinary instructions and then executes a single precompile instruction whose operand $b$ points to them. The parameter-passing instructions are proved like any other instruction; the precompile instruction is dispatched by the Main chip on the Operation Bus together with its main step, and the precompile chip proves the whole memory effect of the operation, reading and writing through the Memory Bus at the memory steps of that main step (@sec:timestamps). Adding a new precompile requires only defining a new chip and wiring it to the appropriate buses, with no changes to any existing chip.

=== Frequent-Operation Caches <sec:freq-op-caches>

Basic operation chips carry a fixed per-invocation overhead: each chip handles a whole family of operations, and a single query pays for the constraints that distinguish all of them, regardless of which one is actually being proved. Across a typical program execution, however, only a small fraction of all possible input combinations actually appear, and those that do appear tend to repeat. ZisK exploits this with _frequent-operation caches_: for binary and arithmetic operations, results for the most commonly queried input pairs are pre-computed and committed once at setup time.

At proof time, sub-chips resolve queries directly from the cache for inputs it covers, and fall back to constraint checking for the remainder. This significantly reduces witness size and proving time for programs with typical workloads.

== Word Encoding over Goldilocks <sec:word-encoding>

The ZisK ISA operates on 64-bit words, i.e. integers in $[0, 2^(64))$ with arithmetic modulo $2^(64)$, while the arithmetization works over the Goldilocks field, whose modulus $p = 2^(64) - 2^(32) + 1$ is smaller than $2^(64)$. A word therefore does not fit in a single field element, and integer overflow must happen at $2^(64)$, not at $p$. ZisK bridges this gap with a uniform encoding that every chip and every bus follows.

- *Two 32-bit limbs.* A word $v$ is represented by two field elements $(v_0, v_1)$ with $v = v_0 + 2^(32) dot v_1$ and $v_0, v_1 in [0, 2^(32))$. Since $2^(32) < p$, every limb has a unique representative in $FF$, and the pair determines $v$. The Main chip's operand and result columns, the Operation Bus, the Memory Bus and the Memory AIRs all use this form (@sec:bus-system); the 32-bit opcodes simply set the high limb of their inputs to zero.
- *Range checks at the producer.* A limb is meaningful only if it lies in $[0, 2^(32))$. ZisK enforces this where a value is _produced_: the executor and precompile chips decompose their results into smaller pieces ---bytes in Binary and BinaryExtension, $16$-bit chunks in BinaryAdd, Arith and the 256- and 384-bit precompiles--- which are range-checked through the table buses of @sec:table-buses, and rebuild each limb from them, e.g. $v_0 = sum_(k=0)^3 2^(8 k) beta_k$ from bytes $beta_k in [0, 2^8)$. Likewise, values entering from the input data region are range-checked by the InputData AIR in $16$-bit chunks. Chips that only _move_ a value ---Main forwarding an operand, the Memory AIRs storing it--- do not check it again: the bus transports the exact limbs, so a consumed value inherits the range established by its producer.
- *Overflow at $2^(64)$.* Arithmetic is verified on the decomposed form, with explicit carries. For instance, BinaryAdd proves $c = a + b mod 2^(64)$ through
  $
    a_0 + b_0 = c_0 + 2^(32) kappa_0, quad a_1 + b_1 + kappa_0 = c_1 + 2^(32) kappa_1, quad kappa_0, kappa_1 in {0, 1},
  $
  discarding the final carry $kappa_1$, and Arith proves multiplications and divisions as integer identities over $16$-bit chunks with range-checked carries. Every term of these identities is bounded well below $p$ by the range checks, so none of them can wrap around modulo $p$: they hold over the integers, and hence modulo $2^(64)$ as the ISA requires.
- *Addresses and steps.* Byte addresses ($32$ bits), program counters ($32$ bits) and memory steps ($38$ bits) are below $p$ and are carried as single field elements, bounded by the range checks of the chips that use them (@sec:memory-chip, @sec:timestamps).

== System Buses <sec:bus-system>

ZisK uses a bus system ---recall @tbl:buses for an overview--- to constrain valid state transitions during program execution. Now we discuss all of them except the continuation bus, which is described in @sec:continuation-bus.

Every bus is an instance of the bus-balancing primitive of @sec:arithmetization, identified by a fixed bus identifier and carrying messages of a fixed schema. All buses are reduced by the same LogUp argument (@sec:logup-reduction) under the global challenges of @sec:challenge-derivation; they differ in the argument they realise (@appendix:arguments). Values in $[0, 2^(64))$ travel as two $32$-bit limbs, following @sec:word-encoding.

=== Operation Bus <sec:operation-bus>

The _operation bus_ routes complex operations from the Main chip to specialized sub-chips. Messages have the form:
$
  ("op", a_0, a_1, b_0, b_1, c_0, c_1, "flag", t, x, "extra"),
$
where $"op" in [0, 2^8)$ identifies the operation (@appendix:opcodes), $(a_0, a_1)$ and $(b_0, b_1)$ are the input operands, $(c_0, c_1)$ is the output, $"flag" in {0, 1}$ is the operation's flag, $t$ is the main step (@sec:timestamps), $x$ is the _extended argument_ of a precompile instruction (@subsec:instruction_format), and $"extra"$ carries additional information used only between the DMA chips.

The main step $t$ plays two different roles depending on the kind of sub-chip on the receiving end. For sub-chips whose entire input/output is already conveyed by $(a, b, c)$ ---i.e. those that do not interact with memory--- $t$ is set to $0$ and carries no information: the operation is fully specified by its operands. For precompiles, by contrast, $(a, b, c)$ is not enough: precompiles read their inputs and write their outputs directly through the memory bus rather than through the operand triple, so each precompile invocation must be tied to a specific point in the execution timeline. In that case, $t$ is set to the current execution step of the Main chip, allowing the precompile's memory accesses to be ordered consistently with the rest of the trace.

When the Main chip delegates an operation, it sends a message on the operation bus and asserts that $(c, "flag") = "op"(a, b)$ without verifying the operation locally; for the $32$-bit opcodes it zeroes the high limbs $a_1, b_1$. The executor or precompile chip in charge of the opcode (@tbl:chip-inventory) receives those messages and proves correctness through its own constraints, as do the frequent-operation caches for the inputs they cover. The bus is a lookup argument: each receiving chip proves a message with a free multiplicity, and executor chips cancel the contribution of their unused (padding) rows with a single term per segment, derived from its AIR values.

=== ROM Bus <sec:rom-bus>

The _ROM bus_ ensures correctness of instruction fetching. Messages are instructions in the format of @subsec:instruction_format, keyed by their address:
$
  ("pc", "a_off", "a_imm1", "b_off", "b_imm1", "ind_w", "op", "store_off", "j1", "j2", "flags"),
$
where $"flags" = 1 + sum_k 2^k f_k$ packs the fifteen boolean fields $f_k$ of the instruction (source and store kinds, `store_pc`, `set_pc`, `m32`, `is_external_op` and `is_precompiled`). The constant $1$ makes every instruction distinct from the all-zero padding rows of the table.

The Main chip sends one message per row, built from the instruction columns of that row; the Rom chip proves the program as a lookup table, with one row per instruction and a free multiplicity column. The Rom chip's table columns are _cached_ (@sec:arithmetization): they are committed once per program, and their Merkle root is the _program commitment_ $"root"_"ROM"$, a public input of every ZisK proof (@sec:zisk-statement). Balancing of the ROM bus therefore implies that the instruction executed at every Main row is the one stored at its program counter in the committed program.

=== Memory Bus <sec:memory-bus>

The _memory bus_ is the channel through which every chip that reads from or writes to an address space submits its memory operations. Messages have the form:
$
  ("op"_"mem", "addr", t_"mem", "width", v_0, v_1),
$
where $"op"_"mem" in {mono("LOAD") = 1, mono("STORE") = 2, mono("REG") = 3}$ is the access type, $"addr" in [0, 2^32)$ is the target byte address (the register index for $mono("REG")$ messages, @sec:registers), $t_"mem"$ is the memory step (@sec:timestamps), $"width" in {1, 2, 4, 8}$ is the access width in bytes, and $(v_0, v_1)$ is the value read or written.

The requesters ---Main, the MemAlign chips and the precompiles--- submit their operations; the three Memory AIRs prove the aligned 8-byte ones; the MemAlign chips prove the sub-word and unaligned ones and in turn submit the aligned operations they decompose them into (@fig:memory-access-paths); and Main both submits and proves the $mono("REG")$ messages of the register argument. The bus is a permutation argument, so balancing it, together with the constraints of the Memory AIRs, implies that every read observes the most recent write to its address.

=== Table Buses <sec:table-buses>

The remaining buses connect executor and precompile chips to fixed tables, which are packed into the SpecifiedRanges, VirtualTable0 and VirtualTable1 AIRs (@tbl:chip-inventory). Each table bus is a lookup argument whose receiving side is a fixed table with a free multiplicity column, so balancing implies that every message sent on it is a row of the table. @tbl:table-buses lists them.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (1.2fr, 2.6fr, 1fr),
      align: (left, left, left),
      table.header([*Table*], [*Rows*], [*Queried by*]),
      [Binary table],
      [one byte of a byte-sliced comparison, subtraction or bitwise operation, with carry in and out],
      [Binary],

      [Binary extension table], [one byte of a shift or sign extension], [BinaryExtension],
      [Arith table], [decoding of the Arith operations and of their sign and range selectors], [Arith],
      [Arith range table], [$16$-bit chunks, sign-dependent chunk ranges and carry ranges of Arith], [Arith],
      [MemAlign program], [the micro-program executed by MemAlign], [MemAlign],
      [ArithEq comparison table], [chunk-wise comparison used for modular reduction], [ArithEq, ArithEq384],
      [Keccak-f table], [the bit-sliced Keccak-f round functions], [Keccakf],
      [DMA tables], [DMA micro-program, partial-word patterns and byte comparisons], [DMA chips],
      [Dual range tables], [pairs of values in $[0, 2^7)$, resp. $[0, 2^8)$], [MemAlign, DMA chips],
      [Range checks], [one bus per range $[x, y]$ used in the circuit], [all chips],
    )
  },
  caption: [Table buses of ZisK. The frequent-operation caches of @sec:freq-op-caches are also fixed tables, but they receive on the Operation Bus instead of a bus of their own.],
  kind: table,
) <tbl:table-buses>

Finally, a few buses are internal to a single chip: the DMA chips use a permutation bus to hand a bulk operation from the front-end AIR to its head-and-tail AIR, and Blake2br uses a permutation bus to apply its message permutation. Neither carries messages from outside the chip.
