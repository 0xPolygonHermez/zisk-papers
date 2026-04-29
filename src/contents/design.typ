#import "../lib.typ": definition

// TODO
// #remark(title: "field dependency")[
//   The ZisK ISA operates on 64-bit unsigned integers ---values in $[0, 2^(64))$--- but the underlying arithmetization works over Goldilocks $p = 2^(64) - 2^(32) + 1$. Because $p < 2^(64)$, there is a semantic gap: integer operations in the ZisK ISA are defined modulo $2^(64)$, while field arithmetic is modulo $p$. The constraint systems for operations such as addition, multiplication, and comparison must explicitly account for this difference, handling overflow at $2^(64)$ rather than at $p$.
// ]

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

Now we delve into the details of the design of the ZisK chips (@sec:chip-design) and bus system (@sec:bus-system).

== Chip Design <sec:chip-design>

We now turn to the chips themselves: the AIRs that, together with the bus system, implement the ZisK zkVM. The presentation roughly follows the dependency structure of @fig:chip-hierarchy, starting from the central spine and moving outwards. We begin with the _Main_ chip (@sec:main-chip), which materializes one row per instruction step and orchestrates the rest of the system: it fetches instructions, resolves operands, dispatches operations to specialized sub-chips, and writes back results. We then describe the _Memory_ chip (@sec:memory-chip), which centralizes the memory consistency argument that almost every other chip ultimately relies on. The remaining categories cover what the Main delegates: _base-operation_ chips (@sec:base-operations) handle classes of simple operations ---binary, arithmetic, comparisons--- through dedicated AIRs and lookup tables; _precompiles_ (@sec:precompiles) handle expensive or memory-intensive primitives such as elliptic-curve arithmetic, hash functions, and bulk transfers, each as an independent instruction executor with its own internal layout; and _frequent-operation caches_ (@sec:freq-op-caches) commit pre-computed results for the most commonly queried inputs of base operations, replacing constraint checking with a direct lookup wherever possible.

=== The Main <sec:main-chip>

ZisK uses a _Main_ chip as the central execution spine. Each row of the Main AIR corresponds to one instruction step and its trace materializes the full execution transcript. Recalling the notation from @subsec:instruction_format, the Main chip is responsible for:

+ *Instruction fetch*: At each step, the Main chip reads the instruction at the current program counter from the program ROM via the Program Bus.

+ *Operand resolution*: The input operands $a$ and $b$ are resolved according to their source modes (immediate, memory, or indirect), with memory reads constrained through the Memory Bus.

+ *Operation dispatch*: Operations that are simple enough are computed directly in the Main chip (e.g., no-ops, jumps, and control flow). Operations requiring dedicated constraint systems ---binary operations, multiplications, cryptographic primitives--- are _delegated_: the Main chip sends the inputs and receives back the result $(c, "flag")$ via the Operation Bus, and a specialized sub-chip proves correctness.

+ *State update*: The output $c$ is written to its destination via the Memory Bus or directly in the Main trace.

==== Registers

Although the ZisK ISA addresses the 32 general-purpose registers within the same numerical address space as data memory (@sec:memory), the proof system does _not_ route register accesses through memory. Forcing every register read and write to traverse the Memory Bus would inflate the global memory trace ---registers are by far the most frequently accessed locations in any execution--- and would couple the cost of register access to the cost of generic RAM. Instead, the register region is carved out of memory's domain and handled internally by the Main chip. Operand-resolution and store-back constraints reference register values directly from the Main chip, with a per-register linked-step argument (analogous to the global memory consistency argument, but local to the Main) ensuring that every register read observes the most recent write. From the program's standpoint nothing changes ---a load or store to the register region behaves exactly as the ISA prescribes--- but the underlying argument is local to Main rather than dispatched on the Memory Bus.

==== Timestamps <sec:timestamps>

The circuit arithmetization does not inherently represent temporal order. On the other hand, the execution of instructions is inherently sequential. To encode it, ZisK discretizes time by attaching a _timestamp_ to every memory access, so that the memory consistency argument can verify that reads always observe the most recent write to each address.

Time is organized at two granularities. A _main step_ $t$ indexes one full instruction execution by the Main. Because rows within a trace are strictly increasing, $t$ is a globally monotone counter across the entire execution; i.e., if $t_i < t_j$ for all $i < j$ and the instruction at step $t_i$ is always executed before the instruction at step $t_j$.

A single main step, however, is not atomic from the memory's perspective: operand resolution requires reads, storing the result requires a write, and a dispatched precompile may independently access memory to read its inputs and write its outputs. To order all of these accesses, each main step $t$ is subdivided into four fixed _memory step_ timestamps:
$
  t_"mem" = 4 dot t + s, quad s in {0, 1, 2, 3}
$
with slots $0, 1$ reserved for reads and slots $2, 3$ for writes. These four timestamps are the only ordering device: the address accessed at each slot is unconstrained and varies freely from instruction to instruction and from chip to chip. Any operation dispatched at step $t$ can use the same four memory step values to stamp its own memory accesses ---at addresses entirely different from those of the Main chip, but it can perform as much accesses as needed during its execution.

=== Memory <sec:memory-chip>

The _Memory_ chip centralizes all memory access verification. The Memory chip collects all submitted operations, verifies their consistency, and rejects any execution in which a memory access violates the memory rules.

To enforce correctness, all submitted operations are sorted globally by address, then by step within the same address. Within a given address, memory steps act as timestamps that must be strictly increasing; each time the address changes, the new address must be strictly greater than the previous one, so no address can appear more than once in non-consecutive blocks. This reduces the global consistency requirement ---that every read observes the most recent prior write--- to a sequence of local, row-to-row checks.

Recall from @sec:memory that address space is partitioned into regions, each governed by one of three access policies. The mutable RAM region supports arbitrary reads and writes: any address may be written at any step, and subsequent reads return the last written value; a read to an address that has never been written returns zero. Immutable regions (ROM and input data) admit exactly one write per address, which must be the first access to it; all later accesses are reads returning that same value.

The input data is also considered the region for the hint stream (@sec:inputs_and_hints): they carry no writes, their values are treated as unconstrained inputs supplied by the executor, and all accesses to the same address must agree on that value. Notably, the same address may be read multiple times at the same step in these free-input regions (i.e., the hint stream region described above) ---a property exploited by precompiles that need to read the same input data repeatedly during their execution.

Value continuity for mutable memory follows from the sorted order: because rows for the same address are contiguous and ordered by step, the chip verifies each read against the immediately preceding row using adjacent-row constraints. Writes are additionally subject to a silent write prohibition: every write must produce a message on the Memory Bus, ensuring no memory modification can occur outside the scope of the consistency argument.

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

At the ISA level, invoking a precompile follows a calling convention: the caller issues a sequence of parameter-passing instructions, a call instruction, and result-retrieval instructions. These steps appear in the Main chip trace as bookkeeping steps that set up and tear down the call, but carry no proof obligation themselves. Adding a new precompile requires only defining a new chip and wiring it to the appropriate buses, with no changes to any existing chip.

=== Frequent-Operation Caches <sec:freq-op-caches>

Basic operation chips carry a fixed per-invocation overhead: each chip handles a whole family of operations, and a single query pays for the constraints that distinguish all of them, regardless of which one is actually being proved. Across a typical program execution, however, only a small fraction of all possible input combinations actually appear, and those that do appear tend to repeat. ZisK exploits this with _frequent-operation caches_: for binary and arithmetic operations, results for the most commonly queried input pairs are pre-computed and committed once at setup time.

At proof time, sub-chips resolve queries directly from the cache for inputs it covers, and fall back to constraint checking for the remainder. This significantly reduces witness size and proving time for programs with typical workloads.

== System Buses <sec:bus-system>

ZisK uses a bus system ---recall @tbl:buses for an overview--- to constrain valid state transitions during program execution. Now we discuss all of them except the continuation bus, which is described in @sec:continuation-bus.

=== Operation Bus

The _operation bus_ routes complex operations from the Main chip to specialized sub-chips. Messages have the form:
$
  ("op", a, b, c, "flag", t, "extra"),
$
where $"op" in [0, 2^8)$ identifies the operation, $a,b in [0, 2^64)$ are the input operands, $c in [0, 2^64)$ is the output, $"flag" in {0, 1}$ indicates whether the operation was valid, $t$ is the main step (@sec:timestamps), and $"extra" in [0, 2^32)$ carries any additional information needed to prove correctness.

The main step $t$ plays two different roles depending on the kind of sub-chip on the receiving end. For sub-chips whose entire input/output is already conveyed by $(a, b, c)$ ---i.e. those that do not interact with memory--- $t$ is set to $0$ and carries no information: the operation is fully specified by its operands. For precompiles, by contrast, $(a, b, c)$ is not enough: precompiles read their inputs and write their outputs directly through the memory bus rather than through the operand triple, so each precompile invocation must be tied to a specific point in the execution timeline. In that case, $t$ is set to the current execution step of the Main chip, allowing the precompile's memory accesses to be ordered consistently with the rest of the trace.

When the Main chip delegates an operation, it sends a message on the operation bus and asserts that $(c, "flag") = "op"(a, b)$ without verifying the operation locally. The corresponding sub-chip receives those messages and proves correctness through its own constraints.

=== ROM Bus

The _ROM bus_ ensures correctness of instruction fetching. Messages have the form:
$
  ("pc", "a_imm", "b_imm", "op", "store_offset", "jmp_offsets", "flags"),
$
where $"pc" in [0, 2^32)$ is the program counter, $"a_imm", "b_imm" in [0, 2^64)$ are the immediate values, $"op" in [0, 2^8)$ identifies the operation, $"store_offset" in [-2^32, 2^32)$ is the memory offset for store instructions, $"jmp_offsets" in [-2^32, 2^32)^2$ are the jump offsets for control flow instructions, and $"flags" in {0, 1}^k$ are flags indicating various instruction properties (e.g., whether it is a precompile call).

Instruction executor chips query this bus to verify that the instruction they execute exists in the program ROM at the given program counter. A dedicated ROM chip provides the program ROM as a lookup table.

=== Memory Bus

The _memory bus_ is the channel through which every chip that reads from
or writes to an address space submits its memory operations. Messages have the form:
$
  ("op"_"mem", "addr", t_"mem", "width", "data"),
$
where $"op"_"mem" in {0, 1}$ is the access type (0: read, 1: write),
$"addr" in [0, 2^32)$ is the target address, $t_"mem"$ is the memory step (@sec:memory-chip),
$"width" in {1, 2, 4, 8}$ is the access width in bytes, and
$"data" in [0, 2^(8 dot "width"))$ is the value read or written.
The Memory chip collects all messages on this bus
and enforces global memory consistency.
