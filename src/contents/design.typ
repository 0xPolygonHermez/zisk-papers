#import "../lib.typ": definition, remark, lemma

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

@tbl:chip-inventory enumerates every AIR of the ZisK circuit $cal(C)$ at v0.16.1, with its trace height $N_i$ and the category it belongs to. This is the concrete instantiation of the abstract circuit $cal(C) = {(cal(A)_i, cal(I)_i)}_(i=1)^M$ of @sec:arithmetization: $M = 35$, of which $32$ are instruction-executor or memory AIRs and $3$ are table AIRs. The recursion circuits of @sec:recursion are not part of $cal(C)$; they are listed in the topology of @sec:topology. Several chips are realised by more than one AIR (the Memory chip by three region AIRs, MemAlign by four, DMA by twelve); conversely, every AIR belongs to exactly one chip, so "chip" is a grouping of AIRs for exposition and the formal objects are the AIRs.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (1.25fr, 0.45fr, 0.9fr, 2.4fr),
      align: (left, center, left, left),
      table.header([*AIR*], [*$log_2 N_i$*], [*Category*], [*Proves*]),
      [Main], [22], [executor (spine)], [one instruction step per row: fetch, operand resolution, dispatch, store, control flow, register argument],
      [Rom], [22], [table (cached)], [the program $P$ as a lookup table on the ROM Bus; cached columns committed per program],
      [Mem], [22], [memory], [sorted access trace of the writable RAM region],
      [RomData], [21], [memory], [sorted access trace of the read-only data region],
      [InputData], [21], [memory], [sorted access trace of the input-data region (free values)],
      [MemAlign], [21], [memory helper], [sub-word and unaligned accesses as sequences of aligned ones],
      [MemAlignByte, MemAlignReadByte, MemAlignWriteByte], [22], [memory helper], [single-byte accesses (read+write, read-only, write-only variants)],
      [Arith], [21], [executor], [64/32-bit multiplication, division and remainder],
      [Binary], [22], [executor], [byte-sliced comparisons, min/max, subtraction, bitwise logic],
      [BinaryAdd], [22], [executor], [64-bit addition],
      [BinaryExtension], [22], [executor], [shifts, rotations, sign extension],
      [Add256], [20], [precompile], [256-bit addition with carry],
      [ArithEq], [20], [precompile], [256-bit modular arithmetic, secp256k1/secp256r1/BN254 curve and $FF_(p^2)$ operations],
      [ArithEq384], [20], [precompile], [384-bit modular arithmetic and BLS12-381 curve and $FF_(p^2)$ operations],
      [Keccakf], [17], [precompile], [Keccak-f[1600] permutation],
      [Sha256f], [18], [precompile], [SHA-256 compression function],
      [Poseidon2], [17], [precompile], [Poseidon2 permutation of width 16],
      [Blake2br], [18], [precompile], [BLAKE2b round function],
      [Dma, DmaMemCpy, DmaInputCpy], [21], [precompile], [DMA front-ends: decode a bulk copy/compare/set into phases],
      [Dma64Aligned and 4 variants], [21], [precompile], [aligned bulk copy, compare and set loops],
      [DmaUnaligned], [21], [precompile], [unaligned bulk copy and compare],
      [DmaPrePost, DmaPrePostMemCpy, DmaPrePostInputCpy], [21], [precompile], [head and tail partial words of a DMA operation],
      [SpecifiedRanges], [20], [table], [all range-check tables ($[0, 2^(16))$, $[0, 2^(22))$, $[0, 2^(24))$, signed carry ranges, ...)],
      [VirtualTable0, VirtualTable1], [21], [table], [packed fixed lookup tables: arithmetic, binary, binary-extension, Keccak, MemAlign program, DMA tables, frequent-operation caches, dual-byte ranges],
    )
  },
  caption: [The $M = 35$ AIRs of ZisK v0.16.1. Instances of each AIR are created on demand by trace splitting (@sec:continuations); an execution uses as many instances of each AIR as its workload requires, and none of an AIR whose operation never occurs.],
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

Although the ZisK ISA addresses the 32 general-purpose registers within the same numerical address space as data memory (@sec:memory), ZisK does _not_ route register accesses through the Memory chip. Forcing every register read and write to traverse the sorted memory trace would inflate it ---registers are by far the most frequently accessed locations in any execution--- and would couple the cost of register access to the cost of generic RAM. Instead, the register region is carved out of the Memory chip's domain and handled by the Main chip with a _linked-step argument_ on the Memory Bus.

Concretely, every register access at memory step $t_"mem"$ (@sec:timestamps) to register $i in [1, 31]$ with value $v$ is accompanied in the Main trace by the memory step $t_"prev"$ of the previous access to the same register. The Main chip _receives_ the message $(mono("REG"), i, t_"prev", 8, v_"prev")$ ---asserting that the previous access exists and left value $v_"prev"$--- and _sends_ $(mono("REG"), i, t_"mem", 8, v)$, where $v_"prev" = v$ for a read and $v_"prev"$ is a free witness column for a write. A range check $0 <= t_"mem" - t_"prev" - 1 < 2^(24)$ forces the chain of accesses to each register to be strictly increasing in time. The chain is opened once, globally, by a receive of $(mono("REG"), i, 0, 8, 0)$ for every $i$ (registers start at zero), and it is closed by the last segment; at every segment boundary the Main chip reloads all $31$ registers (@sec:continuation-bus), which is what keeps the $2^(24)$ window sufficient. The register messages use the opcode $mono("REG")$ and the bare index $i$ as address, so they can never be confused with a RAM message. @sec:memory-relation states the relation this argument enforces and its refinement to the ISA view in which registers are memory cells.

==== Timestamps <sec:timestamps>

The circuit arithmetization does not inherently represent temporal order. On the other hand, the execution of instructions is inherently sequential. To encode it, ZisK discretizes time by attaching a _timestamp_ to every memory access, so that the memory consistency argument can verify that reads always observe the most recent write to each address.

Time is organized at two granularities. A _main step_ $t in [0, 2^(36))$ indexes one full instruction execution by the Main; it is the global step counter of the execution model, reconstructed inside a segment as $t = "seg" dot N + r$ from the segment index $"seg"$ (an AIR value, range-checked) and the row $r$. A single main step, however, is not atomic from the memory's perspective: operand resolution requires reads, storing the result requires a write, and a dispatched precompile may independently access memory to read its inputs and write its outputs. To order all of these accesses, each main step $t$ is subdivided into four _memory steps_
$
  t_"mem" = 1 + 4 dot t + s, quad s in {0, 1, 2, 3},
$
with the following fixed slot assignment: $s = 0$ for the read of operand $a$, $s = 1$ for the read of operand $b$, $s = 2$ for the store of $c$ and for the reads of a precompile dispatched at step $t$, and $s = 3$ for the writes of such a precompile, for the write-back that MemAlign performs on behalf of a slot-2 store, and for the end-of-segment register reload. Memory step $0$ is reserved for the global initialisation of the registers. Since $t < 2^(36)$, memory steps fit in $38$ bits. The slot is the only ordering device: the address accessed at each slot is unconstrained and varies freely from instruction to instruction and from chip to chip, but an operation dispatched at step $t$ can only stamp its accesses with the memory steps of step $t$, because the Main chip places $t$ on the Operation Bus for every precompile call (@sec:operation-bus) and the precompile chip derives its memory steps from that value.

=== Memory <sec:memory-chip>

The _Memory_ chip centralizes all memory access verification. It is realised by three AIRs of the same template, one per address region (@tbl:chip-inventory): Mem for writable RAM, RomData for the read-only data, and InputData for the input-data region. Each AIR collects every memory operation submitted on the Memory Bus for its region, verifies their consistency, and rejects any execution in which a memory access violates the region's rules.

To enforce correctness, all submitted operations are sorted globally by address, then by memory step within the same address. This reduces the global consistency requirement ---that every read observes the most recent prior write--- to a sequence of local, row-to-row checks. We now state precisely what the AIR enforces; the constraint system is the one of `mem.pil` at v0.16.1, and the description below is complete with respect to the soundness-relevant constraints.

==== Memory Consistency Relation <sec:memory-relation>

A row of a Memory AIR is a tuple $(rho, "addr", t_"mem", "wr", "sel", v)$ with $rho in {0, 1}$ the _address-change_ flag, $"addr" in [0, 2^(29))$ a word address, $t_"mem"$ a memory step, $"wr" in {0, 1}$ the write flag, $"sel" in {0, 1}$ the _bus selector_, and $v = (v_0, v_1) in [0, 2^(32))^2$ the value as two limbs. Rows with $"sel" = 1$ emit the message $("op", 8 dot "addr", t_"mem", 8, v_0, v_1)$ on the Memory Bus with $"op" = mono("STORE")$ if $"wr" = 1$ and $mono("LOAD")$ otherwise, as a _prove_ (positive multiplicity); rows with $"sel" = 0$ emit nothing and exist only to bridge address gaps or to pad the trace. The Memory Bus is a _permutation_ argument (@appendix:arguments): the multiset of messages proved by the Memory AIRs must equal the multiset of messages assumed by all requesters.

#definition(title: "Sorted Access Trace")[
  Fix a region with word-address interval $["base", "end"]$. A sequence of rows $(rho_r, "addr"_r, t_r, "wr"_r, "sel"_r, v_r)_(r in [R])$, together with a _previous row_ $("addr"_0, t_0, v_0)$ supplied by the continuation bus (@sec:continuation-bus), is a _sorted access trace_ of the region if for every $r in [R]$:
  + (_Region_) $"base" <= "addr"_1$ and $"addr"_R <= "end"$ (each enforced by a $32$-bit range check on the distance).
  + (_Address order_) $rho_r = 1 => "addr"_r > "addr"_(r-1)$, and $rho_r = 0 => "addr"_r = "addr"_(r-1)$.
  + (_Time order_) $rho_r = 0 => t_r - t_(r-1) >= "wr"_r$, i.e. strictly increasing steps for writes and non-decreasing steps for reads, so that several reads of the same word at the same memory step are allowed.
  + (_Bounded increments_) the quantity $rho_r ("addr"_r - "addr"_(r-1)) + (1 - rho_r)(t_r - t_(r-1) + 1 - "wr"_r) - 1$ lies in $[0, 2^(38))$, witnessed by a $22$-bit and a $16$-bit range-checked limb.
  + (_No silent writes_) $"wr"_r = 1 => "sel"_r = 1$.
  + (_Read-after-write_) $rho_r = 0 and "wr"_r = 0 => v_r = v_(r-1)$.
  + (_Region policy_) for the writable RAM region, $rho_r = 1 and "wr"_r = 0 => v_r = 0$ (an address that is read before ever being written reads as zero). For the read-only data region, $"wr"_r = rho_r dot "sel"_r$: the first access to each address is a write and all later accesses are reads. For the input-data region, $"wr"_r = 0$ and, except at the free-input port (the region's base address), $rho_r = 0 => v_r = v_(r-1)$; at the free-input port the value is unconstrained on every row.
  The relation $cal(R)_"MEM"^("region")$ consists of all $(x_"mem"; w_"mem")$ where $w_"mem"$ is such a trace and $x_"mem"$ is the pair of boundary rows carried on the continuation bus.
] <def:sorted-access-trace>

The witness-side facts that make the definition sound are recorded here because the soundness sketch relies on them. Padding rows repeat the last row's address, step and value with $"sel" = "wr" = 0$, which satisfies every constraint and emits nothing. Because increments are bounded by $2^(38)$ on the RAM region, whose address space is $2^(29)$ words and whose time span is $2^(38)$ memory steps, no address or time gap ever requires a bridging row there; the read-only and input-data regions use a $2^(24)$ address-increment bound and insert bridging rows with $"sel" = 0$ where an address gap exceeds it. The selectors are constrained to be binary, so a row cannot emit a message with multiplicity greater than one.

What the sorted access trace guarantees is the semantic memory relation of the execution model. Say that a multiset $O$ of memory operations $("op", x, t_"mem", w, v)$ is _consistent with an initial memory_ $"mem"_0$ if, processing the operations in order of $t_"mem"$, every $mono("LOAD")$ returns the value most recently stored at its address, or the initial value if none.

#lemma(title: "Memory Argument")[
  Let $O$ be the multiset of aligned memory messages assumed by the requester AIRs of a satisfying circuit witness, restricted to a region, and suppose the Memory Bus balances. Then the region's Memory AIR instances jointly form a sorted access trace whose $"sel" = 1$ rows are exactly $O$, and $O$ is consistent with the region's initial memory: zero for RAM, the values of the first (write) access to each address for the read-only data region, and an arbitrary per-address constant for the input-data region. In particular every read of the RAM region observes the most recent prior write to its address, and the input-data region behaves as a read-only memory with prover-chosen contents whose values, once fixed by the first read, are the same for every subsequent read.
] <lem:memory-argument>

The proof is the standard one for sorted memory-checking @FOCS:BEGKN91: address and time order make the trace a concatenation of per-address blocks ordered in time; the permutation argument makes the blocks contain exactly the requested operations (with duplicates counted); read-after-write and the region policy pin the value of every read. The lemma is stated as a proof obligation in @sec:proof-obligations (it is a property of the constraint system, not of the cryptography). Two refinements connect the lemma to the ISA view of memory in @sec:execution_model: the _register refinement_, which shows that the linked-step argument of @sec:registers enforces the same consistency property for the $31$ register cells, and the _MemAlign refinement_, which shows that the sub-word and unaligned operations proved by MemAlign are equivalent to the ISA's byte-granular reads and writes (@sec:memalign-refinement).

#remark(title: "Binding of the read-only data region")[
  @lem:memory-argument makes the contents of the read-only data region equal to the values of the _first_ access to each address, which is a write requested on the Memory Bus. Whether those values equal the constants $"ROMDATA"_P$ of the program binary therefore depends on which chip requests the initialising writes and on how that chip is bound to the program commitment $"root"_"ROM"$. In the current ZisK sources the ROM AIR emits the initialising writes from its committed cached columns, which binds them to $"root"_"ROM"$; the corresponding proof obligation for v0.16.1 is listed explicitly in @sec:proof-obligations.
]

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

==== MemAlign Refinement <sec:memalign-refinement>

MemAlign receives from the requester the unaligned message $("op", x, t_"mem", w, v)$ with $w in {1, 2, 4}$ or $8 divides.not x$, and assumes from the Memory chip one or two aligned messages: the reads $(mono("LOAD"), 8 floor(x \/ 8), t_"mem", 8, u_0)$ and, if the access spans two words, $(mono("LOAD"), 8 floor(x \/ 8) + 8, t_"mem", 8, u_1)$; for a write, additionally the stores of the patched words at memory step $t_"mem" + 1$. The fixed MemAlign program table (a lookup on its own table bus) forces the byte selection and patching to be the little-endian extraction and replacement of bytes $x mod 8, dots, x mod 8 + w - 1$ of the concatenation $u_0 || u_1$. The stamping of the write-back at $t_"mem" + 1$ is what preserves the order of the read-modify-write pair inside the requester's slot, and it is the reason a store slot is followed by a reserved slot in @sec:timestamps.

#lemma(title: "MemAlign Refinement")[
  In a satisfying circuit witness with balanced buses, every unaligned or sub-word message assumed by a requester is realised by aligned messages on the Memory Bus whose net effect on the byte-granular memory function of @sec:execution_model is exactly $"mem"[x]_w$ for a load and $"mem"[x]_w <- v$ for a store, and no other byte is modified.
] <lem:memalign-refinement>


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

== Word Encoding over Goldilocks <sec:word-encoding>

The ZisK ISA operates on 64-bit unsigned integers, while the arithmetization works over the Goldilocks field with $p = 2^(64) - 2^(32) + 1 < 2^(64)$. A 64-bit word therefore does not fit canonically into one field element, and integer overflow must occur at $2^(64)$, not at $p$. ZisK resolves this with a uniform encoding, which every bus schema in @sec:bus-system and every trace column holding an ISA value adheres to.

- *Canonical limbs.* A 64-bit value $v$ is represented as two field elements $(v_0, v_1)$ with $v = v_0 + 2^(32) v_1$ and $v_0, v_1 in [0, 2^(32))$. Since $2^(32) < p$, each limb has a unique canonical representative, and the pair determines $v$ uniquely. The Main chip, the Operation Bus, the Memory Bus and the Memory AIRs all use this two-limb form; the `_w` opcodes zero the high limb of their operands on the Operation Bus.
- *Range constraints.* A limb column is a valid 32-bit limb only if constrained to $[0, 2^(32))$. In ZisK this is enforced at the point where a value is _produced_: the executor chips decompose their outputs further (bytes in Binary and BinaryExtension, $16$-bit chunks in BinaryAdd, Arith and the 256/384-bit precompiles) and range-check the pieces via the table buses, and reconstruct the limbs as $v_0 = sum_k 2^(8 k) b_k$ or $sum_k 2^(16 k) h_k$. A value that is only _consumed_ (e.g. an operand received by the Main from a register) inherits its range from the message that produced it, since the bus transports the exact limbs.
- *Overflow at $2^(64)$.* Arithmetic operations are verified on the decomposed form with explicit carries: addition as $a_0 + b_0 = c_0 + 2^(32) kappa_0$, $a_1 + b_1 + kappa_0 = c_1 + 2^(32) kappa_1$ with $kappa_i in {0, 1}$ and $kappa_1$ discarded; multiplication in Arith as the integer identity $a dot b + c = 2^(64) d_"hi" + d_"lo"$ over $16$-bit chunks with range-checked carries. None of these identities can wrap modulo $p$, because every term is bounded far below $p$ by its range constraints.
- *Addresses and steps.* Addresses are $32$-bit and carried as a single field element; memory steps are $38$-bit and carried as a single field element; both are bounded by range checks or by the increment argument of @def:sorted-access-trace. The Memory chip's word address is the byte address divided by $8$; the bus carries the byte address.

The consequence for the security analysis is that the map from a satisfying trace to ISA values is well defined and injective on every column that the relations of @sec:statement read, so an extractor can decode 64-bit words from field elements without ambiguity. The obligation that every limb column consumed by a relation is actually range-constrained is recorded in @sec:proof-obligations.

== System Buses <sec:bus-system>

ZisK uses a bus system ---recall @tbl:buses for an overview--- to constrain valid state transitions during program execution. Every bus is an instance of the bus-balancing primitive of @sec:arithmetization with a fixed _message schema_ and a fixed _semantic relation_ that balancing enforces; we give both for each bus. All 64-bit values use the two-limb encoding of @sec:word-encoding. The continuation buses are described in @sec:continuation-bus.

=== Operation Bus <sec:operation-bus>

The _Operation Bus_ (identifier $5000$) routes operations from the Main chip to the executor and precompile chips. Messages have the form
$
  ("op", a_0, a_1, b_0, b_1, c_0, c_1, "flag", t, x, "extra"),
$
where $"op" in [0, 2^8)$ identifies the operation, $(a_0, a_1), (b_0, b_1), (c_0, c_1)$ are the operands and result, $"flag" in {0, 1}$, $t$ is the main step, $x$ is the extended argument (the `j1` field of a precompile instruction) and $"extra"$ is a chip-specific field used only by the DMA chips. The Main chip _sends_ one message per row with $"is_external_op" = 1$, setting $t = x = 0$ unless the instruction is a precompile call, and zeroing $a_1, b_1$ for `_w` opcodes; the frequent-operation caches _receive_ messages of the form $("op", a_0, a_1, b_0, b_1, c_0, c_1, "flag")$ (trailing zeros are implicit); every executor and precompile chip _receives_ the messages for its opcodes; and the global public-output binding of @sec:statement _receives_ the $32$ `pubout` messages. Executor chips whose rows are not all used cancel their padding rows with a degree-zero term (@sec:continuation-bus).

#definition(title: "Operation Bus Relation")[
  A message $("op", a, b, c, "flag", t, x, "extra")$ received by a non-precompile chip is _valid_ if $(c, "flag") = "op"(a, b)$ according to @appendix:opcodes. A message received by a precompile chip is valid if $(c, "flag") = "op"(a, b)$ and the chip's memory messages (@sec:memory-bus) at memory steps $1 + 4t + 2$ (reads) and $1 + 4t + 3$ (writes) realise the memory effect $"Eff"_"op"$ of @sec:execution_model. Balancing of the Operation Bus in a satisfying circuit witness implies that every message sent by the Main is valid.
] <def:operation-bus-relation>

The implication holds because each receiving AIR's constraints accept only valid messages for the opcodes it handles, the frequent-operation tables are fixed columns containing only valid triples, and the multiset equality of the lookup argument means every sent message equals some received one. The only sender is the Main chip (and, for the `pubout` opcode, the global binding), so the relation is a property of the Main's rows.

=== ROM Bus <sec:rom-bus>

The _ROM Bus_ (identifier $7890$) ensures correctness of instruction fetching. Messages have the form
$
  ("pc", "a_off", "a_imm1", "b_off", "b_imm1", "ind_w", "op", "store_off", "j1", "j2", "flags"),
$
where the fields are those of @subsec:instruction_format and $"flags"$ packs the boolean fields as
$
  "flags" = 1 + 2 dot [mono("a_src") = mono("IMM")] + 2^2 [mono("a_src") = mono("MEM")] + 2^3 "is_precompiled" + 2^4 [mono("b_src") = mono("IMM")] + 2^5 [mono("b_src") = mono("MEM")] + 2^6 "is_external_op" \
  + 2^7 "store_pc" + 2^8 [mono("store") = mono("MEM")] + 2^9 [mono("store") = mono("IND")] + 2^(10) "set_pc" + 2^(11) "m32" + 2^(12) [mono("b_src") = mono("IND")] + 2^(13) [mono("a_src") = mono("REG")] + 2^(14) [mono("b_src") = mono("REG")] + 2^(15) [mono("store") = mono("REG")].
$
The constant $1$ makes every genuine instruction distinct from the all-zero padding rows of the table. The Main chip _sends_ one message per row, formed from its decoded instruction columns; the ROM chip _receives_ them with a free multiplicity column against its cached columns, which hold the table $P$. Since the ROM chip's columns are committed once per program and bound to the program commitment $"root"_"ROM"$ (@sec:vk-ledger), balancing gives:

#definition(title: "ROM Bus Relation")[
  Balancing of the ROM Bus in a satisfying circuit witness implies that at every Main row the decoded instruction equals $P["pc"]$, where $P$ is the program committed to by $"root"_"ROM"$; i.e. $iota_t = "Fetch"_P (S_t)$ for every step $t$.
] <def:rom-bus-relation>

=== Memory Bus <sec:memory-bus>

The _Memory Bus_ (identifier $10$) is the channel through which every chip that reads from or writes to an address space submits its memory operations. Messages have the form
$
  ("op"_"mem", "addr", t_"mem", "width", v_0, v_1),
$
where $"op"_"mem" in {mono("LOAD") = 1, mono("STORE") = 2, mono("REG") = 3}$, $"addr" in [0, 2^(32))$ is the byte address (or the register index for $mono("REG")$ messages), $t_"mem"$ is the memory step (@sec:timestamps), $"width" in {1, 2, 4, 8}$, and $(v_0, v_1)$ is the value. Requesters ---Main, MemAlign, the precompiles--- _send_ their operations; the three Memory AIRs _receive_ aligned ones; MemAlign receives unaligned ones and sends the aligned ones it decomposes them into; and the Main both sends and receives the $mono("REG")$ messages of its linked-step argument. The bus is a permutation argument, and its semantic relation is @lem:memory-argument together with its two refinements: balancing implies that the requested operations, taken over the whole execution, are consistent with the initial memory $"mem"_0$ of @sec:execution_model.

=== Table Buses <sec:table-buses>

The remaining buses connect executor chips to fixed tables. Each is a lookup argument (@appendix:arguments) whose receiving side is a table AIR with fixed columns and a free multiplicity column, so its semantic relation is simply membership of the sent message in the table. @tbl:table-buses lists them. The range-check buses are the specialisation of @appendix:arguments; all of them are hosted in the SpecifiedRanges AIR, and the two dual-byte tables in the VirtualTable AIRs.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (1fr, 0.4fr, 2.7fr, 0.9fr),
      align: (left, center, left, left),
      table.header([*Table*], [*Id*], [*Message schema and meaning*], [*Senders*]),
      [BinaryTable], [125], [$("pos", "op", a, b, "cin", c, "flags")$: one byte of a byte-sliced binary operation with carry in and result flags], [Binary],
      [BinaryExtensionTable], [124], [$("op", "off" | "flags", a, b, c_0, c_1)$: one byte of a shift, rotation or sign extension], [BinaryExtension],
      [ArithTable], [331], [$("op", "flags", "range"_"ab", "range"_"cd")$: operation decoding and range selectors for Arith], [Arith],
      [ArithRangeTable], [330], [$("range_id", v)$: $16$-bit chunk and signed-carry ranges for Arith], [Arith],
      [MemAlignRom], [133], [$("pc", Delta "pc", Delta "addr", "off", w, "flags")$: the MemAlign micro-program], [MemAlign],
      [ArithEqLtTable], [5002], [$("lt", Delta)$: chunk-wise comparison for modular reduction], [ArithEq, ArithEq384],
      [KeccakfTable], [126], [bit-sliced Keccak round tables], [Keccakf],
      [FrequentOps (3 tables)], [5010--5012], [$("op", a, b, c, "flag")$ on the Operation Bus: cached results of frequent arithmetic, binary and shift operations], [(receive from Main)],
      [DmaRom, DmaPrePostTable, DmaByteCmpTable], [8001--8003], [DMA micro-program, partial-word and byte-comparison tables], [Dma chips],
      [DualByte, DualRange7Bits], [88, 77], [$(x, y)$ with $x, y in [0, 2^8)$ resp. $[0, 2^7)$: two range checks per lookup], [MemAlign, Dma chips],
      [Range checks], [$>= 100$], [$(x)$ with $x in ["lo", "hi"]$ for each declared range], [all chips],
    )
  },
  caption: [Table buses of ZisK v0.16.1. Every table is a fixed column set committed at setup (@sec:vk-ledger); the DMA chips additionally use an inter-chip permutation bus (identifier $8000$) to hand in-flight operations between their front-end and worker AIRs.],
  kind: table,
) <tbl:table-buses>
