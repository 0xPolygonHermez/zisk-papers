#import "../../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Spec, Time, Zisk, corollary, definition, fwd,
  game, lemma, mult, negl, poly, proof, proposition, remark, theorem, todo, vk,
)

This section states what each chip of ZisK establishes about the messages it
proves, in the terms of @sec:per-bus, from the constraints of its AIR. The chips on which the reconstruction of the execution rests ---the
Rom, the fixed tables, BinaryAdd, the Main chip and the Memory AIRs--- are
proved sound below; the soundness of the others is stated, with the same
contract, as an obligation. The last section orders the chips and applies
@thm:system-soundness.

== Valid Programs <sec:valid-programs>

The Main chip executes whatever instructions the program table holds. Its
rows follow the step semantics of the ISA only if the table is the ROM table
of a _valid_ program, as $cal(R)_"exec"$ requires: one whose instructions
have their fields in their domains, take $"m32"$, $"is_external_op"$ and
$"is_precompiled"$ from their opcodes, use register indices in $[1, 31]$, and
set $"set_pc"$ only for opcodes whose flag is always zero. In the ROM table of
such a program the addresses are distinct, and the packed flags of every
message select exactly one source for each operand and at most one store.
No AIR checks validity: it is a property of the committed program, which the
external verifier fixes by comparing $"root"_"ROM"$ with the commitment of
the program it expects. Every program produced by the transpiler is valid,
and the theorem of @sec:theorem-iii assumes that the program committed in
$"root"_"ROM"$ is.

== The Rom and the Fixed Tables

The Rom chip has a single interaction: it proves, on the ROM bus, every row of
its table columns with a free multiplicity. Its table columns are cached
(@def:columns), so by $Local$ they open the commitment $"root"_"ROM"$ carried
in the public statement.

#lemma(title: "Program Table")[
  Let the Rom witnesses of $L$ have the same cached columns, and let $P_L$ be
  the program whose messages are their rows other than the all-zero padding
  rows. Then $"RomRoot"(P_L) =
  "root"_"ROM"$, and every push on the ROM bus is a message of $P_L$. These
  pushes are unconditional.
] <lem:rom>

#proof[
  The Rom chip has no constraint other than its interaction, which proves a
  row of its cached columns; $Local$ requires these columns to open the
  coordinates of $bold(p)_"ext"$ that hold $"root"_"ROM"$, which is the
  statement $"RomRoot"(P_L) = "root"_"ROM"$. Every push is a row of the
  cached columns, hence a message of $P_L$, whatever the witness; the chip
  makes no pull, so its pushes are unconditional.
]

The hypothesis that all the Rom witnesses have the same cached columns follows
from the binding of $Commit_"cach"$, since they all open the same
$"root"_"ROM"$; its failure is a term of the composition in Part IV. With the
program $P_L$, the predicate of the ROM channel states that the message is a
message of $P_L$.

The other chips that prove from fixed columns have the same shape: the range
tables, the tables of the binary, binary extension, arithmetic, MemAlign and
DMA chips, the Keccak-f table, and the frequent-operation caches, which prove
on the operation bus. Each proves, with a free multiplicity, a row of its
fixed columns.

#lemma(title: "Fixed Tables")[
  Every push of a chip that proves from fixed columns is a row of those
  columns, unconditionally. If the fixed columns are the table that the chip's
  bus specifies, the pushes meet their contracts.
] <lem:tables>

#proof[
  The fixed columns are part of the verification key of the chip, so every
  locally satisfying witness has them, and every interaction of the chip
  proves a row of (some of) them. If they are the specified table, a row of them
  satisfies the predicate of its channel.
]

That the fixed columns of every table are the specified table, and that every
row of a frequent-operation cache is a correct operation, are properties of
the setup, which this analysis takes as obligations (@tbl:obligations).

== BinaryAdd

The BinaryAdd chip proves the $64$-bit addition $mono("add")$ on the
operation bus, one operation per row. A row holds the limbs $a_0, a_1, b_0,
b_1$ of the operands, four $16$-bit chunks $gamma_0, dots, gamma_3$ of the
result and two carries $kappa_0, kappa_1$, with the constraints
$
  kappa_i (1 - kappa_i) = 0, quad
  a_0 + b_0 = 2^(32) kappa_0 + 2^(16) gamma_1 + gamma_0, quad
  a_1 + b_1 + kappa_0 = 2^(32) kappa_1 + 2^(16) gamma_3 + gamma_2,
$
the chunks range-checked to $[0, 2^(16))$ on a range bus. It proves
$(mono("add"), a_0, a_1, b_0, b_1, c_0, c_1, 0, 0, 0, 0)$ with
$c_0 = 2^(16) gamma_1 + gamma_0$ and $c_1 = 2^(16) gamma_3 + gamma_2$, and
cancels its padding rows, which prove $0 + 0 = 0$, with a single interaction
per instance.

#lemma(title: "BinaryAdd")[
  The BinaryAdd chip is sound, relying on the $16$-bit range channel: every
  push it makes meets the contract of $mono("add")$.
] <lem:binary-add>

#proof[
  Let the pulls of the range channel meet their contract, so that every chunk
  lies in $[0, 2^(16))$, and let a row have $a_0, a_1, b_0, b_1 < 2^(32)$.
  Then $c_0, c_1 < 2^(32)$. The first equation holds in $FF$ between two
  integers below $2^(33) < p$, hence over the integers, and so does the second,
  with $kappa_0 in {0, 1}$. Adding the first to $2^(32)$ times the second,
  $a + b = c + 2^(64) kappa_1$ for the words of the limbs, so
  $c = a + b mod 2^(64)$ with flag $0$, which is $mono("add")(a, b)$. The
  padding interaction carries the message of $0 + 0 = 0$, which meets the
  contract whatever its multiplicity.
]

The proof is the pattern of every operation chip of ZisK: the result is
decomposed into range-checked pieces, the operation is checked as an identity
between integers bounded below $p$, and the identity holds over the integers,
hence modulo $2^(64)$.

== The Main Chip

A Main witness holds one segment of the execution. Its AIR values give the
segment index $j$, whether it is the last segment, the program counter
$"pc"^"in"$ and the output $c^"in"$ it starts from, and the program counter
$"pc"^"out"$ and the output $c^"out"$ it ends with. Its row $r in [0, N)$, of
step $t = j N + r$, holds the fields of an instruction ---its program counter
$"pc"_r$, opcode, source and store flags, offsets, immediates and jump
offsets--- and the limbs of the operands $a_r$ and $b_r$, the result $c_r$
and the flag of the row. We write $c^"prev"_r$ for $c^"in"$ if $r = 0$ and
for $c_(r - 1)$ otherwise, and $"next"_r$ for the program counter that the
step rule of the ISA gives after row $r$:
$"pc"_r + "j1"$ if the flag of the row is $1$, $c_(r, 0) + "j1"$ if
$"set_pc"$, and $"pc"_r + "j2"$ otherwise.

#lemma(title: "Main Rows")[
  Let $w$ be a Main witness with $Local_"Main" (bold(p), w)$ whose pulls on
  the ROM channel, the operation channels and the range channels meet their
  contracts. Then for
  every row $r$:
  + _Fetch._ The row holds the fields of the message of $P_L$ at
    $"pc"_r$, and $"pc"_r$ is an address of $P_L$.
  + _Operands._ $a_r$ is $c^"prev"_r$ if its source is $mono("C")$, the
    immediate of the instruction if it is $mono("IMM")$, and otherwise the
    value of the access that the row pulls on the memory bus: the load of the
    word at address $"a_off"$ ($mono("MEM")$), at memory step $1 + 4 t$, or,
    for register $"a_off"$ ($mono("REG")$), the access at that memory step
    that the row pushes after pulling the previous access to the register. Likewise $b_r$, at memory step
    $1 + 4 t + 1$, where an indirect source ($mono("IND")$) loads $"ind_w"$
    bytes at address $a_(r, 0) + "b_off"$, with $a_(r, 1) = 0$.
  + _Operation._ If the instruction is internal, it is `flag`, with result
    $0$ and flag $1$, or `copyb`, `fcall_param`, `fcall` or `fcall_get`, with
    result $b_r$ and flag $0$. If it is
    external and the limbs of $a_r$ and $b_r$ are well formed, then the
    result and the flag of the row are those of the operation on $a_r$ and
    $b_r$, the result is well formed, and, for a precompile, its memory effect
    at step $t$ is the one its prover makes.
  + _Store._ If the instruction stores, the row pulls on the memory bus, at
    memory step $1 + 4 t + 2$, the store of $"pc"_r + "j2"$ if
    $"store_pc"$ and of $c_r$ otherwise, at the address or register of its
    destination.
  + _Control._ $"pc"_0 = "pc"^"in"$, $"pc"_(r + 1) = "next"_r$ for
    $r < N - 1$, and $"pc"^"out" = "next"_(N - 1)$ and $c^"out" = c_(N - 1)$.
] <lem:main-rows>

#todo[Proof: from the constraints of the Main AIR at v0.16.1: the ROM lookup with the packed flags, the source and store selectors, the internal opcodes, the operation lookup with the $"m32"$ masking, and the program-counter constraint.]

The memory accesses that the lemma names are pulls on a counted channel: the
lemma says which accesses a row makes, not what they return. @sec:memory shows
that they return the memory of the execution, and @sec:stitching that the
segments follow one another.

== The Memory AIRs

The three Memory AIRs are instances of one template, for the RAM, the ROM
data and the input data regions. A witness of a region holds a slice of rows
$("addr", t_"mem", v, "wr", "sel")$ of the region's access log, preceded by
the payload $B^"in"$ that it pulls on the continuation bus, which plays the
role of the row before its first row.

#lemma(title: "Memory Rows")[
  Let $w$ be a witness of the Memory AIR of a region, with
  $Local_tau (bold(p), w)$, whose pulls on the range channels meet their
  contracts. Then the sequence of its rows, preceded by $B^"in"$, satisfies
  the conditions of a log of the region, with the first
  address of the first segment new; its addresses lie between the base and
  the end of the region; the accesses it proves on the memory bus are those of
  its selected rows, as aligned $8$-byte operations; and it pushes on the
  continuation bus its last row as the payload of the next segment, unless it
  is the last segment.
] <lem:mem-rows>

#todo[Proof: from the constraints of the Mem template at v0.16.1, for its RAM, immutable and free-input variants.]

== Obligations

The soundness of the other chips is stated as an obligation, in the same form:
every push meets the contract of its channel, relying on the table and range
channels and, where stated, on operation channels; and every interaction of
the chip on the memory bus has multiplicity $0$, $1$ or $-1$. @tbl:obligations
lists them.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (1.4fr, 2.6fr),
      align: (left, left),
      table.header([*Chips*], [*Obligation*]),
      [Binary, BinaryExtension], [sound for the operation channels of their opcodes],
      [Arith], [sound for the operation channels of its opcodes, relying on the comparisons it assumes from Binary],
      [Add256, ArithEq, ArithEq384, Keccakf, Sha256f, Poseidon2, Blake2br],
      [sound for the operation channels of their opcodes, including the memory effect],

      [Dma, DmaMemCpy, DmaInputCpy],
      [sound for the operation channels of the DMA opcodes, relying on the operations they assume from the DMA workers],

      [Dma64Aligned, DmaUnaligned, DmaPrePost and their variants],
      [sound for the operation channels of the internal DMA operations, including their memory effect],

      [MemAlign, MemAlignByte, MemAlignReadByte, MemAlignWriteByte],
      [every sub-word or unaligned access they prove is the corresponding read or write of the aligned words they access],

      [Fixed tables and frequent-operation caches],
      [their fixed columns are the specified tables, and every cache row is a correct operation],
    )
  },
  caption: [Obligations on the chips that this analysis does not prove sound.],
  kind: table,
) <tbl:obligations>

== The Order

#proposition(title: "Order of the Chips")[
  Under the obligations of @tbl:obligations, the chips of ZisK are sound for
  the channels of @def:zisk-channels and ordered by any linear order that
  places
  + the fixed tables and the Rom first;
  + then Binary, BinaryAdd, BinaryExtension, the precompiles and the DMA
    workers;
  + then Arith and the DMA front-ends;
  + then the MemAlign chips and the Memory AIRs;
  + and the Main chip last.
] <prop:zisk-order>

#proof[
  _Soundness._ The Rom and the fixed tables are sound, with unconditional
  pushes, by @lem:rom and @lem:tables, under the obligation on the contents of
  the fixed tables and the caches; BinaryAdd is sound, relying on a range
  channel, by @lem:binary-add. The Main chip and the Memory AIRs push only on
  the memory and continuation buses, whose channels are counted, so every
  push they make meets its contract: they are sound, establishing
  @lem:main-rows and @lem:mem-rows respectively, relying on the ROM, operation
  and range channels. The other chips are sound by the obligations.

  _Order._ Every chip may rely on the table and range channels, whose only
  pushers are the fixed tables, first in the order. Beyond these, the chips
  that rely on a predicate channel are Arith, on the comparison operations,
  which Binary and the caches prove; the DMA front-ends, on the internal
  operations, which the DMA workers prove; and the Main chip, on the ROM
  channel, which the Rom proves, and on the operation channels, which the
  operation chips and the caches prove. In each case the pushers come earlier
  in the order, or are the caches, whose pushes are unconditional.
]

#corollary(title: "Contracts of ZisK")[
  Let $(bold(p)_"ext"; (bold(p)_"pv", L)) in cal(R)_Zisk$, let the Rom
  witnesses of $L$ have the same cached columns, with $P_L$ valid, and let
  the obligations of @tbl:obligations hold. Then every pull and every push of
  $cal(J)_bold(p) (L)$ meets its contract, every Main witness of $L$ satisfies
  @lem:main-rows and every Memory witness @lem:mem-rows, and the memory and
  continuation buses carry the same multiset of messages pushed as pulled.
] <cor:zisk-contracts>

#proof[
  The witnesses of $L$ are locally satisfying and $L$ is balanced for
  $bold(p)$, with $abs(L) < 2^B$, so $Lambda(L) + g <= Lambda_"max" < p$. The
  global messages are compatible with the channels of @def:zisk-channels, and
  the chips are sound and ordered by @prop:zisk-order. @thm:system-soundness
  then gives the contracts, and the specifications @lem:main-rows and
  @lem:mem-rows of the Main witnesses and the Memory witnesses. Its third
  statement applies to the memory and continuation buses, whose
  multiplicities are $0$, $1$ and $-1$: the Memory AIRs and the continuation
  interactions have boolean selectors; the selectors of the Main chip are its
  source and store flags, which the validity of $P_L$ makes exclusive; and for
  the other chips this is part of their obligations.
]
