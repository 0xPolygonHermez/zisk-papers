#import "../../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, fwd, game, lemma, mult,
  negl, poly, proof, proposition, remark, theorem, todo, vk,
)

The state of the machine at step $t$ is $S_t = ("pc"_t, c_t, bold(x)_t, "mem"_t)$:
the program counter, the output of the previous instruction, the registers
$x_1, dots, x_(31)$ and the data memory, a map from the $32$-bit byte addresses
to bytes. A program $P$ is a finite partial map from instruction addresses to
instructions, and one step from $S$, with the sequence $h$ of hint words that
it reads, gives the state $"Step"_P (S, h)$, as the whitepaper specifies,
operand by operand, for every opcode. A step is _valid_ if its program counter
is an address of $P$ whose instruction is not `halt`, every memory access it
makes lies in one region of the address space, it writes nothing to the input
data region, and it reads exactly the words of $h$ from the free-input port.

The relation has the external statement
$bold(p)_"ext" = ("root"_"ROM", "out"_0, dots, "out"_(31))$ as statement and a
whole execution $w_"exec" = (P, "in", (h_t)_(t < T), (S_t)_(t <= T))$ as
witness, and $(bold(p)_"ext"; w_"exec") in cal(R)_"exec"$ requires:
- _Program._ $P$ is valid and $"RomRoot"(P) = "root"_"ROM"$: its
  instructions are instructions of the ISA (@sec:valid-programs), and the
  root of the Rom chip's cached columns for $P$ is the program commitment.
- _Initial state._ $S_0 = ("pc"_"BOOT", 0, bold(0), "mem"_0)$, where
  $"mem"_0$ holds $"in"$ from address `0x4000_0008` and is zero outside the
  input data and ROM data regions.
- _Steps._ For every $t < T$, the step from $S_t$ with hints $h_t$ is valid and
  $S_(t+1) = "Step"_P (S_t, h_t)$.
- _ROM data._ Every write to the ROM data region leaves the memory unchanged,
  every word of the region is written at most once, and every word that is
  never written is zero in $"mem"_0$.
- _Termination._ $"pc"_T = "pc"_"END"$, $c_T = 0$ and $T <= 2^(36)$.
- _Public outputs._ Every step $t < T$ that executes `pubout` has operands
  $a_t < 32$ and $b_t = "out"_(a_t)$, and for every $i < 32$ exactly one step
  executes `pubout` with $a_t = i$.

The ROM data clause records what the arithmetization enforces for the
read-only region, which groups the accesses to a word but does not order them
in time: the contents of the region are fixed from the start by the stores of
the boot code, and a read returns the same value whenever it happens. The
statement contains neither the input nor the hints; a guest that wants its
outputs bound to its input must expose, for instance, a hash of the input
among them.

== Transpiler Correctness

The relation concerns the committed ZisK program. Its connection to the
RISC-V binary that the developer compiled is the correctness of the
transpiler, an off-chain, deterministic tool that this analysis does not
verify.

#definition(title: "Transpiler Correctness")[
  The transpiler is _correct_ if, for every supported RISC-V binary $P_"rv"$
  and its transpilation $P$, every successful execution of $P$ on an input
  $"in"$ and hints $h$ that declares the public outputs $"out"_0, dots,
  "out"_(31)$ corresponds to an execution of $P_"rv"$ on $"in"$, with the host
  answering its requests for hints by $h$, that terminates and produces the
  same outputs.
] <def:transpiler>

We assume that the transpiler is correct; every statement of this paper is
about the committed ZisK program, and becomes a statement about the RISC-V
binary only through this assumption.

== Words and Limbs <sec:encoding>

The ISA computes on $64$-bit words, with arithmetic modulo $2^(64)$, while the
traces and the messages of ZisK are vectors over $FF$, of order
$p = 2^(64) - 2^(32) + 1 < 2^(64)$. ZisK writes every word as two $32$-bit
limbs. The rest of this section states when limbs stand for words, and where
the range of every limb is established.

We identify every element of $FF$ with its representative in $[0, p)$.

#definition(title: "Words")[
  The _word_ of a pair of limbs $(v_0, v_1) in FF^2$ is
  $"word"(v_0, v_1) := v_0 + 2^(32) v_1 in NN$, and the _split_ of a
  $64$-bit value $v in [0, 2^(64))$ is
  $"split"(v) := (v mod 2^(32), floor(v \/ 2^(32))) in FF^2$. A pair of limbs is
  _well formed_ if $v_0, v_1 < 2^(32)$.
] <def:words>

#lemma(title: "Words and Limbs")[
  For every $v in [0, 2^(64))$, $"split"(v)$ is well formed and
  $"word"("split"(v)) = v$; for every well-formed pair,
  $"split"("word"(v_0, v_1)) = (v_0, v_1)$. Hence $"word"$ is a bijection from
  the well-formed pairs to $[0, 2^(64))$, and two messages whose words are
  carried in well-formed pairs are equal if and only if the words are.
] <lem:words>

#proof[
  Both limbs of $"split"(v)$ are below $2^(32) < p$, so they are their own
  representatives, and $(v mod 2^(32)) + 2^(32) floor(v \/ 2^(32)) = v$. For a
  well-formed pair, $v_0 + 2^(32) v_1 < 2^(64)$, and division by $2^(32)$ with
  remainder recovers $v_1$ and $v_0$. The last statement follows, since a
  message determines its limbs and the limbs, when well formed, determine the
  word and are determined by it.
]

The lemma is what lets the analysis read words off messages: the operands and
results of the Operation Bus, the values of the Memory Bus and the outputs in
$bold(p)_"ext"$ are words exactly when their limbs are well formed. A pair that is
not well formed is not the split of its word, and two pairs may differ in
$FF^2$ while having the same $"word"$, so every pair that the reconstruction
reads must be shown to be well formed.

== Where Limbs Are Well Formed

ZisK establishes the range of a limb where the value is _produced_, and chips
that only move a value do not check it again. In the terms of @sec:per-bus, the producers are:
- _The program._ The immediates of an instruction are fields of the
  committed program, in $[0, 2^(32))$ by the instruction format.
- _The Operation Bus._ The contract of every operation states that the limbs
  of its result are well formed whenever those of its operands are
  (@def:zisk-channels); for a precompile, the words that it writes to memory
  are well formed by the contract of its memory effect.
- _The input data region._ Its AIR range-checks every value in $16$-bit
  chunks, so every word read from the input, and every hint, is well formed.
- _The global messages._ The public outputs are two $32$-bit limbs of each
  word in $bold(p)_"ext"$ by the instantiation of @sec:instantiation, and the
  initial values of the registers and the anchors of the memory chains carry
  the value zero.

Starting from these producers, the reconstruction of @sec:theorem-iii shows,
step by step, that every operand, result, register and memory word of the
execution is well formed: a value is read either from a producer or from a
word that an earlier step stored, which the induction has already shown to
be well formed.

== Addresses, Steps and Wrap-Around

Byte addresses ($32$ bits), program counters ($32$ bits), memory steps
(at most $2^(38)$) and segment indices (below $2^(36) \/ N$) are below $p$ and are
carried as single field elements, so an equality between two of them in $FF$
is an equality of integers. The chips bound them by range checks where they
are produced, and the soundness of every chip includes that the arithmetic
identities it checks over range-checked chunks hold over the integers rather
than modulo $p$: this is how the result of an operation is the one the ISA
specifies, modulo $2^(64)$.
