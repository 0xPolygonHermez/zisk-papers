#import "../../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Spec, Time, Zisk, definition, fwd, game, lemma,
  mult, negl, poly, proof, proposition, remark, theorem, todo, vk,
)

The Main chip, the MemAlign chips and the precompiles access memory by
pulling messages on the memory bus; the Memory AIRs prove the aligned
accesses of each region as a sorted log; and the registers are carried by a
linked-step argument of the Main chip on the same bus. The
bus carries no contract. This section states how counting on it, together with
the logs, makes every load of the execution return its memory.

== Accesses

#definition(title: "Accesses of a Collection")[
  An _access_ is a tuple $("op", "addr", t_"mem", "width", v)$ of an
  operation $mono("LOAD")$, $mono("STORE")$ or $mono("REG")$, an address, a
  memory step, a width in bytes and a word $v$, read from a memory-bus message
  whose value limbs are well formed (@lem:words). The _requested_ accesses
  of $L$ are those that the Main chip, the MemAlign chips and the precompiles
  pull; an access is _aligned_ if its width is $8$ and its address a multiple
  of $8$.
] <def:accesses>

#lemma(title: "Memory Bus")[
  Under the hypotheses of @cor:zisk-contracts:
  + the aligned $mono("LOAD")$ and $mono("STORE")$ accesses requested in a
    region, together with those that the MemAlign chips request to implement
    the others, are the submitted accesses of the region's log of
    @lem:mem-chain, as multisets;
  + every sub-word or unaligned access is implemented by MemAlign as the
    corresponding read or write of the aligned words it covers; and
  + the $mono("REG")$ accesses are pushed and pulled only by the Main chip and
    by the global messages that initialize the registers.
] <lem:memory-bus>

#todo[Proof: the third statement of @cor:zisk-contracts on the memory bus;
the regions are disjoint and identified by their addresses; (2) is the
obligation on MemAlign (@tbl:obligations); a message determines its access,
since addresses and steps are below $p$.]

== The Memory of an Execution

#definition(title: "Memory of a Step")[
  For $t <= T$, the _memory_ $"mem"_t$ of step $t$ is the function from byte
  addresses to bytes that holds: in the RAM region, the bytes of the last
  write at a memory step below $1 + 4 t$, or zero if there is none; in the
  ROM data region, the bytes of the unique write to the word, or zero if there
  is none; in the input data region, the value of the word in its log; and
  zero elsewhere.
] <def:mem-of-step>

#lemma(title: "Offline Memory Check")[
  Let a multiset of accesses of a region be the accesses of a log of the
  region from its genesis payload.
  + _RAM._ The writes to an address have distinct memory steps, and every
    read returns the value of the last write to its address at a memory step
    at most its own, or zero if there is none.
  + _ROM data._ Every word is written at most once, and every read returns the
    value of that write, or zero if there is none.
  + _Input data._ All the reads of a word other than the free-input port
    return the same value.
] <lem:offline-memory>

#proof[
  The addresses of a log do not decrease, so the accesses to an address form
  a contiguous block, whose first access is the only one with a new address.

  (1) Within a block, memory steps do not decrease and increase strictly at
  every write, so the writes have distinct steps; the writes before a read in
  the block have steps at most its own, and the writes after it larger steps.
  By induction along the block, every read returns the value of the last write
  before it, or zero if there is none: the first access, if a read, returns
  zero, and every other read returns the value of its predecessor, which is
  that write, or a read that returns the value of that write by induction.

  (2) Within a block, the first access is the only one that can be a write,
  and every other access is a read that returns the value of its predecessor;
  so every access returns the value of the first, which is the value of the
  write if it is one and zero otherwise.

  (3) Within a block of an address other than the free-input port, every
  access but the first returns the value of its predecessor.
]

#lemma(title: "Registers")[
  Under the hypotheses of @cor:zisk-contracts, every read of register
  $i in [1, 31]$ at memory step $t_"mem"$ returns the value of the last
  write to it at a smaller memory step, or zero if there is none.
] <lem:registers>

#todo[Proof: every register access pulls the previous access of its
register and pushes its own, with a range-checked increasing memory step; the
global messages open every chain with value zero at step $0$, and the
end-of-segment reloads carry each register across a segment boundary. With
@lem:memory-bus (3), the accesses of each register form one chain ordered by
memory step.]

#lemma(title: "Loads Read the Memory")[
  Under the hypotheses of @cor:zisk-contracts, if every word stored at a step
  before $t$ is well formed, then every load of step $t$ ---an operand read of
  the Main chip at memory step $1 + 4 t$ or $1 + 4 t + 1$, or a read of a
  precompile dispatched at step $t$--- returns the bytes of $"mem"_t$ at its
  address, except a read of the free-input port, which returns a hint; and
  every read of a register returns its value after step $t - 1$.
] <lem:loads>

#todo[Proof: @lem:memory-bus, @lem:mem-chain, @lem:offline-memory and
@lem:registers, with the slot assignment of memory steps: the reads of step
$t$ come after every write of an earlier step and before the writes of step
$t$. Since @lem:offline-memory lets a read see a write at its own memory step,
this needs that no write at slot $2$ of step $t$ (the store of the Main row)
is to an address that a precompile dispatched at step $t$ reads at that slot,
which the validity of $P_L$ ensures: a precompile instruction stores nothing
in memory.]
