#import "../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, fwd, game, lemma, mult,
  negl, poly, proof, proposition, remark, theorem, todo, vk,
)
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

Consider a party that needs the result of a computation but cannot, or does
not want to, carry it out itself: a blockchain that must validate a block of
transactions without every node re-executing it, a light client that follows
a chain it cannot store, or a service that runs a computation on behalf of
its users. The party delegates the computation to a _prover_, which runs the
program and returns the result. Nothing guarantees that the prover is honest,
so the result comes with a proof, and the party that checks it, the
_verifier_, accepts the result only if the proof convinces it of the claim

#quote(block: true)[
  _"The program $P$, run on the input $x$, produces the output $y$."_
]

A _zero-knowledge virtual machine_ (zkVM) produces such proofs for arbitrary
programs, written in ordinary programming languages and compiled to a
standard instruction set, rather than for computations written by hand as
constraints. ZisK @ZISK:WHITEPAPER is such a system, for programs compiled
to RISC-V and translated into the ZisK instruction set. Its prover does not
produce one monolithic proof of the entire execution. ZisK splits the work
of the VM among a fixed family of _chips_, each in charge of one kind of
operation (e.g., the main loop, memory or the arithmetic), and splits
the execution of each chip into segments; every segment is proved by a
succinct argument for its chip; and the proofs are aggregated by a tree of
recursive verifiers whose root checks that the segments fit together. The
verifier receives a single proof, the _final proof_, together with the
public statement it attests to.

The security of such a system is not the security of its textbook
components. Each layer departs from the construction whose analysis it would
like to inherit: the interactive oracle proof (IOP) behind every argument is
made non-interactive with a transcript that does not observe everything the
verifier reads, the segment proofs share a bus key derived once for the
whole execution, the recursive verifiers switch verification on and off
depending on the shape of the tree, and the bus contributions of the
segments are checked only once, summed, at the root. A gap in any of these
places can make an accepting proof certify nothing, while every component
remains sound on its own. This paper states precisely what an accepting
final proof of ZisK certifies, and proves it for the protocol as deployed,
under explicit assumptions on the primitives.

== What ZisK Proves <sec:intro-statement>

The claim above cannot be what the final proof certifies as it stands.
Delegation pays off only if checking the proof is much cheaper than running
the program, and to check the claim the verifier would have to read $P$ and
$x$. Moreover, $x$ is often the part of the computation that the prover
wants to keep private. ZisK therefore proves a refinement of the claim,
obtained by revisiting each of its three components and adding a fourth.

*The program.* ZisK proves executions of programs for the ZisK instruction
set, a machine with registers and a byte-addressed memory, into which RISC-V
programs are translated; a program starts from a fixed initial state. A
program can be megabytes long, so the verifier does not receive $P$ but a
short _commitment_ to it, a value computed from its code such that no one can
find a different program with the same value. A verifier that knows which
program it expects, for instance because its developer published the
commitment, compares the commitment with that value, and the proof then
speaks about that program and no other.

*The input.* The input $x$ is supplied before the program starts. It may be
large, such as a batch of transactions, or secret, such as a signing key, and
in either case it should not be sent to the verifier. The claim therefore
does not fix $x$ but quantifies over it: the proof says that _some_ input
leads to the output. Whatever the verifier must know about $x$ has to be
revealed by the program itself, for instance by outputting a hash of it.

*The output.* A program has no single output: when it halts, all of its
memory is a candidate. ZisK lets the program _declare public outputs_ while
it runs, the values it chooses to reveal, and $y$ is the sequence of these
values.

*The hints.* To run efficiently, a program may request values from the
prover while it runs, its _hints_, typically the result of a costly
computation that the program then checks, such as a square root that it
verifies by squaring. Hints do not appear in the original claim and come from
an untrusted source, so the claim quantifies over them as it does over the
input. Neither kind of data is trusted: the program must behave correctly
whatever values it receives, and checking the hints is the responsibility
of the program, not of ZisK.

*The public statement.* A proof is therefore checked against a short _public
statement_ $bold(p)$ made of two parts: the public outputs $y$ and the
commitment to $P$. The input and the hints stay with the prover. What a
proof claims is:

#quote(block: true)[
  _There exist an input $x$ and a sequence of hints on which the committed
  program $P$, started from its initial state, runs according to the
  semantics of the ZisK instruction set until it halts, and declares exactly
  the public outputs $y$ of $bold(p)$._
]

We formalize this claim as a relation $cal(R)_"exec"$ whose witness is the
whole execution: the program, the input, the hints and the sequence of
machine states (#fwd(<sec:exec-relation>)[Part III]). The claim concerns the committed ZisK
program; its connection to the original RISC-V binary rests on the
correctness of the transpiler, which we assume.

#theorem(title: "Main Theorem, Informal")[
  For every efficient adversary that makes
  at most $Q$ queries to the random oracles and outputs $bold(p)$
  with a final proof that the verifier accepts, an
  extractor outputs a witness of $cal(R)_"exec"$ for $bold(p)$,
  except with probability at most the sum of:
  - The knowledge-soundness errors of the arguments proving the nodes of
    the aggregation tree, each at most $Q$ times the largest round-by-round
    error of its IOP.
  - The soundness error of the bus argument at a key derived after the
    leaves are committed, for each of the $Q$ queries.
  - The extraction errors of the challenge accumulator and of the commitments.
] <thm:intro>

The proof of @thm:intro retraces, in reverse, the way ZisK builds a proof: from
the final proof it recovers a proof for every segment, from each of these
proofs a valid trace of its segment, and from the traces an execution of the
program (@fig:layers).

#figure(
  {
    set text(size: 8pt)
    set par(justify: false)
    let stage(pos, body) = node(
      pos,
      align(center, body),
      stroke: 0.5pt + luma(120),
      inset: 6pt,
      corner-radius: 2pt,
      width: 2.7cm,
    )
    let lbl(body) = text(size: 7.5pt, body)
    diagram(
      spacing: (1.6cm, 1cm),
      stage((0, 0), [an execution \ of the program]),
      stage((1, 0), [segment traces, \ one per chip]),
      stage((2, 0), [a proof \ for every segment]),
      stage((3, 0), [one final proof]),
      // How ZisK builds a proof.
      edge((0, 0), (1, 0), "-|>", lbl[split], label-side: left),
      edge((1, 0), (2, 0), "-|>", lbl[prove], label-side: left),
      edge((2, 0), (3, 0), "-|>", lbl[aggregate], label-side: left),
      // What the analysis recovers.
      edge((3, 0), (2, 0), "--|>", lbl[Part II], bend: 50deg, label-side: left),
      edge((2, 0), (1, 0), "--|>", lbl[Part I], bend: 50deg, label-side: left),
      edge((1, 0), (0, 0), "--|>", lbl[Part III], bend: 50deg, label-side: left),
    )
  },
  caption: [How ZisK proves an execution (solid arrows) and how the analysis
    recovers one from an accepted final proof (dashed arrows). Part IV
    composes the three steps.],
) <fig:layers>

*Part I: The Proving System.* Every chip and every recursive verifier of
ZisK is proved with the same protocol: an IOP that checks the constraints of
its chip, compiled into a succinct
argument with Merkle trees and the Fiat–Shamir transformation. The compilation is where ZisK departs from the
textbook: the bus key and the first stage of every chip proof are bound
through the global challenge rather than through the proof's own
transcript. A prover that could choose its first-stage columns after the
out-of-domain sample could satisfy the constraint check with any trace, so
the binding lemma, which combines preimage awareness of the accumulator with
extractability of the Merkle trees, is what makes the chip proofs sound.

*Part II: The Recursion.* Each node of the aggregation tree carries a leaf
counter, a homomorphic hash of the leaves' typed commitments, and the sum of
their bus contributions; the root of the tree checks that the bus key was
derived from the hash and that the contributions, with the global messages
of the statement, sum to zero. The analysis descends the tree with one
extraction game per layer, and a zero test at a key derived after the
leaves are fixed turns the root check into balance of every bus.

*Part III: The Semantics.* A balanced collection of locally satisfying
witnesses of the ZisK chips encodes an execution: the memory argument
reconstructs the memory, the continuation buses stitch the segments of each
chip into one sequence, and the constraints of the Main chip and of the
chips it delegates to implement one step of the instruction set. The decoding
is deterministic and involves no cryptography.

*Part IV: Composition.* The last part composes the three steps into
#fwd(<thm:final>)[the main theorem] and records, in a ledger, every assumption the theorem rests on
and every obligation left open.

// == Our Contributions <sec:intro-contributions>

// Our first contribution is a precise statement of what ZisK proves. We
// formalize the claim of a proof as a relation $cal(R)_"exec"$ between the
// public statement and a full execution of the committed program
// (@sec:intro-statement), and prove that ZisK is a knowledge-sound argument
// for it (#fwd(<thm:final>)[Part IV]), with an explicit error and explicit assumptions.

// Second, we analyze the protocol that proves every chip and every recursive verifier of ZisK as it is
// deployed. We specify it as an interactive oracle proof and prove its
// round-by-round knowledge soundness (#fwd(<thm:iop-rbr>)[Part I]), with an explicit error for
// every round: the constraint combination, the out-of-domain sample, the DEEP
// batching with two challenges, folding of arbitrary arity, and the query
// phase. We then bound the knowledge-soundness error of its compilation with
// ZisK's Fiat–Shamir transcript, grinding and query derivation (#context if query(<thm:bcs>).len() > 0 [@thm:bcs, @lem:grinding] else [Part I]). The compilation departs from the textbook in one essential
// way: the transcript of an AIR proof does not observe its first-stage
// commitment, which is instead hashed into the key shared by all the AIR proofs
// of an execution. We show that, as a consequence, a single AIR proof is not
// knowledge-sound (#fwd(<rem:standalone>)[Part I]), but that the AIR proofs of an aggregation
// tree are, jointly (#fwd(<lem:binding>)[Part I]).

// Third, we analyze the recursion. We abstract the bus argument as a
// fingerprint of a multiset of messages and the per-node bookkeeping as
// accumulators, and prove that an accepting final proof yields a collection of
// locally satisfying AIR witnesses that together balance every bus
// (#fwd(<thm:main>)[Part II]). The result is stated for the abstractions and instantiated with
// LogUp and LtHash. We then show that such a collection encodes an execution
// of the committed program, by a deterministic decoding that adds no error
// (Part III).

// Finally, the relations attested by the recursive verifiers are stated as
// conditions that can be checked against the implementation, so that the
// analysis doubles as a specification of what the recursive verifiers must enforce.

// == Model and Limitations <sec:idealized>

// The analysis is carried out in the random-oracle model and is idealized in
// two respects (@rem:idealized). It assumes that straight-line extraction
// composes across the layers of the recursion, which does not hold for
// succinct arguments in general, and that the accumulator of the leaves'
// commitments is preimage aware, which is not known to follow from standard
// assumptions for an algebraic multiset hash. The bounds should therefore be
// read as statements about the structure of the reductions rather than as a
// concrete security level.

// == Organization

// @sec:preliminaries fixes the notation and the security definitions, and
// @sec:system describes the ZisK proof system. Parts I to IV follow, and the
// appendices collect the parameters of every argument, the constraint audits of
// the chips, deferred proofs and an index of notation.
