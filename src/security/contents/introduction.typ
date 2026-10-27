#import "../../lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, game, lemma, mult, negl,
  poly, proof, proposition, remark, theorem, todo, vk,
)
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

A _zero-knowledge virtual machine_ (zkVM) proves statements of the form
"this program, run on some input, produces this output". ZisK
@ZISK:WHITEPAPER is such a system, for programs compiled to RISC-V and
translated into the ZisK instruction set. Its prover does not produce one
monolithic proof of the entire execution. The execution is split, chip by chip, into segments; every
segment is proved by a succinct argument for the AIR of its
chip; and the proofs are
aggregated by a tree of recursive verifiers whose root, the _Final
Verifier_, checks that the segments fit together. The external verifier sees
a single proof and the public statement it attests to.

The security of such a system is not the security of its textbook
components. Each layer departs from the construction whose analysis it would
like to inherit: the interactive oracle proof (IOP) behind every argument is
made non-interactive with a transcript that does not observe everything the
verifier reads, the AIR proofs share a bus
key derived once for the whole execution, the recursive circuits switch
verification on and off depending on the shape of the tree, and the bus
contributions of the segments are checked only once, summed, at the root. A gap in any of these places can make an accepting proof
certify nothing, while every component remains sound on its own. This paper
states precisely what an accepting final proof of ZisK certifies, and proves
it for the protocol as deployed, under explicit assumptions on the
primitives.

== What ZisK Proves <sec:intro-statement>

*Programs and their data.* ZisK proves executions of programs for the ZisK
instruction set, a machine with registers and a byte-addressed memory, into
which RISC-V programs are translated. A program starts from a fixed initial
state and reads two kinds of data. Its _input_ is supplied before it starts.
Its _hints_ are values it requests while running from an untrusted source,
the prover, typically the result of a costly computation that the program
then checks, such as a square root it verifies by squaring. Neither kind of
data is trusted: the program must behave correctly whatever values it
receives. While running, the program may also _declare public outputs_, the
values it chooses to reveal.

*The public statement.* A proof is checked against a short _public
statement_ $bold(p)$ made of two parts: the public outputs, and a
_commitment_ to the program, a short value computed from its code such that
no one can find a different program with the same value. The input and the
hints are not part of the statement; they stay with the prover. What a proof
claims is therefore existential:

#quote(block: true)[
  _There exist an input and a sequence of hints on which the committed
  program, started from its initial state, runs according to the semantics of
  the ZisK instruction set until it halts, and declares exactly the public
  outputs of $bold(p)$._
]

We formalize this claim as a relation $cal(R)_"exec"$ whose witness is the
whole execution: the program, the input, the hints and the sequence of
machine states (@sec:exec-relation). The claim concerns the committed ZisK
program; its connection to the original RISC-V binary rests on the
correctness of the transpiler, which we assume.

#theorem(title: "Main Theorem, Informal")[
  For every efficient adversary that makes
  at most $Q$ queries to the random oracles and outputs $bold(p)$
  with a final proof that the external verifier accepts, an
  extractor outputs a witness of $cal(R)_"exec"$ for $bold(p)$,
  except with probability at most the sum of:
  - The knowledge-soundness errors of the arguments proving the nodes of
    the aggregation tree, each at most $Q$ times the largest round-by-round
    error of its circuit.
  - The soundness error of the bus argument at a key derived after the
    leaves are committed, for each of the $Q$ queries.
  - The extraction errors of the challenge accumulator and of the commitments.
] <thm:intro>

The proof of @thm:intro descends from the Final Verifier to the execution in
three extraction steps, each the subject of one part of the paper
(@fig:layers).

#figure(
  {
    set text(size: 8pt)
    set par(justify: false)
    let box-node(pos, body) = node(
      pos,
      align(center, body),
      stroke: 0.5pt + luma(120),
      inset: 6pt,
      corner-radius: 2pt,
      width: 3cm,
    )
    diagram(
      spacing: (1.5cm, 0.9cm),
      box-node((0, 0), [accepting Final proof \ for $bold(p)$]),
      box-node((1, 0), [accepting proofs \ for every node]),
      box-node((2, 0), [$(bold(p)_"pv", L) in cal(R)_Zisk$: \ balanced, locally \ satisfying AIR witnesses]),
      box-node((3, 0), [$w_"exec"$ with \ $(bold(p)_"ext"; w_"exec") in cal(R)_"exec"$]),
      edge((0, 0), (1, 0), "->", [Part II], label-side: left),
      edge((1, 0), (2, 0), "->", [Parts I, II], label-side: left),
      edge((2, 0), (3, 0), "->", [Part III], label-side: left),
    )
  },
  caption: [The chain of extractions behind @thm:intro. Part IV composes the three steps.],
) <fig:layers>

*Part I: the proving system.* Every circuit of ZisK is proved with the same
protocol: an IOP that checks the constraints of the AIR, compiled into a succinct
argument with Merkle trees and the Fiat–Shamir transformation. We present
it in the style of @EC:ACFY25, as an IOP whose round-by-round soundness is
proved through a state function. Mutual correlated agreement makes the role
of every folding challenge explicit, and the query phase is handled by an
induction over the layers. The compilation is where ZisK departs from the
textbook: the bus key and the first stage of every AIR proof are bound
through the global challenge rather than through the proof's own
transcript. A prover that could choose its first-stage columns after the
out-of-domain sample could satisfy the constraint check with any trace, so
the binding lemma, which combines preimage awareness of the accumulator with
extractability of the Merkle trees, is what makes the AIR proofs sound.

*Part II: the recursion.* Each node of the aggregation tree carries a leaf
counter, a homomorphic hash of the leaves' typed commitments, and the sum of
their bus contributions; the Final Verifier checks that the bus key was
derived from the hash and that the contributions, with the global messages
of the statement, sum to zero. The analysis descends the tree with one
extraction game per layer, and a zero test at a key derived after the
leaves are fixed turns the root check into balance of every bus.

*Part III: the semantics.* A balanced collection of locally satisfying
witnesses of the ZisK chips encodes an execution: the memory argument
reconstructs the memory, the continuation buses stitch the segments of each
chip into one sequence, and the constraints of the Main chip and of the
chips it delegates to implement one step of the instruction set. The decoding
is deterministic and involves no cryptography.

*Part IV: composition.* The last part composes the three steps into
@thm:final and records, in a ledger, every assumption the theorem rests on
and every obligation left open.

== Our Contributions <sec:intro-contributions>

Our first contribution is a precise statement of what ZisK proves. We
formalize the claim of a proof as a relation $cal(R)_"exec"$ between the
public statement and a full execution of the committed program
(@sec:intro-statement), and prove that the final verifier is knowledge-sound
for it (@thm:final), with an explicit error and explicit assumptions.

Second, we analyze the protocol that proves every circuit of ZisK as it is
deployed. We specify it as an interactive oracle proof and prove its
round-by-round knowledge soundness (@thm:iop-rbr), with an explicit error for
every round: the constraint combination, the out-of-domain sample, the DEEP
batching with two challenges, folding of arbitrary arity, and the query
phase. We then bound the knowledge-soundness error of its compilation with
ZisK's Fiat–Shamir transcript, grinding and query derivation (@thm:bcs,
@lem:grinding). The compilation departs from the textbook in one essential
way: the transcript of an AIR proof does not observe its first-stage
commitment, which is instead hashed into the key shared by all the AIR proofs
of an execution. We show that, as a consequence, a single AIR proof is not
knowledge-sound (@rem:standalone), but that the AIR proofs of an aggregation
tree are, jointly (@lem:binding).

Third, we analyze the recursion. We abstract the bus argument as a
fingerprint of a multiset of messages and the per-node bookkeeping as
accumulators, and prove that an accepting final proof yields a collection of
locally satisfying AIR witnesses that together balance every bus
(@thm:main). The result is stated for the abstractions and instantiated with
LogUp and LtHash. We then show that such a collection encodes an execution
of the committed program, by a deterministic decoding that adds no error
(Part III).

Finally, the relations attested by the recursive circuits are stated as
conditions that can be checked against the implementation, so that the
analysis doubles as a specification of what the circuits must enforce.

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
// appendices collect the parameters of every circuit, the constraint audits of
// the chips, deferred proofs and an index of notation.
