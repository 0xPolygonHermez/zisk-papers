#import "../shared/style.typ": paper, part, references
#import "../shared/lib.typ": Com, remark

#show: paper.with(
  title: "Security of ZisK",
  authors: (
    (
      name: "Héctor Masip-Ardevol",
      email: "hector@zisk.technology",
      affiliation: "ZisK Core Team",
    ),
  ),
  // Fixed on purpose: the build script pins SOURCE_DATE_EPOCH for
  // reproducible PDFs, so `datetime.today()` would not give the real date.
  date: [September 14, 2026],
  abstract: [
    This document analyzes the security of ZisK's proof system, from the
    proof of a single chip to the statement about program execution that a
    final proof certifies. It is organized in four parts. Part I describes the
    proving system as implemented and bounds the knowledge soundness of every
    argument it uses. Part II analyzes the recursive aggregation layer: the bus
    argument that ties the AIR instances together is abstracted as an additive
    fingerprint of a weighted multiset of messages, and the per-node
    bookkeeping as accumulators over a commutative monoid; from any adversary
    producing an accepting final proof, an extractor obtains a bounded
    collection of locally satisfying, bus-balanced AIR witnesses. Part III
    states, and partly proves, that such a collection encodes a successful
    execution of the committed program. Part IV composes the three into the
    main theorem: for a fixed valid program, the final argument is
    knowledge-sound for ZisK's execution relation, with an explicit error
    bound. The idealizations made, the assumptions inherited from the
    primitives and the obligations left open are recorded in a ledger.
  ],
)

= Introduction <sec:introduction>

#include "contents/introduction.typ"

= Preliminaries <sec:preliminaries>

#include "contents/preliminaries.typ"

= The ZisK Proof System <sec:system>

#include "contents/system.typ"

#part("part:proving-system", [Part I: The Proving System])

= The ZisK Proving Protocol <sec:stark>

#include "contents/part1/stark.typ"

= Non-Interactive Compilation and Extraction <sec:compilation>

#include "contents/part1/compilation.typ"

= Knowledge Soundness of the Arguments <sec:theorem-i>

#include "contents/part1/theorem.typ"

#part("part:recursion", [Part II: Recursion])

We prove that the ZisK aggregation tree is _correct-witness extractable_: any
adversary that produces an accepting final proof for an external statement
$bold(p)_"ext"$ can be used to extract, in a straight-line fashion, proof
values $bold(p)_"pv"$ and a typed witness collection $L$ such that every witness
satisfies its AIR and is consistent with $bold(p) = (bold(p)_"ext", bold(p)_"pv")$, and
every bus balances across the whole collection together with the global
messages of $bold(p)$. The proof
descends the aggregation tree of @sec:tree layer by layer, reducing
everything to the guarantees of the argument systems of ZisK established in
Part I (@thm:arguments), the straight-line extractability of the trace commitment $Com$, the preimage
awareness of the accumulator $cal(H)$, and the soundness of the bus
fingerprint.

This part follows the reference architecture of the EF zkVM security sprint
@EF:VanillaVM in structure as well as in method: a bridging proposition, one
extraction game and lemma per layer of the recursion, and a main theorem whose
bound is an explicit sum over those lemmas; the idealized-model remark and the
definitions of the assumptions are in @sec:preliminaries. Where ZisK departs from that architecture,
the departure is flagged at the point where it matters.

#remark(title: "Scope")[
  The target relation of this part speaks about AIR witnesses, not about
  guest executions: it is the recursion layer of the chain that leads from an
  accepting final proof to a correct execution of the guest program. The
  semantic layer (that a balanced collection of locally satisfying witnesses
  encodes a single execution of the committed program, including the memory
  argument and continuation stitching) is Part III; completeness, zero
  knowledge and any wrapper placed above the Final Verifier are outside the
  analysis (@sec:discussion).
]

= From the Root Check to Bus Balancing <sec:bus>

#include "contents/part2/bus.typ"

= Descending the Aggregation Tree <sec:lemmas>

#include "contents/part2/descent.typ"

= Main Theorem of the Recursion <sec:theorem>

#include "contents/part2/theorem.typ"

#part("part:semantics", [(WIP) Part III: Semantics])

What a ZisK proof claims is the execution relation $cal(R)_"exec"$ of the
whitepaper @ZISK:WHITEPAPER, which formalizes the claim of
@sec:intro-statement. Part III states, and partly proves, that a balanced
collection of locally satisfying witnesses encodes a witness of this relation;
@sec:exec-relation recalls what such a witness is and how its words are
carried by field elements.

= Executions and Words <sec:exec-relation>

#include "contents/part3/exec.typ"

= Bus Semantics <sec:per-bus>

#include "contents/part3/buses.typ"

= Chips <sec:chips>

#include "contents/part3/chips.typ"

= Segmentation and Stitching <sec:stitching>

#include "contents/part3/stitching.typ"

= Memory <sec:memory>

#include "contents/part3/memory.typ"

= Reconstructing the Execution <sec:theorem-iii>

#include "contents/part3/theorem.typ"

#part("part:composition", [(WIP) Part IV: Composition])

= Main Theorem <sec:composition>

#include "contents/part4/composition.typ"

= Ledger and Limitations <sec:discussion>

#include "contents/part4/ledger.typ"

#pagebreak()

#references()
