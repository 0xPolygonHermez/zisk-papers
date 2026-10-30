#import "../style.typ": article, title-page, zisk-version
#import "../lib.typ": Com, remark

// Page geometry
#let margin = 1in
#let title-margin = (
  top: (116pt / 279mm) * 100%,
  left: (126pt / 216mm) * 100%,
  right: (128pt / 216mm) * 100%,
  bottom: (94pt / 279mm) * 100%,
)

#let body-font = "New Computer Modern"
#show math.equation: set text(font: "New Computer Modern Math")

#title-page(
  margin: title-margin,
  font: body-font,
  title: [Security of ZisK#zisk-version],
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
    final proof certifies. It is organized in three parts that compose. Part I
    describes the proving system as implemented and bounds the knowledge
    soundness of every argument it uses. Part II analyzes the recursive aggregation
    layer: the bus argument that ties the AIR instances together is abstracted
    as an additive fingerprint of a weighted multiset of messages, and the
    per-node bookkeeping as accumulators over a commutative monoid, and any
    adversary producing an accepting Final proof is turned into an extractor
    that outputs a bounded collection of locally satisfying, bus-balanced AIR
    witnesses. Part III shows that such a collection encodes a successful
    execution of the committed program. The composition yields the knowledge
    soundness of the final verifier for ZisK's execution relation, with an
    explicit error bound. The idealizations made, the assumptions inherited
    from the primitives and the obligations left open are recorded in a ledger.
  ],
  // keywords: (
  //   "zero-knowledge virtual machines",
  //   "recursive proof composition",
  //   "knowledge soundness",
  //   "lookup arguments",
  // ),
)

#show: article.with(
  font: body-font,
  title: "Security of ZisK",
  authors: ("Héctor Masip-Ardevol",),
  margin: margin,
  // The bibliography is placed by hand below, before the appendix.
  bibliography: none,
)

// Set bibliography style to alphanumeric
#set cite(style: "alphanumeric")

// Theorem-like environments (definitions, lemmas, propositions, theorems)
// share one counter, which the AMS template resets at every top-level
// heading. They are therefore displayed and referenced as "Definition 2.3".
// Remarks have their own counter, reset in the same way.
#let sec-numbering(n) = numbering("1.1", counter(heading).get().first(), n)

// The remark counter restarts at every top-level heading, like the theorem
// counter (which `article` resets).
#show heading.where(level: 1): it => {
  counter(figure.where(kind: "remark")).update(0)
  it
}

#show ref: it => {
  let el = it.element
  if el != none and el.func() == figure and (el.kind == "theorem" or el.kind == "remark") {
    let loc = el.location()
    let sec = counter(heading).at(loc).first()
    let n = counter(figure.where(kind: el.kind)).at(loc).first()
    link(loc, text(font: body-font, [#el.supplement #numbering("1.1", sec, n)]))
  } else {
    it
  }
}

// Long games and proofs must be allowed to break across pages.
#show figure.where(kind: "theorem"): set block(breakable: true)
#show figure.where(kind: "remark"): set block(breakable: true)
#show figure.where(kind: table): set block(breakable: true)

// Theorem-like environments: bold head, upright body for definitions, italic
// body for theorems, lemmas, propositions and corollaries.
#let italic-envs = ([Theorem], [Lemma], [Proposition], [Corollary])
#show figure.where(kind: "theorem"): it => block(width: 100%, spacing: 11.5pt, breakable: true, {
  strong({
    it.supplement
    if it.numbering != none {
      [ ]
      it.counter.display(sec-numbering)
    }
    if it.caption != none {
      [ (]
      it.caption.body
      [)]
    }
    [.]
  })
  [ ]
  if it.supplement in italic-envs { emph(it.body) } else { it.body }
})

// Italic styling for remarks (including title)
#show figure.where(kind: "remark"): it => block(width: 100%, spacing: 11.5pt, breakable: true, align(left, emph({
  strong({
    it.supplement
    if it.numbering != none {
      [ ]
      it.counter.display(sec-numbering)
    }
    if it.caption != none {
      [ (]
      it.caption.body
      [)]
    }
    [.]
  })
  [ ]
  it.body
})))

// Make top-level outline entries bold
#show outline.entry.where(level: 1): it => {
  if it.element.supplement == [Part] {
    block(above: 1.3em, below: .8em, text(size: 1.12em, strong(it)))
  } else {
    strong(it)
  }
}

// Remove background fill from top-level outline entries
#show outline.entry.where(level: 1): set outline.entry(fill: none)

#outline(depth: 2)
#pagebreak()

// A part groups several sections: an unnumbered, outlined heading that starts
// on a new page.
#let part(label-name, title) = {
  pagebreak(weak: true)
  show heading: it => block(above: 20pt, below: 14pt, text(size: 16pt, weight: "bold", it.body))
  [#heading(level: 1, numbering: none, outlined: true, supplement: [Part], title) #label(label-name)]
}

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
adversary that produces an accepting Final proof for an external statement
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
@EF:VanillaVM in structure as well as in method: an idealized-model remark,
the definitions of the assumptions, a bridging proposition, one extraction
game and lemma per layer of the recursion, and a main theorem whose bound is
an explicit sum over those lemmas. Where ZisK departs from that architecture,
the departure is flagged at the point where it matters.

#remark(title: "Scope")[
  The target relation of this part speaks about AIR witnesses, not about
  guest executions: it is the recursion layer of the chain that leads from an
  accepting final proof to a correct execution of the guest program. Not
  covered here, and left as named obligations, are the semantic layer (that a
  balanced collection of locally satisfying witnesses encodes a single
  execution of the committed program, including the memory argument and
  continuation stitching), completeness, zero knowledge, and any wrapper
  placed above the Final Verifier.
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
@sec:intro-statement. Part III shows that a balanced collection of locally
satisfying witnesses encodes a witness of this relation, and this chapter
recalls what such a witness is and how its words are carried by field
elements.

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

#set std.bibliography(title: [References])
#show std.bibliography: set text(8.50012pt)
#show std.bibliography: set block(above: 11pt)
#show std.bibliography: pad.with(x: 0.5pt)
#bibliography(("refs.bib", "../whitepaper/refs.bib"))

// The appendices are not part of this version yet.
/*
#pagebreak()

#heading(outlined: true, numbering: none)[Appendix]

#counter(heading).update(0)
#set heading(outlined: false, numbering: "A.", supplement: "Appendix")
#show heading.where(level: 1): set heading(outlined: true)
#show heading.where(level: 2): set heading(numbering: none)

= Parameters <app:parameters>

#include "appendix/parameters.typ"

= Constraint Audits <app:audits>

#include "appendix/audits.typ"

= Deferred Proofs <app:proofs>

#include "appendix/proofs.typ"

= Notation <app:notation>

#include "appendix/notation.typ"
*/
