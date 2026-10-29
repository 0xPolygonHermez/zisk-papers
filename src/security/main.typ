#import "../style.typ": article, title-page, zisk-version

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
  strong(it)
}

// Remove background fill from top-level outline entries
#show outline.entry.where(level: 1): set outline.entry(fill: none)

#outline(depth: 2)
#pagebreak()

// A part groups several sections: an unnumbered, outlined heading that starts
// on a new page.
#let part(label-name, title) = {
  pagebreak(weak: true)
  [#heading(level: 1, numbering: none, outlined: true, title) #label(label-name)]
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

// Parts II-IV are not part of this version yet; they are kept here, commented
// out, to be restored as they are completed.
/*
#part("part:recursion", [Part II: Recursion])

= Overview of the Recursion Analysis <sec:recursion-overview>

#include "contents/part2/overview.typ"

= From the Root Check to Bus Balancing <sec:bus>

#include "contents/part2/bus.typ"

= Descending the Aggregation Tree <sec:lemmas>

#include "contents/part2/descent.typ"

= Main Theorem of the Recursion <sec:theorem>

#include "contents/part2/theorem.typ"

#part("part:semantics", [Part III: Semantics])

= The Execution Relation <sec:exec-relation>

#include "contents/part3/exec.typ"

= Bus Semantics <sec:per-bus>

#include "contents/part3/buses.typ"

= Memory <sec:memory>

#include "contents/part3/memory.typ"

= Segmentation and Stitching <sec:stitching>

#include "contents/part3/stitching.typ"

= Chips <sec:chips>

#include "contents/part3/chips.typ"

= Word Encoding <sec:encoding>

#include "contents/part3/encoding.typ"

= Reconstructing the Execution <sec:theorem-iii>

#include "contents/part3/theorem.typ"

#part("part:composition", [Part IV: Composition])

= Main Theorem <sec:composition>

#include "contents/part4/composition.typ"

= Ledger <sec:discussion>

#include "contents/part4/ledger.typ"

= Limitations <sec:limitations>

#include "contents/part4/limitations.typ"

*/

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
