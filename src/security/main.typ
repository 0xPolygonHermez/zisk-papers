#import "../style.typ": article, title-page

// Page geometry
#let margin = 1in
#let title-margin = (
  top: (116pt / 279mm) * 100%,
  left: (126pt / 216mm) * 100%,
  right: (128pt / 216mm) * 100%,
  bottom: (94pt / 279mm) * 100%,
)

#title-page(
  margin: title-margin,
  title: [ZisK's Recursion],
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
    This document analyzes the security of the recursive aggregation layer of
    ZisK. It first gives a self-contained statement of the relations proved by
    the AIR arguments, the leaf verifiers, the aggregation nodes and the Final
    Verifier. The bus argument that ties the AIR instances together is
    abstracted as an additive fingerprint of a weighted multiset of messages,
    and the per-node bookkeeping as accumulators over a commutative monoid;
    the LogUp running sum and the LtHash challenge accumulator of ZisK are
    instances of these notions.

    It then proves that any adversary producing an accepting Final proof for a
    public statement can be turned into an extractor that outputs a typed
    collection of AIR witnesses that are locally satisfying and bus balanced.
    The bound is an explicit sum of the knowledge-soundness errors of the four
    argument systems, weighted by the size of the unrolled aggregation tree,
    the soundness error of the fingerprint, the collision resistance of the
    challenge accumulator and the extractability of the trace commitment, in
    the random-oracle model. Two idealizations are made explicit, straight-line
    composition and the uniqueness of the accumulated multiset, and the
    assumptions inherited from the backend together with the obligations left
    for a complete proof are recorded in a ledger.
  ],
  keywords: (
    "zero-knowledge virtual machines",
    "recursive proof composition",
    "knowledge soundness",
    "lookup arguments",
  ),
)

#show: article.with(
  title: "ZisK's Recursion",
  authors: ("Héctor Masip-Ardevol",),
  margin: margin,
  bibliography: bibliography(("./refs.bib", "../whitepaper/refs.bib")),
)

// Monospace for URL links only; internal cross-references keep the text font.
#show link: it => if type(it.dest) == str {
  set text(font: "DejaVu Sans Mono")
  it
} else { it }

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
    link(loc, text(font: "Libertinus Serif", [#el.supplement #numbering("1.1", sec, n)]))
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

= Preliminaries and Recursive Relations <sec:relations>

#include "contents/relations.typ"

= Security <sec:security>

#include "contents/security.typ"
