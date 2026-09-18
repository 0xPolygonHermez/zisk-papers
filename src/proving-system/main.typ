#import "../style.typ": article, title-page, zisk-version

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
  title: [ZisK's Proving System#zisk-version],
  authors: (
    (
      name: "Héctor Masip-Ardevol",
      email: "hector@zisk.technology",
      affiliation: "ZisK Core Team",
    ),
  ),
  // Fixed on purpose: the build script pins SOURCE_DATE_EPOCH for
  // reproducible PDFs, so `datetime.today()` would not give the real date.
  date: [September 18, 2026],
  abstract: [
    This document specifies the argument system that ZisK uses for every proof
    it produces, and analyses its soundness. The protocol is a STARK in the
    DEEP-ALI + FRI family: a multi-stage algebraic commitment to the execution
    trace, a random aggregation of the constraints into a single quotient, an
    out-of-domain consistency check, and a low-degree test of the resulting
    batch by FRI, compiled into a non-interactive argument by the Fiat--Shamir
    transform in the random-oracle model.

    The specification is parametrised by a configuration record, and the whole
    of ZisK --- the AIR proofs of the execution segments, the leaf verifiers,
    the aggregation nodes and the Final Verifier --- is this one protocol
    instantiated at different configurations. What distinguishes the layers is
    the AIR they are given, not the protocol that proves it. The analysis is
    therefore carried out once, for an arbitrary AIR and configuration, and the
    recursion is left to instantiate it.
  ],
)

#show: article.with(
  title: "ZisK's Proving System",
  authors: ("Héctor Masip-Ardevol",),
  margin: margin,
  bibliography: bibliography(("./refs.bib", "../security/refs.bib", "../whitepaper/refs.bib")),
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

= Preliminaries <sec:prelim>

#include "contents/preliminaries.typ"

= The Protocol <sec:protocol>

#include "contents/protocol.typ"

= Soundness <sec:soundness>

#include "contents/soundness.typ"

#pagebreak()
