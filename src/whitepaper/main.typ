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
  title: [ZisK Whitepaper#zisk-version],
  authors: (
    (
      name: "ZisK Core Team",
    ),
  ),
  // Fixed on purpose: the build script pins SOURCE_DATE_EPOCH for
  // reproducible PDFs, so `datetime.today()` would not give the real date.
  date: [September 14, 2026],
  abstract: [
    We present ZisK, a STARK-based zero-knowledge virtual machine (zkVM) that executes programs compiled from standard instruction set architectures and produces succinct, transparent proofs of their correct execution. ZisK targets the RISC-V ISA, allowing developers to use existing Rust and C toolchains without modification. Moreover, ZisK's modular architecture enables the addition of optimized constraint systems for expensive operations such as elliptic-curve arithmetic and bulk memory access, making it practical to prove complex computations at scale.

    This paper provides a precise specification of the ZisK design: its instruction set architecture, the arithmetization framework, the circuit architecture and chip design, the continuation mechanism, and the recursive aggregation system.
  ],
  // keywords: (
  //   "zero-knowledge virtual machines",
  //   "recursive proof composition",
  //   "knowledge soundness",
  //   "lookup arguments",
  // ),
)

#show: article.with(
  title: "ZisK Whitepaper",
  authors: ("ZisK Core Team",),
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

= Introduction <sec:introduction>

#include "contents/introduction.typ"

= Instruction Set Architecture <sec:isa>

#include "contents/isa.typ"

= Arithmetization Framework <sec:arithmetization>

#include "contents/arithmetization.typ"

= ZisK Design <sec:design>

#include "contents/design.typ"

= Continuations <sec:continuations>

#include "contents/continuations.typ"

= Recursion <sec:recursion>

#include "contents/recursion.typ"

#pagebreak()

#heading(outlined: false, numbering: none)[Acknowledgments]

This paper draws on the designs presented in the OpenVM @OPENVM and Nexus @NEXUS whitepapers, which served as important sources of inspiration. We also acknowledge RISC Zero @RISCZERO as a pioneering zkVM and SP1 @SP1 for advancing the practical deployment of RISC-V-based proving systems.

We extend our gratitude to the Polygon zkEVM and Plonky3 @PLONKY3 teams for their foundational work in zero-knowledge proving systems, as well as to the RISC-V community @RISCV for providing a robust architecture that enables the zkVM model.

#set heading(outlined: true)

#set std.bibliography(style: "springer-mathphys", title: [References])
#show std.bibliography: set text(8.50012pt)
#show std.bibliography: set block(above: 11pt)
#show std.bibliography: pad.with(x: 0.5pt)
#bibliography("refs.bib")

#pagebreak()

#heading(outlined: true, numbering: none)[Appendix]

// Set up appendix with custom heading style
#counter(heading).update(0)
#set heading(outlined: false, numbering: "A.", supplement: "Appendix")
#show heading.where(level: 2): set heading(numbering: none)

= Arguments <appendix:arguments>

#include "appendix/arguments.typ"
