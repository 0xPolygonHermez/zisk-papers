#import "@preview/unequivocal-ams:0.1.2": ams-article, proof, theorem
#import "lib.typ": definition

#show: ams-article.with(
  title: [ZisK Whitepaper#footnote[This document describes ZisK v0.16.1
      [48cf7cc -- 2026-20-03]. \ ~~~ Source code available at #link("https://github.com/0xPolygonHermez/zisk")[github.com/0xPolygonHermez/zisk].]],
  authors: (
    (
      name: "ZisK Core Team",
    ),
  ),
  abstract: [
    We present ZisK, a STARK-based zero-knowledge virtual machine (zkVM) that executes programs compiled from standard instruction set architectures and produces succinct, transparent proofs of their correct execution. ZisK targets the RISC-V ISA, allowing developers to use existing Rust and C toolchains without modification. Moreover, ZisK's modular architecture enables the addition of optimized constraint systems for expensive operations such as elliptic-curve arithmetic and bulk memory access, making it practical to prove complex computations at scale.

    This paper provides a precise specification of the ZisK design: its instruction set architecture, the arithmetization framework, the circuit architecture and chip design, the continuation mechanism, and the recursive aggregation system.
  ],
)

// Set text properties for the entire document
#set text(
  font: "Libertinus Serif",
  size: 11pt,
)

// Set bibliography style to alphanumeric
#set cite(style: "alphanumeric")

// Override AMS theorem styling to remove italic
#show figure.where(kind: "theorem"): it => block(spacing: 11.5pt, {
  strong({
    it.supplement
    if it.numbering != none {
      [ ]
      it.counter.display(it.numbering)
    }
    [.]
  })
  [ ]
  it.body
})

// Make top-level outline entries bold
#show outline.entry.where(level: 1): it => {
  strong(it)
}

// Remove background fill from top-level outline entries
#show outline.entry.where(level: 1): set outline.entry(fill: none)

#outline(depth: 1)

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

// TODO: Complete

// = RISC-V Support <sec:riscv>

// #include "contents/riscv.typ"

// = Proving System <sec:proving_system>

// #include "contents/proving_system.typ"

// = Conclusion <sec:conclusion>

// #include "contents/conclusion.typ"

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

// = ZisK Instruction Set <appendix:instructions>

// #include "appendix/isa-complete.typ"

// = ZisK Arithmetization <appendix:air_table>

// #include "appendix/pil.typ"
