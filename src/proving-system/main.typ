#import "@preview/unequivocal-ams:0.1.2": ams-article, proof, theorem
#import "../lib.typ": definition, remark, theorem-styles

#show: ams-article.with(
  title: [The Proving System of ZisK],
  authors: (
    (
      name: "ZisK Core Team",
    ),
  ),
  abstract: [
    TODO.
  ],
)

#set text(font: "New Computer Modern", size: 11pt)
#show link: set text(font: "DejaVu Sans Mono")
#set cite(style: "alphanumeric")

// Boxed definitions / italic remarks (shared styling from lib.typ).
#show: theorem-styles

#show outline.entry.where(level: 1): it => strong(it)
#show outline.entry.where(level: 1): set outline.entry(fill: none)

#outline(depth: 1)

= Introduction <sec:intro>

#include "contents/introduction.typ"

= Multilinear Arithmetization <sec:mle>

#include "contents/arithmetization.typ"

= Commitment Scheme <sec:commitment>

#include "contents/commitment.typ"

= The Zerocheck PIOP <sec:zerocheck>

#include "contents/zerocheck.typ"

= Opening the Committed Columns <sec:opening>

#include "contents/opening.typ"

= The Basic-Proof Protocol <sec:protocol>

#include "contents/protocol.typ"

#set std.bibliography(style: "springer-mathphys", title: [References])
#show std.bibliography: set text(8.5pt)
#bibliography("refs.bib")
