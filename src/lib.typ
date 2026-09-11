#let definition(body, title: none, numbered: true) = figure(
  body,
  kind: "theorem",
  supplement: [Definition],
  numbering: if numbered { "1" } else { none },
  caption: if title != none { title } else { none },
)

#let remark(body, title: none, numbered: false) = figure(
  body,
  kind: "remark",
  supplement: [Remark],
  numbering: if numbered { "1" } else { none },
  caption: if title != none { title } else { none },
)

#let assumption(body, title: none, numbered: true) = figure(
  body,
  kind: "theorem",
  supplement: [Assumption],
  numbering: if numbered { "1" } else { none },
  caption: if title != none { title } else { none },
)

#let lemma(body, title: none, numbered: true) = figure(
  body,
  kind: "theorem",
  supplement: [Lemma],
  numbering: if numbered { "1" } else { none },
  caption: if title != none { title } else { none },
)

#let theorem(body, title: none, numbered: true) = figure(
  body,
  kind: "theorem",
  supplement: [Theorem],
  numbering: if numbered { "1" } else { none },
  caption: if title != none { title } else { none },
)

#let proposition(body, title: none, numbered: true) = figure(
  body,
  kind: "theorem",
  supplement: [Proposition],
  numbering: if numbered { "1" } else { none },
  caption: if title != none { title } else { none },
)

#let _theorem-head(it) = strong({
  it.supplement
  if it.numbering != none {
    [ ]
    it.counter.display(it.numbering)
  }
  if it.caption != none {
    [ (]
    it.caption.body
    [)]
  }
  [.]
})

#let theorem-styles(doc) = {
  show figure.where(kind: "theorem"): it => block(
    spacing: 11.5pt,
    width: 100%,
    stroke: 0.5pt + luma(120),
    radius: 3pt,
    inset: (x: 10pt, y: 8pt),
    {
      _theorem-head(it)
      [ ]
      it.body
    },
  )
  show figure.where(kind: "remark"): it => block(
    spacing: 11.5pt,
    align(left, emph({
      _theorem-head(it)
      [ ]
      it.body
    })),
  )
  doc
}
