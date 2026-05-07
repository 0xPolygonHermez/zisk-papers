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
