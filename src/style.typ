// The ZisK release these documents describe. Both papers carry it as a
// footnote on the title, so there is a single place to bump.
#let zisk-version = footnote[
  This document describes ZisK v0.16.1 [48cf7cc -- 2026-20-03]. \
  ~~~~~ Source code available at #link("https://github.com/0xPolygonHermez/zisk").
]

// Stand-alone title page
#let title-page(
  title: none,
  authors: (),
  date: none,
  abstract: none,
  keywords: (),
  paper-size: "us-letter",
  margin: 1in,
  font: "Libertinus Serif",
  mono-font: "New Computer Modern Mono",
) = {
  set page(
    paper: paper-size,
    margin: margin,
    header: none,
    footer: none,
    numbering: none,
  )
  set text(font: font, size: 11pt)
  set par(justify: true)
  counter(page).update(0)

  v(1em)
  align(center, text(size: 22pt, title))
  v(2em)

  let author-cell(a) = align(center, {
    text(size: 12pt, a.name)
    if "email" in a {
      linebreak()
      text(font: mono-font, size: 9.5pt, a.email)
    }
    if "affiliation" in a {
      linebreak()
      a.affiliation
    }
  })
  if authors.len() > 0 {
    align(center, grid(
      columns: calc.min(authors.len(), 2),
      column-gutter: 4em,
      row-gutter: 2.2em,
      ..authors.map(author-cell),
    ))
  }

  if date != none {
    v(1.5em)
    align(center, text(size: 12pt, date))
  }

  if abstract != none {
    v(2.2em)
    align(center, text(size: 12pt, weight: "bold")[Abstract])
    v(0.6em)
    block({
      set par(first-line-indent: (amount: 1.5em, all: true), spacing: 0.65em)
      abstract
    })
  }

  if keywords.len() > 0 {
    v(1.2em)
    [*Keywords*: #keywords.join("; ")]
  }
}

// Sizes of the AMS template.
#let script-size = 7.97224pt
#let footnote-size = 8.50012pt
#let small-size = 9.24994pt
#let normal-size = 10.00002pt

// Article body, adapted from `@preview/unequivocal-ams:0.1.2` (MIT-0).
#let article(
  // Used for the PDF metadata only.
  title: none,
  authors: (),
  paper-size: "us-letter",
  margin: 1in,
  font: "Libertinus Serif",
  size: 11pt,
  // The result of a call to the `bibliography` function or `none`.
  bibliography: none,
  body,
) = {
  set document(title: title, author: authors)
  set text(size: size, font: font)

  set page(
    paper: paper-size,
    margin: margin,
    header: none,
    footer-descent: 12pt,
    footer: context align(center, text(size: script-size, counter(page).display())),
  )

  // Headings: level 1 left-aligned and bold, and resets the theorem counter;
  // deeper levels run in, bold for level 2 and italic below.
  set heading(numbering: "1.")
  show heading: it => {
    let number = if it.numbering != none {
      counter(heading).display(it.numbering)
      h(7pt, weak: true)
    }
    set text(size: normal-size, weight: 400)
    set par(first-line-indent: 0em)
    if it.level == 1 {
      counter(figure.where(kind: "theorem")).update(0)
      set align(left)
      block(above: 20pt, below: 12pt, text(size: 13pt, weight: "bold", {
        if it.numbering != none {
          counter(heading).display(it.numbering)
          h(0.5em)
        }
        it.body
      }))
    } else {
      v(11pt, weak: true)
      number
      let styled = if it.level == 2 { strong } else { emph }
      styled(it.body + [. ])
      h(7pt, weak: true)
    }
  }

  // Lists and equations.
  set list(indent: 24pt, body-indent: 5pt)
  set enum(indent: 24pt, body-indent: 5pt)
  show math.equation: set block(below: 8pt, above: 9pt)
  show math.equation: set text(weight: 400)

  // Citation and bibliography styles.
  set std.bibliography(style: "springer-mathphys", title: [References])

  // Figures: small-caps supplement in captions, a little room around tables
  // and images.
  set figure(gap: 17pt)
  show figure: set block(above: 12.5pt, below: 15pt)
  show figure: it => {
    show figure.caption: caption => {
      smallcaps(caption.supplement)
      if caption.numbering != none {
        [ ]
        numbering(caption.numbering, ..caption.counter.at(it.location()))
      }
      [. ]
      caption.body
    }
    show selector.or(table, image): pad.with(x: 23pt)
    it
  }

  // Theorem-like figures are left-aligned blocks, not centred figures (a
  // figure would otherwise centre the text inside it).
  show figure.where(kind: "theorem"): set align(start)
  show figure.where(kind: "remark"): set align(start)

  set par(spacing: 0.58em, first-line-indent: 1.2em, justify: true, leading: 0.58em)

  body

  if bibliography != none {
    show std.bibliography: set text(footnote-size)
    show std.bibliography: set block(above: 11pt)
    show std.bibliography: pad.with(x: 0.5pt)
    bibliography
  }
}
