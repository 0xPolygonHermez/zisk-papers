// The ZisK release these documents describe.
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

  show link: it => if type(it.dest) == str {
    set text(font: "DejaVu Sans Mono", size: 0.85em)
    it
  } else { it }
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
  // List markers available in every text font.
  set list(marker: ([•], [–], [∗]))

  // Monospace for URL links only; internal cross-references keep the text font.
  show link: it => if type(it.dest) == str {
    set text(font: "DejaVu Sans Mono", size: 0.85em)
    it
  } else { it }

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

// Page geometry and fonts of both papers.
#let body-font = "New Computer Modern"
#let page-margin = 1in
#let title-margin = (
  top: (116pt / 279mm) * 100%,
  left: (126pt / 216mm) * 100%,
  right: (128pt / 216mm) * 100%,
  bottom: (94pt / 279mm) * 100%,
)

// Theorem-like environments (definitions, lemmas, propositions, theorems)
// share one counter, which the AMS template resets at every top-level
// heading. They are therefore displayed and referenced as "Definition 2.3".
// Remarks have their own counter, reset in the same way.
#let sec-numbering(n) = numbering("1.1", counter(heading).get().first(), n)

// Theorem-like environments: bold head, upright body for definitions, italic
// body for theorems, lemmas, propositions and corollaries.
#let italic-envs = ([Theorem], [Lemma], [Proposition], [Corollary])

// A paper: title page, article body, environments and table of contents.
// `authors` are given as for `title-page`; `title` is a string, used for the
// PDF metadata and, followed by the version footnote, on the title page.
#let paper(title: none, authors: (), date: none, abstract: none, body) = {
  show math.equation: set text(font: "New Computer Modern Math")

  title-page(
    font: body-font,
    margin: title-margin,
    title: [#title#zisk-version],
    authors: authors,
    date: date,
    abstract: abstract,
  )

  show: article.with(
    font: body-font,
    title: title,
    authors: authors.map(a => a.name),
    margin: page-margin,
    // The bibliography is placed by hand, with `references`.
    bibliography: none,
  )

  set cite(style: "references.csl")

  // The remark counter restarts at every top-level heading, like the theorem
  // counter (which `article` resets).
  show heading.where(level: 1): it => {
    counter(figure.where(kind: "remark")).update(0)
    it
  }

  show ref: it => {
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
  show figure.where(kind: "theorem"): set block(breakable: true)
  show figure.where(kind: "remark"): set block(breakable: true)
  show figure.where(kind: table): set block(breakable: true)

  show figure.where(kind: "theorem"): it => block(width: 100%, spacing: 11.5pt, breakable: true, {
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
  show figure.where(kind: "remark"): it => block(width: 100%, spacing: 11.5pt, breakable: true, align(left, emph({
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

  // Top-level outline entries are bold, without fill; parts stand out.
  show outline.entry.where(level: 1): it => {
    if it.element.supplement == [Part] {
      block(above: 1.3em, below: .8em, text(size: 1.12em, strong(it)))
    } else {
      strong(it)
    }
  }
  show outline.entry.where(level: 1): set outline.entry(fill: none)

  outline(depth: 2)
  pagebreak()

  body
}

// A part groups several sections: an unnumbered, outlined heading that starts
// on a new page.
#let part(label-name, title) = {
  pagebreak(weak: true)
  show heading: it => block(above: 20pt, below: 14pt, text(size: 16pt, weight: "bold", it.body))
  [#heading(level: 1, numbering: none, outlined: true, supplement: [Part], title) #label(label-name)]
}

// The references.
#let references(label-width: 4.6em) = {
  heading(numbering: none)[References]
  show std.bibliography: set block(inset: (left: label-width), spacing: 1em)
  show std.bibliography: it => {
    show regex("^\[[^\]\s]+\]\s"): label => context {
      h(-label-width)
      if measure(label).width < label-width.to-absolute() {
        box(width: label-width, label.text.trim())
      } else {
        label
      }
    }
    it
  }
  bibliography("refs.bib", style: "references.csl", title: none)
}

// The appendix: everything after `#show: appendix` is numbered "A.", "B.", …
// with only its top-level headings in the outline.
#let appendix(body) = {
  pagebreak()
  heading(outlined: true, numbering: none)[Appendix]
  counter(heading).update(0)
  set heading(outlined: false, numbering: "A.", supplement: "Appendix")
  show heading.where(level: 1): set heading(outlined: true)
  show heading.where(level: 2): set heading(numbering: none)
  body
}
