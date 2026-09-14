// Stand-alone title page
#let title-page(
  title: none,
  authors: (),
  date: none,
  abstract: none,
  keywords: (),
  font: "Libertinus Serif",
  mono-font: "New Computer Modern Mono",
) = {
  set page(
    paper: "us-letter",
    margin: (
      top: (116pt / 279mm) * 100%,
      left: (126pt / 216mm) * 100%,
      right: (128pt / 216mm) * 100%,
      bottom: (94pt / 279mm) * 100%,
    ),
    header: none,
    footer: none,
    numbering: none,
  )
  set text(font: font, size: 11pt)
  set par(justify: true)
  counter(page).update(0)

  v(1.5em)
  align(center, text(size: 22pt, title))
  v(3em)

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
    v(2.5em)
    align(center, text(size: 12pt, date))
  }

  if abstract != none {
    v(4em)
    align(center, text(size: 12pt, weight: "bold")[Abstract])
    v(0.8em)
    block({
      set par(first-line-indent: (amount: 1.5em, all: true), spacing: 0.65em)
      abstract
    })
  }

  if keywords.len() > 0 {
    v(1.8em)
    [*Keywords*: #keywords.join("; ")]
  }
}
