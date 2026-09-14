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

// Theorem-like environments. All share the "theorem" figure kind (and hence
// one counter and the styling rule of the main file); `title` is rendered in
// parentheses after the number.
#let _thm(supplement) = (body, title: none, numbered: true) => figure(
  body,
  kind: "theorem",
  supplement: supplement,
  numbering: if numbered { "1" } else { none },
  caption: if title != none { title } else { none },
)
#let theorem = _thm([Theorem])
#let lemma = _thm([Lemma])
#let proposition = _thm([Proposition])
#let corollary = _thm([Corollary])

#let proof(body, sketch: false) = block(spacing: 11.5pt, {
  emph(if sketch { [Proof sketch.] } else { [Proof.] })
  [ ]
  body
  h(1fr)
  sym.wj
  sym.space.nobreak
  $square.stroked$
})

// Extraction game in the "Adversary / Filter / Extraction / Winning
// condition" format.
#let game(adversary, filter, extraction, winning) = enum(
  numbering: "1.",
  [*Adversary.* #adversary],
  [*Filter.* #filter],
  [*Extraction.* #extraction],
  [*Winning condition.* #winning],
)

// Math helpers for the security analysis (sans-serif operators, as in the
// reference documents). Usable inside math: $Adv("ks", Pi)(cal(A))$.
#let _attach-op(name, sup, sub) = math.attach(
  math.sans(name),
  t: math.sans(sup),
  b: if sub.pos().len() > 0 { sub.pos().first() } else { none },
)
#let Adv(sup, ..sub) = _attach-op("Adv", sup, sub)
#let Exp(sup, ..sub) = _attach-op("Exp", sup, sub)

#let Zisk = math.sans("ZisK")
#let Pr = math.op("Pr")
#let Time = math.sans("Time")
#let Prove = math.sans("Prove")
#let Verify = math.sans("Verify")
#let poly = math.sans("poly")
#let negl = math.sans("negl")
#let Com = math.sans("Com")
#let Commit = math.sans("Commit")
#let vk = math.sans("vk")
#let DeriveKey = math.sans("DeriveKey")
#let BusCont = math.upright("BusCont")
#let Local = math.upright("Local")
#let Bind = math.upright("Bind")
#let Balanced = math.upright("Balanced")
#let mult = math.upright("mult")
#let accept = math.upright("accept")
