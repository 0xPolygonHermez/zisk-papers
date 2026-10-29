// The aggregation tree of a ZisK proof, shared by the whitepaper and the
// security analysis. Each paper wraps it in its own figure and caption.
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "../lib.typ": DeriveKey, verifier, vk

// `root-check` is the bus-balancing check of the Final Verifier, in the
// notation of the paper that draws the tree.
#let aggregation-tree(root-check: $s + cal(F)_chi (cal(G)(bold(p))) = 0$) = {
    set text(size: 7pt)
    let sub(body) = text(size: 6pt, body)
    let lbl(body) = text(size: 6pt, body)
    let leaf-fill = rgb("dde8fb")
    let leaf-stroke = rgb("4a6fa5")
    let lv-fill = rgb("fbe4c2")
    let lv-stroke = rgb("a86e2c")
    let agg-fill = rgb("fbd5d5")
    let agg-stroke = rgb("a84444")
    let root-fill = rgb("c8e6e0")
    let root-stroke = rgb("2e7d6e")
    let comp-fill = rgb("ece4f7")
    let comp-stroke = rgb("6b4fa0")
    let comp-dash = (dash: "dashed", paint: comp-stroke, thickness: 0.5pt)
    let arr-dash = (dash: "dashed", paint: luma(80), thickness: 0.5pt)
    let arr = 0.5pt + luma(80)

    let box(f, s, w, h) = (fill: f, stroke: 0.5pt + s, width: w, height: h, inset: 3pt, corner-radius: 2pt)
    let agg-body = align(center)[
      *Aggregation Node* #linebreak()
      #sub[$verifier_"REC"[vk](pi_L), verifier_"REC"[vk](pi_R) = 1$] #linebreak()
      #sub[$sans("Typed")(tau_L, kappa_L), quad sans("Typed")(tau_R, kappa_R)$] #linebreak()
      #sub[$kappa = kappa_L + kappa_R, quad s = s_L + s_R$] #linebreak()
      #sub[$bold(c) = bold(c)_L + bold(c)_R$]
    ]
    let lv-body = align(center)[
      *Leaf Verifier* $tau$ #linebreak()
      #sub[$verifier_"SEG"^((tau))(pi) = 1$] #linebreak()
      #sub[$kappa = 1, quad bold(c) = h(tau, "com")$]
    ]
    let comp-body = align(center)[
      *Compressor* #linebreak()
      #sub[$verifier_"AIR"^((tau))(pi_"AIR") = 1$]
    ]
    let air-body = align(center)[*AIR Instance* #linebreak() #sub[type $tau$, witness $w$]]

    diagram(
      spacing: (0.7cm, 1.15cm),
      label-sep: 2pt,

      // External verifier
      node((0, -0.75), align(center)[*External Verifier*], stroke: 0.5pt + luma(120), inset: 3pt, corner-radius: 2pt),
      edge((0, 0), (0, -0.75), lbl[$bold(p)_"ext"\, pi_"FINAL"$], "->", stroke: arr, label-side: right),

      // Final Verifier
      node(
        (0, 0),
        align(center)[
          *Final Verifier* #linebreak()
          #sub[$verifier_"REC"[vk_"AGG"](pi) = 1$] #linebreak()
          #sub[$sans("Typed")(tau, kappa)$, #root-check] #linebreak()
          #sub[$chi = DeriveKey(bold(p), bold(c))$]
        ],
        ..box(root-fill, root-stroke, 3.2cm, 1.25cm),
      ),
      // Aggregation nodes
      node((0, 1), agg-body, ..box(agg-fill, agg-stroke, 3.4cm, 1.5cm)),
      node((-1, 2), agg-body, ..box(agg-fill, agg-stroke, 3.4cm, 1.5cm)),
      // Leaf verifiers
      node((-1.5, 3), lv-body, ..box(lv-fill, lv-stroke, 2.5cm, 1.0cm)),
      node((-0.5, 3), lv-body, ..box(lv-fill, lv-stroke, 2.5cm, 1.0cm)),
      node((1, 3), lv-body, ..box(lv-fill, lv-stroke, 2.5cm, 1.0cm)),
      // Optional compressors
      ..(-1.5, -0.5, 1).map(x => node(
        (x, 4),
        comp-body,
        fill: comp-fill,
        stroke: comp-dash,
        width: 2.2cm,
        height: 0.7cm,
        inset: 3pt,
        corner-radius: 2pt,
      )),
      // AIR instances
      node((-1.5, 5), air-body, ..box(leaf-fill, leaf-stroke, 2.2cm, 0.7cm)),
      node((-0.5, 5), air-body, ..box(leaf-fill, leaf-stroke, 2.2cm, 0.7cm)),
      node((1, 5), air-body, ..box(leaf-fill, leaf-stroke, 2.2cm, 0.7cm)),

      // Public statement and key enter every AIR instance
      edge((-1.5, 5.5), (-1.5, 5), lbl[$(bold(p), chi)$], "->", stroke: arr, label-side: right),
      edge((-0.5, 5.5), (-0.5, 5), lbl[$(bold(p), chi)$], "->", stroke: arr, label-side: right),
      edge((1, 5.5), (1, 5), lbl[$(bold(p), chi)$], "->", stroke: arr, label-side: right),

      // Statements and proofs flowing upward
      ..(-1.5, -0.5, 1).map(x => edge(
        (x, 5),
        (x, 4),
        lbl[$(bold(p), chi, s, "com")\, pi_"AIR"$],
        "->",
        stroke: arr-dash,
        label-side: right,
      )),
      ..(-1.5, -0.5, 1).map(x => edge(
        (x, 4),
        (x, 3),
        lbl[$(bold(p), chi, s, "com")\, pi$],
        "->",
        stroke: arr,
        label-side: right,
      )),
      edge((-1.5, 3), (-1, 2), lbl[$(bold(p), chi, sigma_L, vk)\, pi_L$], "->", stroke: arr, label-side: left),
      edge((-0.5, 3), (-1, 2), lbl[$(bold(p), chi, sigma_R, vk)\, pi_R$], "->", stroke: arr, label-side: right),
      edge((-1, 2), (0, 1), lbl[$(bold(p), chi, sigma_L, vk)\, pi_L$], "->", stroke: arr, label-side: left),
      edge((1, 3), (0, 1), lbl[$(bold(p), chi, sigma_R, vk)\, pi_R$], "->", stroke: arr, label-side: right),
      edge((0, 1), (0, 0), lbl[$(bold(p), chi, sigma, vk)\, pi$], "->", stroke: arr, label-side: right),
    )
}
