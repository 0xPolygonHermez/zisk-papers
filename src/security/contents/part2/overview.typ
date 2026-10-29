#import "../../../lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, game, lemma, mult, negl,
  poly, proof, proposition, remark, theorem, todo, vk,
)

We prove that the ZisK aggregation tree is _correct-witness extractable_: any
adversary that produces an accepting Final proof for an external statement
$bold(p)_"ext"$ can be used to extract, in a straight-line fashion, proof
values $bold(p)_"pv"$ and a typed witness collection $L$ such that every witness
satisfies its AIR and is consistent with $bold(p) = (bold(p)_"ext", bold(p)_"pv")$, and
every bus balances across the whole collection together with the global
messages of $bold(p)$. The proof
descends the aggregation tree of @sec:tree layer by layer, reducing
everything to the guarantees of the argument systems of ZisK established in
Part I (@thm:arguments), the straight-line extractability of the trace commitment $Com$, the preimage
awareness of the accumulator $cal(H)$, and the soundness of the bus
fingerprint.

This part follows the reference architecture of the EF zkVM security sprint
@EF:VanillaVM in structure as well as in method: an idealized-model remark,
the definitions of the assumptions, a bridging proposition, one extraction
game and lemma per layer of the recursion, and a main theorem whose bound is
an explicit sum over those lemmas. Where ZisK departs from that architecture,
the departure is flagged at the point where it matters.

#remark(title: "Scope")[
  The target relation of this part speaks about AIR witnesses, not about
  guest executions: it is the recursion layer of the chain that leads from an
  accepting final proof to a correct execution of the guest program. Not
  covered here, and left as named obligations, are the semantic layer (that a
  balanced collection of locally satisfying witnesses encodes a single
  execution of the committed program, including the memory argument and
  continuation stitching), completeness, zero knowledge, and any wrapper
  placed above the Final Verifier.
]
