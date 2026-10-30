#import "../../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, game, lemma, mult, negl,
  poly, proof, proposition, remark, theorem, todo, vk, prover, verifier,
)

// A layer of the descent: a run-in header that starts an unindented paragraph.
#let layer(name) = {
  block(spacing: 1.2em)[]
  strong[#name.]
}

We state one extraction game and one lemma per layer of the aggregation
tree, proceeding from the Final Verifier inward to the compressors. Each
lemma composes the straight-line extractors guaranteed by @def:ks. The AIR
layer has no lemma of its own: it is the joint extraction of Part I
(@thm:arguments).

*Advantage notation.* We collect the advantages introduced above:
$Adv("ks", Pi)$ (knowledge-soundness error, @def:ks), $Adv("ext", Com)$
(@def:ext-com), $Adv("pa", cal(H))$ (@def:cr), $Adv("joint")$
(@def:game-joint) and $Adv("bus")$ (@def:bus-game). All advantages are functions of $lambda$. In each lemma we
exhibit explicit reduction adversaries $cal(D)$ and state their running
times; when a bound has the form $k dot Adv(dot)(cal(D))$, the reduction
$cal(D)$ denotes the maximum-advantage adversary among the $k$ per-node
reductions constructed in the proof, each of which runs in
$Time(cal(A)) + poly(lambda)$. Probabilities in the games below are over the
coins of the adversary, the extractor and the random oracles; verification is
deterministic.

#layer[Final layer] The descent starts from the Final Verifier's proof.

#definition(title: "Final Extraction Game")[
  For an extractor $cal(E)_"FIN"$ and a PPT adversary $cal(A)$, the
  experiment $Exp("fin", (cal(E)_"FIN", cal(A)))(lambda)$ is:
  #game(
    [$cal(A)(1^lambda)$ outputs an external statement $bold(p)_"ext" in cal(P)_"ext"$ and a
      proof $pi_"FIN"$.],
    [If $verifier_"FINAL" (bold(p)_"ext", pi_"FIN") != 1$, return $0$.],
    [Run $(bold(p)_"pv", chi, sigma, pi) <- cal(E)_"FIN" (bold(p)_"ext", pi_"FIN")$, set
      $bold(p) := (bold(p)_"ext", bold(p)_"pv")$, with
      $sigma = (tau, kappa, bold(c), s)$.],
    [Return $1$ if and only if $(bold(p)_"ext"; (bold(p)_"pv", chi, sigma, pi)) in.not cal(R)_"FINAL"$,
      i.e. unless $sans("Typed")(tau, kappa)$,
      $verifier_"REC"^((tau))[vk_"AGG"]((bold(p), chi, sigma, vk_"AGG"), pi) = 1$,
      $s + cal(F)_chi (cal(G)(bold(p))) = 0$ and $chi = DeriveKey(bold(p), bold(c))$.],
  )
  We write $Adv("fin", cal(E)_"FIN")(cal(A))$ for the probability that the
  experiment $Exp("fin", (cal(E)_"FIN", cal(A)))(lambda)$ returns $1$.
] <def:game-fin>

#lemma(title: "Final Extraction")[
  Assume $Pi_"FINAL"$ is knowledge-sound and let $cal(E)_"FIN" := cal(E)_(Pi_"FINAL")$
  be its extractor. For every PPT adversary $cal(A)$ there is a reduction
  $cal(D)_"FIN"$ with $Time(cal(D)_"FIN") = Time(cal(A)) + poly(lambda)$ and
  $
    Adv("fin", cal(E)_"FIN")(cal(A)) = Adv("ks", Pi_"FINAL")(cal(D)_"FIN").
  $
] <lem:fin>

#proof[
  $cal(D)_"FIN"$ runs $cal(A)(1^lambda)$ and forwards $(bold(p)_"ext", pi_"FIN")$ to
  the knowledge-soundness challenger of $Pi_"FINAL"$. The challenger applies
  the same filter and runs the same extractor, and @def:game-fin returns $1$
  exactly when $pi_"FIN"$ verifies but $(bold(p)_"ext"; (bold(p)_"pv", chi, sigma, pi)) in.not cal(R)_"FINAL"$,
  which is the event that $cal(D)_"FIN"$ wins. Since $Pi^*$ and $Pi_"FINAL"$
  are the same algorithm, this is the base of the composition and no
  additional work is required.
]

#layer[Aggregation layer] The aggregation extractor unrolls the tree below the Final Verifier's child
until it reaches leaf-verifier proofs. The counter $kappa$ of the child
statement tells it in advance how many leaves to expect, and it guarantees that it never has to descend further than
$kappa - 1$ aggregation nodes.

#definition(title: "Aggregation Extraction Game")[
  For a counter $kappa in [1, 2^B)$, an extractor $cal(E)_"REC"$ and a PPT
  adversary $cal(A)$, the experiment $Exp("agg", (kappa, cal(E)_"REC", cal(A)))(lambda)$ is:
  #game(
    [$cal(A)(1^lambda)$ outputs $(bold(p), chi, sigma, pi)$ with
      $sigma = (tau, kappa, bold(c), s)$.],
    [If $not sans("Typed")(tau, kappa)$ or
      $verifier_"REC"^((tau))[vk_"AGG"]((bold(p), chi, sigma, vk_"AGG"), pi) != 1$,
      return $0$.],
    [Run $((sigma_1, pi_1), dots, (sigma_kappa, pi_kappa)) <- cal(E)_"REC" (bold(p), chi, sigma, pi)$,
      with $sigma_i = (tau_i, kappa_i, bold(c)_i, s_i)$.],
    [Return $1$ unless, for every $i in [kappa]$, $tau_i in [M]$, $kappa_i = 1$
      and $verifier_"LEAF"^((tau_i))((bold(p), chi, sigma_i, vk_"AGG"), pi_i) = 1$,
      and moreover $sum_(i=1)^kappa s_i = s$ and $sum_(i=1)^kappa bold(c)_i = bold(c)$.],
  )
  We write $Adv("agg", (kappa, cal(E)_"REC"))(cal(A))$ for the probability
  that the experiment returns $1$.
] <def:game-agg>

#lemma(title: "Aggregation Tree Unrolling")[
  Assume $Pi_"AGG"$ is knowledge-sound and let $kappa in [1, 2^B)$. There is
  an extractor $cal(E)_"REC"$, given in the proof, such that for every PPT
  adversary $cal(A)$ there is a reduction $cal(D)_"AGG"$ running in
  $Time(cal(A)) + poly(lambda)$ with
  $
    Adv("agg", (kappa, cal(E)_"REC"))(cal(A)) <= (kappa - 1) dot Adv("ks", Pi_"AGG")(cal(D)_"AGG").
  $
  $cal(E)_"REC"$ makes at most $kappa - 1$ calls to $cal(E)_(Pi_"AGG")$ and
  runs in $(kappa - 1) dot Time(cal(A)) + poly(lambda)$.
] <lem:agg>

#proof[
  The game returns $0$ unless the filter passes, so we assume it does and
  bound the probability that extraction violates the winning condition. The
  argument runs in four steps.

  _Step 1: recursion tree and bad events._ $cal(E)_"REC"$ unrolls a tree
  depth-first. A node $v$ is a pair $(bb(x)_v, pi_v)$ with
  $bb(x)_v = (bold(p), chi, sigma_v, vk_"AGG")$; the root is $cal(A)$'s output. If
  $sigma_v . tau in [M]$, the node is a _leaf_ and the extractor records
  $(sigma_v, pi_v)$. If $sigma_v . tau = M + 1$, the extractor runs
  $cal(E)_(Pi_"AGG")(bb(x)_v, pi_v)$ to obtain a candidate witness
  $((sigma_X, pi_X))_(X in [A])$ and recurses, in slot order, into every
  non-null child $((bold(p), chi, sigma_X, vk_"AGG"), pi_X)$; null slots are
  skipped. If the candidate is not a valid $cal(R)_"AGG"$-witness, the
  extractor aborts. For
  $t >= 1$ let
  $
    B_t & : quad "the first " cal(E)_(Pi_"AGG") " invocation in unroll order that does not return " \
        & quad "a valid " cal(R)_"AGG""-witness for its node's statement is invocation " t "."
  $
  The events are disjoint, and at every invocation the node's proof verifies
  under $verifier(vk_"AGG", dot, dot)$: the root's by the filter (since
  $sans("Typed")(tau, kappa)$ with $tau = M + 1$ and
  $verifier_"REC"^((M+1))[vk_"AGG"] = verifier(vk_"AGG", dot, dot)$), a child's by its parent's
  valid witness. Now count. Before the first failure, the $t - 1$ valid
  aggregation nodes form a tree in which every node has at least two
  non-null children, so each expansion replaces one frontier node by at least
  two and the frontier, the nodes not yet expanded, has at least $t$ nodes. By
  the counter invariant every frontier node carries an integer counter at
  least $1$, and the counters of the frontier sum to $kappa$. Hence
  $t <= kappa$. Moreover, a frontier node of type $M + 1$ has counter at
  least $2$ by $sans("Typed")$, so if $kappa - 1$ valid nodes exist the
  frontier has $kappa$ nodes with counter exactly $1$, all of type in $[M]$,
  and no further invocation exists. Only $B_1, dots, B_(kappa - 1)$ are
  possible, and off all of them the tree has at most $kappa - 1$ aggregation
  nodes and exactly $kappa$ leaves; for $kappa = 1$ the root is a leaf and there is
  nothing to extract.

  _Step 2: one reduction per invocation._ $cal(D)_"AGG"^((t))$ runs
  $cal(A)(1^lambda)$, unrolls the tree up to the $t$-th invocation (which is
  deterministic given $cal(A)$'s output and the earlier extractions) and
  forwards that node's $(bb(x)_v, pi_v)$ to the knowledge-soundness challenger of
  $Pi_"AGG"$. It wins whenever $B_t$ occurs, so
  $Pr[B_t] <= Adv("ks", Pi_"AGG")(cal(D)_"AGG"^((t)))$, and it runs in
  $Time(cal(A)) + poly(lambda)$.

  _Step 3: off the bad events, the extractor succeeds._ Assume
  $not B_1 and dots and not B_(kappa - 1)$; every statement below is then
  deterministic. We show by strong induction on the counter $kappa_v$ that
  for every node $v$ of the unrolled tree, the leaves recorded below $v$
  number exactly $kappa_v$, each has a type in $[M]$ and counter $1$, each
  verifies under $verifier_"LEAF"^((tau_i))$ on the statement
  $(bold(p), chi, sigma_i, vk_"AGG")$, and their partial sums and challenge
  contributions add up to $sigma_v . s$ and $sigma_v . bold(c)$.
  - _Leaf nodes._ If $sigma_v . tau in [M]$, then $sans("Typed")$ (asserted by the
    parent's valid witness, or by the filter for the root) gives
    $kappa_v = 1$, and the same source gives
    $verifier_"REC"^((tau_v))[vk_"AGG"](bb(x)_v, pi_v) = verifier_"LEAF"^((tau_v))(bb(x)_v, pi_v) = 1$.
    The sums are trivial.
  - _Aggregation nodes._ If $sigma_v . tau = M + 1$, the valid witness
    returned for $v$ provides at least two typed non-null children whose
    counters sum to $kappa_v$ over the integers, with $kappa_X in [1, kappa_v - 1]$, each verifying under
    $verifier_"REC"^((tau_X))[vk_"AGG"]$ on a statement that, by the propagation
    invariant, carries the same $(bold(p), chi, vk_"AGG")$; a child of type
    $M + 1$ is therefore verified by $verifier(vk_"AGG", dot, dot) = verifier_"AGG"$ and
    is itself an aggregation node of the tree. The induction hypothesis
    applies to every non-null child; concatenating their leaf lists gives
    $sum_(X in N) kappa_X = kappa_v$ leaves, and
    $s_v = sum_(X in N) s_X$, $bold(c)_v = sum_(X in N) bold(c)_X$ make the
    sums telescope.
  Applied to the root, this is exactly the winning condition of
  @def:game-agg.

  _Step 4: conclusion._ Off all bad events the extractor meets the winning
  condition, so the game returns $1$ only if some $B_t$ occurs, and only
  $B_1, dots, B_(kappa - 1)$ are possible. By a union bound
  $
    Adv("agg", (kappa, cal(E)_"REC"))(cal(A)) <= sum_(t=1)^(kappa - 1) Pr[B_t] <= (kappa - 1) dot Adv("ks", Pi_"AGG")(cal(D)_"AGG"),
  $
  with $cal(D)_"AGG"$ the maximum-advantage reduction among the
  $cal(D)_"AGG"^((t))$. The extractor invokes $cal(E)_(Pi_"AGG")$ once per
  aggregation node, at most $kappa - 1$ times, each call costing at most
  $Time(cal(A)) + poly(lambda)$.
]

The proof relies on the typing predicate at three places where a proof could
_verify_ for a statement outside the relation's support, which knowledge
soundness excludes only up to its error probability: a child of type $M + 1$ with counter $1$ (whose
statement has no witness), a child of type in $[M]$ with a counter other than
$1$ (outside the support of the leaf relation), and a child type outside
$[M + 1]$ (for which no verifier is selected). In each case the parent's valid
witness excludes the child, so the offending proof is charged to the parent's
invocation. Null children need no such argument: they are never verified and
enter none of the sums, so they carry nothing to extract. What the counting
does need is that every aggregation node has at least two non-null children;
without it a chain of aggregation nodes with a single non-null child each
would keep the counter constant, and the number of invocations would no
longer be bounded by $kappa$.

#layer[Leaf-verifier layer] Every leaf-verifier proof yields the proof of its
segment.

#definition(title: "Leaf-Verifier Extraction Game")[
  For $tau in [M]$, an extractor $cal(E)_"LEAF"^((tau))$ and a PPT adversary
  $cal(A)$, the experiment $Exp("leaf", (tau, cal(E)_"LEAF"^((tau)), cal(A)))(lambda)$ is:
  #game(
    [$cal(A)(1^lambda)$ outputs $(bold(p), chi, sigma, vk)$ with
      $sigma = (tau', kappa, bold(c), s)$, and a proof $pi_"LEAF"$.],
    [If $verifier_"LEAF"^((tau))((bold(p), chi, sigma, vk), pi_"LEAF") != 1$,
      return $0$.],
    [Run $("com", pi) <- cal(E)_"LEAF"^((tau))((bold(p), chi, sigma, vk), pi_"LEAF")$.],
    [Return $1$ if and only if
      $((bold(p), chi, sigma, vk); ("com", pi)) in.not cal(R)_"LEAF"^((tau))$,
      i.e. unless $tau' = tau$, $kappa = 1$,
      $verifier_"SEG"^((tau))((bold(p), chi, s, "com"), pi) = 1$ and
      $bold(c) = h(tau, "com")$.],
  )
  We write $Adv("leaf", (tau, cal(E)_"LEAF"^((tau))))(cal(A))$ for the
  probability that the experiment returns $1$.
] <def:game-leaf>

#lemma(title: "Leaf-Verifier Extraction")[
  Assume $Pi_"LEAF"^((tau))$ is knowledge-sound and let
  $cal(E)_"LEAF"^((tau)) := cal(E)_(Pi_"LEAF"^((tau)))$. For every PPT adversary
  $cal(A)$,
  $
    Adv("leaf", (tau, cal(E)_"LEAF"^((tau))))(cal(A)) = Adv("ks", Pi_"LEAF"^((tau)))(cal(D)_"LEAF"^((tau))),
    quad cal(D)_"LEAF"^((tau)) := cal(A).
  $
] <lem:leaf>

#proof[
  The experiment is the knowledge-soundness game of $Pi_"LEAF"^((tau))$: same
  filter, same extractor, and the winning condition is non-membership of the
  extracted pair in $cal(R)_"LEAF"^((tau))$. A statement with $tau' != tau$ or
  $kappa != 1$ lies outside the support of the relation; a verifying proof for
  it is a knowledge-soundness break, and the experiment returns $1$ for it as
  well, so the two advantages coincide. The key $vk$ is not constrained at
  this layer and is only forwarded.
]

The type under which a leaf is extracted is the type $sigma_i . tau$ read from
its statement, which is also the type that selected the verifier in the
aggregation layer. The extracted proof is therefore accepted by the segment
verifier of type $sigma_i . tau$, and this is what makes the output of the
composed extractor a _typed_ collection.

#layer[Compressor layer] For a leaf of a compressed type, the segment verifier is the compressor's,
and the proof extracted from the leaf verifier is a compressor proof. One
more extraction recovers the AIR proof it verifies.

#definition(title: "Compressor Extraction Game")[
  For $tau in T_"COMP"$, an extractor $cal(E)_"COMP"^((tau))$ and a PPT
  adversary $cal(A)$, the experiment
  $Exp("comp", (tau, cal(E)_"COMP"^((tau)), cal(A)))(lambda)$ is:
  #game(
    [$cal(A)(1^lambda)$ outputs a statement $bb(x) = (bold(p), chi, s, "com")$
      and a proof $pi_"COMP"$.],
    [If $verifier_"COMP"^((tau))(bb(x), pi_"COMP") != 1$, return $0$.],
    [Run $pi_"AIR" <- cal(E)_"COMP"^((tau))(bb(x), pi_"COMP")$.],
    [Return $1$ if and only if $verifier_"AIR"^((tau))(bb(x), pi_"AIR") != 1$,
      i.e. unless $(bb(x); pi_"AIR")$ is in the compressor relation of
      $Pi_"AIR"^((tau))$ (@def:r-comp).],
  )
  We write $Adv("comp", (tau, cal(E)_"COMP"^((tau))))(cal(A))$ for the
  probability that the experiment returns $1$.
] <def:game-comp>

#lemma(title: "Compressor Extraction")[
  Assume $Pi_"COMP"^((tau))$ is knowledge-sound and let
  $cal(E)_"COMP"^((tau)) := cal(E)_(Pi_"COMP"^((tau)))$. For every PPT
  adversary $cal(A)$,
  $
    Adv("comp", (tau, cal(E)_"COMP"^((tau))))(cal(A)) = Adv("ks", Pi_"COMP"^((tau)))(cal(D)_"COMP"^((tau))),
    quad cal(D)_"COMP"^((tau)) := cal(A).
  $
] <lem:comp>

#proof[
  The experiment is the knowledge-soundness game of $Pi_"COMP"^((tau))$ for
  the compressor relation of $Pi_"AIR"^((tau))$.
]

For a leaf of a type $tau in.not T_"COMP"$ the segment verifier is
$verifier_"AIR"^((tau))$, and there is nothing to extract. After this layer,
every leaf carries an AIR proof accepted by the AIR verifier of its type.

#layer[AIR layer] The AIR proofs are not extracted one by one, since an AIR proof is not
knowledge-sound on its own (@rem:standalone). After the previous layers,
the leaves of an accepting tree carry exactly the data of the joint AIR
extraction game (@def:game-joint): a public statement $bold(p)$, fewer than
$2^B$ typed commitments $"com"_i$ with bus contributions $s_i$, the key
$chi = DeriveKey(bold(p), sum_i h(tau_i, "com"_i))$ certified by the Final
layer, and AIR proofs accepted under that key. The AIR layer is therefore a
single call to the extractor $cal(E)_"J"$ of the first statement of
@thm:arguments, which outputs the witnesses of all the leaves at once.
