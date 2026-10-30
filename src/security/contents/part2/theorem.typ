#import "../../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, fwd, game, lemma, mult, negl,
  poly, proof, proposition, remark, theorem, todo, vk, prover, verifier,
)

== The Target Relation <sec:target>

#definition(title: "ZisK Proof System")[
  A _ZisK proof system_ is a tuple
  $
    Zisk = (frak(A), Com, Com_"cach", h, cal(H), DeriveKey, cal(F), {Pi_"AIR"^((tau))}_(tau in [M]), {Pi_"COMP"^((tau))}_(tau in T_"COMP"), {Pi_"LEAF"^((tau))}_(tau in [M]), Pi_"AGG", Pi_"FINAL")
  $
  consisting of the following components:
  + *Chip family.* $frak(A) = {(cal(C)_tau, cal(I)_tau)}_(tau in [M])$, the
    chips of @def:chips, each with its trace height $N_tau$, its column
    classes, its prescribed data and its cached-commitment binding
    (@def:columns).

  + *Trace commitment.* $Com$, a deterministic commitment scheme
    (@def:commitment) on witnesses of any type, straight-line extractable
    (@def:ext-com). It is exposed in the AIR statements (@def:r-air), and its
    digests are what the leaf verifiers hash into the challenge accumulator.

  + *Cached-column commitment.* $Com_"cach"$, a deterministic commitment
    scheme on cached submatrices with commitment space $FF^m$. Its output
    travels in the public statement and is what binds a proof to a program
    (@def:local).

  + *Hash to the accumulator group.* $h : [M] times {0,1}^* -> G_(cal(H))$,
    modeled as a random oracle (@def:rom), which maps a typed commitment to
    the leaf contribution of the challenge accumulator.

  + *Multiset hash.* $cal(H)$, the additively homomorphic extension of $h$ to
    finite multisets of typed commitments, preimage aware on multisets of
    cardinality below $2^B$ (@def:cr).

  + *Key derivation.* $DeriveKey : cal(P) times G_(cal(H)) -> cal(X)$,
    modeled as a random oracle (@def:rom), which turns the public statement
    and the accumulated value into the fingerprint key that the Final
    Verifier checks.

  + *Bus fingerprint.* $cal(F)$ (@def:fingerprint), with key space $cal(X)$ and
    values in $G_(cal(F))$, statistically sound with error
    $epsilon_(cal(F))$ and admitting every nonzero multiset.

  + *Argument systems.* Each is a non-interactive argument system in the sense
    of @sec:components, for the relation named.
    - ${Pi_"AIR"^((tau))}_(tau in [M])$: one per type, for
      $cal(R)_"AIR"^((tau))$ (@def:r-air), proving a single AIR instance.
    - ${Pi_"COMP"^((tau))}_(tau in T_"COMP")$: one per compressed type, for
      the compressor relation of $Pi_"AIR"^((tau))$ (@def:r-comp), which
      hard-codes $vk_"AIR"^((tau))$.
    - ${Pi_"LEAF"^((tau))}_(tau in [M])$: one per type, for
      $cal(R)_"LEAF"^((tau))$ (@def:r-leaf), the leaf verifier, which
      hard-codes the key $vk_"SEG"^((tau))$ of its segment verifier
      (@def:seg).
    - $Pi_"AGG"$: for $cal(R)_"AGG"$ (@def:r-agg), the aggregation node, which
      hard-codes the $M$ leaf-verifier keys and reads the aggregation key from
      its own statement.
    - $Pi_"FINAL"$: for $cal(R)_"FINAL"$ (@def:r-final), the Final Verifier,
      which hard-codes $vk_"AGG"$ and whose verifier the external party runs.

  The carriers are those of the ZisK instantiation (@sec:instantiation), the
  key hard-coded by $Pi_"FINAL"$ is the key of $Pi_"AGG"$, and the parameters
  satisfy the standing assumptions of @sec:preliminaries.
] <def:zisk>

#definition(title: "Bounded Global Satisfiability")[
  The _target relation_ $cal(R)_Zisk$ has external statements
  $bold(p)_"ext" in cal(P)_"ext"$ as statements, and pairs of proof values
  $bold(p)_"pv" in cal(P)_"pv"$ and typed witness collections $L$ as witnesses: with
  $bold(p) := (bold(p)_"ext", bold(p)_"pv")$,
  $
    (bold(p)_"ext"; (bold(p)_"pv", L)) in cal(R)_Zisk
    <=>
    cases(
      1 <= abs(L) < 2^B\,,
      Local_(tau_i)(bold(p), w_i) "for every" i in [abs(L)]\,,
      Balanced_bold(p) (L).
    )
  $
  The family $frak(A)$, the local predicates and $B$ are implicit in the
  notation.
] <def:r-zisk>

The relation is invariant under permutations of $L$; it requires neither that
every type occur nor that witnesses be distinct. Its three conjuncts are
exactly what the recursion adds to the individual AIR proofs: a bound on the
number of instances, one common public statement, and global bus balancing,
including the global messages determined by the statement.
Everything else that a ZisK proof establishes about the guest execution is a
consequence of $Local$ and $Balanced$ for the specific AIRs of ZisK and is the
subject of #fwd(<sec:exec-relation>)[Part III].

#definition(title: "Final Argument System")[
  The _final argument system_ of $Zisk$ is the non-interactive
  argument system $Pi^*$ for $cal(R)_Zisk$ whose proofs are final
  proofs and whose verifier is
  $
    verifier^* (bold(p)_"ext", pi_"FIN") := verifier_"FINAL" (bold(p)_"ext", pi_"FIN").
  $
  Its prover is the honest proving pipeline (execute, split, prove every
  instance, aggregate) and plays no role below.#footnote[
    Knowledge soundness depends only on the verification algorithm.
  ]
] <def:final-as>

In the reference architecture @EF:VanillaVM the two systems differ as
algorithms: its target relation has boundary machine states as statements,
with memory given in full, while its last recursive proof speaks about states
whose memory has been replaced by a commitment, so its external verifier must
commit to the two boundary memories before it can run that proof's verifier.
ZisK needs no such step: the Final relation and $cal(R)_Zisk$ have the same
statement, the external statement $bold(p)_"ext"$, so $Pi^*$ and $Pi_"FINAL"$ are the same
algorithm and differ only in the relation against which each is judged.

#definition(title: "Correct-Witness Extractability")[
  $Zisk$ is _correct-witness extractable_ (CWE) if $Pi^*$ is
  knowledge-sound for $cal(R)_Zisk$ in the sense of @def:ks. We write
  $
    Adv("cwe", Zisk)(cal(A)) := Adv("ks", Pi^*)(cal(A))
  $
  for the _CWE advantage_ of a PPT adversary $cal(A)$ and $cal(E)_Zisk$
  for the extractor whose existence is asserted, which may run in time
  $O(kappa_"max") dot Time(cal(A)) + poly(lambda)$ rather than within the
  bound of @def:ks.
] <def:cwe>

== Correct-Witness Extractability

#theorem(title: "Correct-Witness Extractability")[
  Let $Zisk$ be a ZisK proof system (@def:zisk), let
  $kappa_"max" := 2^B - 1$, and let $epsilon^*$ and $Lambda_"pole"$ be as in
  @lem:binding. Under the idealizations of @rem:idealized, for every PPT
  adversary $cal(A)$ that, together with the extractors composed with it
  below, makes at most $Q$ random-oracle queries, with CWE advantage
  $epsilon := Adv("cwe", Zisk)(cal(A))$, there exist PPT reduction
  adversaries $cal(D)_"FIN"$, $cal(D)_"AGG"$, ${cal(D)_"LEAF"^((tau))}_(tau in [M])$,
  ${cal(D)_"COMP"^((tau))}_(tau in T_"COMP")$ and $cal(D)^"pa"$ such that
  $
    epsilon <= & Adv("ks", Pi_"FINAL")(cal(D)_"FIN")
                 + (kappa_"max" - 1) dot Adv("ks", Pi_"AGG")(cal(D)_"AGG") \
               & + kappa_"max" dot max_(tau in [M]) Adv("ks", Pi_"LEAF"^((tau)))(cal(D)_"LEAF"^((tau)))
                 + kappa_"max" dot max_(tau in T_"COMP") Adv("ks", Pi_"COMP"^((tau)))(cal(D)_"COMP"^((tau))) \
               & + Q dot epsilon^* + Adv("pa", cal(H))(cal(D)^"pa") + epsilon_"MT" (Q)
                 + frac(Q dot Lambda_"pole", abs(KK))
                 + (Q + 1) dot epsilon_(cal(F))(Lambda_"max").
  $
  All reduction adversaries invoke $cal(A)$ exactly once and run in time at
  most $(3 kappa_"max" + 2) dot Time(cal(A)) + poly(lambda)$. In particular, if
  every term on the right-hand side is negligible in $lambda$, then
  $Zisk$ is correct-witness extractable (@def:cwe).
] <thm:main>

Each term of the bound accounts for one way in which an accepting final
proof may fail to yield a witness of $cal(R)_Zisk$, and the proof charges
each to one step of the descent:
- $Adv("ks", Pi_"FINAL")$: the final proof is accepted, but no witness of
  $cal(R)_"FINAL"$ can be extracted from it.
- $(kappa_"max" - 1) dot Adv("ks", Pi_"AGG")$: the same for one of the
  aggregation nodes, of which a tree with $kappa$ leaves has at most
  $kappa - 1$, since each has at least two non-null children.
- $kappa_"max" dot max_tau Adv("ks", Pi_"LEAF"^((tau)))$ and
  $kappa_"max" dot max_(tau in T_"COMP") Adv("ks", Pi_"COMP"^((tau)))$: the
  same for one of the at most $kappa$ leaf verifiers and compressors.
- $Q dot epsilon^*$: some query of the adversary to the transcript of an AIR
  proof makes a round of the IOP succeed, which each of the $Q$ queries does
  with probability at most the round-by-round error $epsilon^*$
  (@thm:iop-rbr).
- $Adv("pa", cal(H))$: when the key is derived, the accumulator $bold(c)$
  hides a multiset other than the typed commitments of the leaves.
- $epsilon_"MT" (Q)$: the oracle queries contain a collision or an inversion
  of the hash, so that some Merkle root has no unique preimage.
- $Q dot Lambda_"pole" \/ abs(KK)$: the derived key is a pole of one of the
  extracted witnesses, where the bus constraints do not determine the bus
  contribution.
- $(Q + 1) dot epsilon_(cal(F))(Lambda_"max")$: the fingerprint of an
  unbalanced collection vanishes at one of the at most $Q + 1$ derived keys,
  so the root check passes although some bus is unbalanced.
The first four terms are charged by the layers of @sec:lemmas; the next four
by the joint extraction of the AIR witnesses (@lem:binding), which also
supplies the preimage awareness and the Merkle extraction that the bus
argument needs; and the last by @prop:bus-soundness.

#proof[
  Let $cal(A)$ be a PPT adversary with CWE advantage $epsilon$; we bound
  $epsilon$. We construct $cal(E)_Zisk$ by composing the sub-extractors
  of @lem:fin, @lem:agg, @lem:leaf and @lem:comp with the joint extractor of
  the AIR layer of @sec:lemmas, each straight-line and each applied to the values extracted
  by the preceding layer. Let $(bold(p)_"ext", pi_"FIN")$ be $cal(A)$'s output
  and assume $verifier_"FINAL" (bold(p)_"ext", pi_"FIN") = 1$, since otherwise
  $cal(A)$ does not win.

  *Step 1 (Final layer).* Apply $cal(E)_"FIN"$ to $(bold(p)_"ext", pi_"FIN")$ to
  obtain $(bold(p)_"pv", chi, sigma, pi)$ with $sigma = (tau, kappa, bold(c), s)$ such
  that, for $bold(p) := (bold(p)_"ext", bold(p)_"pv")$, $sans("Typed")(tau, kappa)$,
  $verifier_"REC"^((tau))[vk_"AGG"]((bold(p), chi, sigma, vk_"AGG"), pi) = 1$,
  $s + cal(F)_chi (cal(G)(bold(p))) = 0$ and $chi = DeriveKey(bold(p), bold(c))$. This fails with probability at
  most $Adv("ks", Pi_"FINAL")(cal(D)_"FIN")$ by @lem:fin. In particular
  $kappa in [1, 2^B)$, so $kappa <= kappa_"max"$.#footnote[
    This composition is where the first idealization of @rem:idealized is
    invoked: a straight-line extractor for a succinct $Pi_"FINAL"$ does not
    exist in the plain model, and composing it with the extractors below
    requires relativized arguments.
  ]

  *Step 2 (Aggregation layer).* Apply $cal(E)_"REC"$ to
  $(bold(p), chi, sigma, pi)$; its filter is satisfied by Step 1. Obtain
  $((sigma_1, pi_1), dots, (sigma_kappa, pi_kappa))$ with
  $sigma_i = (tau_i, 1, bold(c)_i, s_i)$, $tau_i in [M]$,
  $verifier_"LEAF"^((tau_i))((bold(p), chi, sigma_i, vk_"AGG"), pi_i) = 1$,
  $sum_i s_i = s$ and $sum_i bold(c)_i = bold(c)$. This fails with
  probability at most $(kappa - 1) dot Adv("ks", Pi_"AGG")(cal(D)_"AGG")$ by
  @lem:agg, and the extractor runs in $(kappa - 1) dot Time(cal(A)) + poly(lambda)$.

  *Step 3 (Leaf-verifier layer, applied $kappa$ times).* For each $i in [kappa]$
  apply $cal(E)_"LEAF"^((tau_i))$ to $((bold(p), chi, sigma_i, vk_"AGG"), pi_i)$
  to obtain $("com"_i, pi_i^"SEG")$ with
  $verifier_"SEG"^((tau_i))((bold(p), chi, s_i, "com"_i), pi_i^"SEG") = 1$ and
  $bold(c)_i = h(tau_i, "com"_i)$. Each invocation fails with probability at
  most $Adv("ks", Pi_"LEAF"^((tau_i)))(cal(D)_"LEAF"^((tau_i)))$ by @lem:leaf;
  the total over $kappa$ calls is at most
  $kappa dot max_tau Adv("ks", Pi_"LEAF"^((tau)))(cal(D)_"LEAF"^((tau)))$.

  *Step 3′ (Compressor layer, applied at most $kappa$ times).* For each
  $i in [kappa]$ with $tau_i in T_"COMP"$, apply $cal(E)_"COMP"^((tau_i))$ to
  $((bold(p), chi, s_i, "com"_i), pi_i^"SEG")$ to obtain $pi_i^"AIR"$ with
  $verifier_"AIR"^((tau_i))((bold(p), chi, s_i, "com"_i), pi_i^"AIR") = 1$. Each
  invocation fails with probability at most
  $Adv("ks", Pi_"COMP"^((tau_i)))(cal(D)_"COMP"^((tau_i)))$ by @lem:comp, and
  the total is at most
  $kappa dot max_(tau in T_"COMP") Adv("ks", Pi_"COMP"^((tau)))(cal(D)_"COMP"^((tau)))$.
  For $tau_i in.not T_"COMP"$ the segment verifier is
  $verifier_"AIR"^((tau_i))$, and we set $pi_i^"AIR" := pi_i^"SEG"$.

  *Step 4 (AIR layer, one joint call).* Let $cal(A)_"J"$ be the algorithm
  that runs $cal(A)$ and Steps 1 to 3′ and outputs $bold(p)$ and
  $(tau_i, "com"_i, s_i, pi_i^"AIR")_(i in [kappa])$. When Steps 1 to 3′
  succeed, $1 <= kappa < 2^B$, $sum_i h(tau_i, "com"_i) = sum_i bold(c)_i = bold(c)$,
  $chi = DeriveKey(bold(p), bold(c))$, and every $pi_i^"AIR"$ is accepted
  under $chi$, so $cal(A)_"J"$ passes the filter of the joint game
  (@def:game-joint). Apply $cal(E)_"J"$ to obtain $w_1, dots, w_kappa$ with
  $((bold(p), chi, s_i, "com"_i); w_i) in cal(R)_"AIR"^((tau_i))$, that is,
  $Local_(tau_i)(bold(p), w_i)$, $s_i = BusCont_chi (cal(I)_(tau_i), w_i)$
  and $Commit(w_i) = "com"_i$, for every $i$. Let $B_"J"$ be the union of the
  four events of the proof of @lem:binding for $cal(A)_"J"$; outside $B_"J"$
  the extraction succeeds, and
  $
    Pr[B_"J"] <= Q dot epsilon^* + Adv("pa", cal(H))(cal(D)^"pa") + epsilon_"MT" (Q) + frac(Q dot Lambda_"pole", abs(KK)).
  $

  *Step 5 (Assembly).* Output $bold(p)_"pv"$ and $L := ((tau_1, w_1), dots, (tau_kappa, w_kappa))$.
  Deterministically, given that Steps 1 to 4 succeeded:
  $abs(L) = kappa in [1, 2^B)$; $Local_(tau_i)(bold(p), w_i)$ for every $i$;
  $bold(c) = sum_i h(tau_i, "com"_i) = sum_i h(tau_i, Commit(w_i))$;
  $chi = DeriveKey(bold(p), bold(c))$; and
  $sum_i BusCont_chi (cal(I)_(tau_i), w_i) + cal(F)_chi (cal(G)(bold(p))) = s + cal(F)_chi (cal(G)(bold(p))) = 0$.

  *Step 6 (Bus soundness).* Let $cal(A)_"bus"$ be the algorithm that runs
  $cal(A)$ and Steps 1 to 5 and outputs $(bold(p), L, ("com"_i)_i)$. When Steps 1
  to 4 succeed, Step 5 shows that the output satisfies every conjunct of the
  winning condition of @def:bus-game except possibly $not Balanced_bold(p) (L)$,
  and the game's derivation reproduces the extracted $bold(c)$ and $chi$.
  Outside $B_"J"$, moreover, the extractor of $cal(H)$ returns the multiset
  ${(tau_i, "com"_i)}_i$ at the first query to $DeriveKey$ at $(bold(p), bold(c))$,
  which excludes the accumulator event of @lem:binding, and the extractor of
  $Com$ returns $w_i$ there, since the $w_i$ are the preimages of the roots
  that the Merkle event of @lem:binding fixes in the query list before that
  query. Hence, by the second statement of @prop:bus-soundness,
  $
    Pr["Steps 1 to 3′ succeed" and not B_"J" and not Balanced_bold(p) (L)] <= (Q + 1) dot epsilon_(cal(F))(Lambda_"max").
  $

  *Conclusion.* If Steps 1 to 3′ succeed, $B_"J"$ does not occur and $L$ is
  balanced for $bold(p)$, then
  $(bold(p)_"ext"; (bold(p)_"pv", L)) in cal(R)_Zisk$ by Step 5 and @def:r-zisk, so
  $cal(A)$ does not win. Summing the failure probabilities,
  $
    epsilon <= & Adv("ks", Pi_"FINAL")(cal(D)_"FIN")                                     &  "(Step 1)" \
               & + (kappa - 1) dot Adv("ks", Pi_"AGG")(cal(D)_"AGG")                     &  "(Step 2)" \
               & + kappa dot max_tau Adv("ks", Pi_"LEAF"^((tau)))(cal(D)_"LEAF"^((tau))) &  "(Step 3)" \
               & + kappa dot max_(tau in T_"COMP") Adv("ks", Pi_"COMP"^((tau)))(cal(D)_"COMP"^((tau))) &  "(Step 3′)" \
               & + Pr[B_"J"]                                                             &  "(Step 4)" \
               & + (Q + 1) dot epsilon_(cal(F))(Lambda_"max")                            & "(Step 6)",
  $
  and replacing $kappa$ by $kappa_"max"$, which only increases the right-hand
  side, gives the stated bound. The terms of preimage awareness and of
  Merkle extraction are charged once, in Step 4, although both the joint
  extraction and the bus argument rely on them. All coefficients are
  polynomially bounded, so the right-hand side is negligible whenever each
  term is. Unlike the step count of the reference architecture
  @EF:VanillaVM, $kappa$ is not a system parameter but part of the extracted
  witness; the bound with $kappa$ is therefore a per-tree refinement and the
  bound with $kappa_"max"$ the unconditional one.

  _Running time._ $cal(E)_Zisk$ never runs $cal(A)$; its cost is the
  straight-line sub-extractor calls plus deterministic work: one call to
  $cal(E)_(Pi_"FINAL")$, at most $kappa - 1$ calls to $cal(E)_(Pi_"AGG")$,
  $kappa$ calls to the leaf-verifier extractors, at most $kappa$ calls to the
  compressor extractors and one call to $cal(E)_"J"$, i.e. at most
  $3 kappa + 1$ calls in total. Under the convention that each call costs at
  most $Time(cal(A)) + poly(lambda)$,
  $Time(cal(E)_Zisk) <= (3 kappa_"max" + 1) dot Time(cal(A)) + poly(lambda)$.
  Each reduction adversary runs $cal(A)$ once and re-runs the extraction
  chain above its own layer, hence runs in at most
  $(3 kappa_"max" + 2) dot Time(cal(A)) + poly(lambda)$. (Strictly, the
  convention of @def:ks bounds each extractor by the time of the composed
  adversary that produced its input, which compounds along the recursion, in
  the worst case exponentially in the depth of the tree, the usual blow-up of
  recursive extraction; the linear figure uses the per-call convention and is
  part of the idealization of @rem:idealized.) In particular
  $cal(E)_Zisk$ is PPT whenever $cal(A)$ is, since $2^B <= poly(lambda)$.
]

#remark(numbered: true, title: [Query Budget and the Factors $kappa_"max"$])[
  The query bound $Q$ counts the queries of $cal(A)$ together with those of
  the extractors composed with it, which are polynomially many: Steps 4 and
  6 apply to such compositions. Every proof of the tree, moreover, is
  produced from the same query list, so a single union bound over the $Q$
  queries could replace the factors of the aggregation, leaf-verifier and
  compressor terms, as it already does for the AIR proofs in Step 4. Doing so
  would merge the layers into one compilation argument; we keep the layered
  structure of the reference architecture @EF:VanillaVM and its looser bound.
] <rem:query-budget>
