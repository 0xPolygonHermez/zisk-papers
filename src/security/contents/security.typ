#import "../../lib.typ": (
  Adv, Balanced, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Prove, Time, Verify, Zisk, accept, definition, game,
  lemma, mult, negl, poly, proof, proposition, remark, theorem, vk,
)

== Overview

We prove that the ZisK aggregation tree is _correct-witness extractable_: any
adversary that produces an accepting Final proof for a public statement
$bold(p)$ can be used to extract, in a straight-line fashion, a typed witness
collection $L$ such that every witness satisfies its AIR and is consistent
with $bold(p)$, and every bus balances across the whole collection. The proof
descends the aggregation tree of @sec:relations layer by layer, reducing
everything to the knowledge soundness of the four kinds of argument systems
($Pi_"AIR"^((tau))$, $Pi_"LEAF"^((tau))$, $Pi_"AGG"$ and $Pi_"FINAL"$), the
straight-line extractability of the trace commitment $Com$, the multiset
collision resistance of $cal(H)$, and the soundness of the bus fingerprint.

#remark(numbered: true, title: "Idealized proof model")[
  The analysis is idealized in three respects.

  First, @def:ks postulates a straight-line extractor that runs in essentially
  the time of the adversary. Because the argument systems are hash-based, the
  natural model is the random oracle model (ROM), in which such extractors
  exist for a single argument @TCC:BenChiSpo16. Composing straight-line
  extraction across the layers of a recursion tree, however, requires every
  argument to remain knowledge-sound relative to the same oracle, and such
  relativized succinct arguments do not exist in general
  @EPRINT:BarChiGua24. In our analysis we idealize over this
  obstruction and assume that straight-line extraction composes.

  Second, the bus argument is sound only if the collection of witnesses that
  is hashed into the accumulator $bold(c)$ is fixed before the random oracle
  answers at $bold(c)$. For the trace commitments this follows from
  straight-line extractability of Merkle trees in the ROM. For the algebraic
  accumulator $cal(H)$ it does not: distinct multisets with equal hash exist
  in abundance, only the hardness of finding them protects
  the scheme, and recovering a multiset from its accumulator is a subset-sum
  problem. We therefore charge the event that two admissible multisets known
  to the adversary share an accumulator to the collision resistance of
  $cal(H)$, although a straight-line reduction cannot in general exhibit the
  second multiset; @rem:forking discusses the rigorous alternative.

  Third, while the analysis produces explicit advantage bounds and reduction
  running times (@thm:main), the two idealizations mean that these should be
  read as statements about the reduction structure (the recursion topology is
  sound and the relations compose) rather than as a concrete security level.
] <rem:idealized>

#remark(numbered: true, title: "Scope")[
  The target relation of this section speaks about AIR witnesses, not about
  guest executions: it is the recursion layer of the chain that leads from an
  accepting final proof to a correct execution of the guest program. Not
  covered here, and left as named obligations, are the semantic layer (that a
  balanced collection of locally satisfying witnesses encodes a single
  execution of the committed program, including the memory argument and
  continuation stitching), the knowledge soundness of the individual STARK
  arguments (a property of the backend, quantified by their own analysis),
  completeness, zero knowledge, and any wrapper or compression layers placed
  above the Final Verifier, each of which adds one more lemma of the kind
  proved for the leaf-verifier layer.
]

== Definitions <sec:definitions>

#definition(title: "Knowledge soundness")[
  A non-interactive argument system $Pi = (Prove, Verify)$ for
  a relation $cal(R)$ is _knowledge-sound_ if there exists a PPT algorithm
  $cal(E)$, the _extractor_, such that for every PPT adversary $cal(A)$:
  $
    Adv("ks", Pi)(cal(A)) := Pr[ & (x, pi) <- cal(A)(1^lambda); w <- cal(E)(x, pi) : \
                                 & Verify(vk_Pi, x, pi) = accept and (x; w) in.not cal(R) ] <= negl(lambda),
  $
  the probability taken over the coins of $cal(A)$ and $cal(E)$ and the
  random oracles, to which all algorithms have access. We assume that the
  running time of $cal(E)(x, pi)$ is at most $Time(cal(A)(1^lambda)) + poly(lambda)$
  for every $cal(A)$ and every $(x, pi)$ in the support of $cal(A)$'s output:
  the extractor incurs an additive polynomial overhead over one evaluation of
  $cal(A)$. We call $Adv("ks", Pi)(cal(A))$ the _knowledge-soundness error_ of
  $cal(A)$ against $Pi$.
] <def:ks>

#remark(title: "Straight-line extraction")[
  The extractor of @def:ks is straight-line: it receives only the statement
  and the proof and does not rewind the adversary. For succinct proofs this is
  not achievable in the plain model, and in the ROM it holds for one argument
  but does not compose across a recursion (@rem:idealized). The definition is a
  proxy that makes the reduction structure explicit; a concrete instantiation
  replaces it by ROM extractability with the overhead discussed there.
]

#definition(title: "Straight-line extractable commitment")[
  A deterministic commitment scheme $Com$ (@def:commitment) is
  _straight-line extractable_ if there is a PPT algorithm $cal(E)_Com$ that,
  given a transcript $cal(T)$ of random-oracle queries and answers and a
  value $"com"$, outputs a message or $bot$, such that for every PPT
  adversary $cal(A)$ that at some point during its execution announces a
  value $"com"$ and at the end outputs a message $m$,
  $
    Adv("ext", Com)(cal(A)) := Pr[
      Commit(m) = "com" and cal(E)_Com (cal(T)_(<= t), "com") != m
    ] <= negl(lambda),
  $
  where $t$ is the time of the announcement and $cal(T)_(<= t)$ the transcript
  up to it.
] <def:ext-com>

For a Merkle tree over a random oracle the extractor recomputes the leaves
from the tree of queried nodes below the root; it fails only if the adversary
later opens the root to a leaf it had not queried, which requires guessing an
oracle output or finding a collision, so
$Adv("ext", Com)(cal(A)) <= (Q^2 + Q) slash abs("Range")$ for the range of the
oracle. Straight-line extractability implies binding: if $cal(A)$ outputs
$m != m'$ with $Commit(m) = Commit(m') = "com"$, the extractor's output on
$"com"$ differs from at least one of them, so the adversary $cal(D)$ that
runs $cal(A)$, announces $"com"$ and returns one of $m, m'$ chosen at
random fails extraction with at least half of $cal(A)$'s success probability:
$Adv("bind", Com)(cal(A)) <= 2 dot Adv("ext", Com)(cal(D))$.

#definition(title: "Multiset collision resistance")[
  The multiset hash $cal(H)$ is _collision-resistant on multisets of
  cardinality below $2^B$_ if for every PPT adversary $cal(A)$
  $
    Adv("cr", cal(H))(cal(A)) := Pr[ & (cal(S), cal(S)') <- cal(A)(1^lambda) : \
        & cal(S) != cal(S)' and abs(cal(S)), abs(cal(S)') < 2^B and cal(H)(cal(S)) = cal(H)(cal(S)') ] <= negl(lambda).
  $
] <def:cr>

The cardinality restriction is necessary for ZisK's accumulator group: $ZZ_p^n$ has exponent $p$, so
adding $p$ copies of any element to a multiset leaves $cal(H)$ unchanged, and
$2^B < p$ rules this out. For LtHash, collision resistance on bounded
multisets reduces to the short-integer-solution problem @STOC:Ajtai96
@ZISK:LTHASH; the reduction requires the inner digest of $h$ to be collision
resistant on its own, which a single field element is not, so we assume the
digest has at least $2 lambda$ bits (@sec:discussion).

#definition(title: "Random-oracle model")[
  The hash-to-group function $h$, the challenge derivation $DeriveKey$ and
  the hash function underlying $Com$ are independent random oracles. An
  adversary makes at most $Q$ queries in total; every algorithm, including
  verifiers and extractors, has oracle access.
] <def:rom>

#definition(title: "ZisK proof system")[
  A _ZisK proof system_ is a tuple
  $
    Zisk = (cal(C), Com, h, cal(H), DeriveKey, cal(F), {Pi_"AIR"^((tau))}_(tau in [M]), {Pi_"LEAF"^((tau))}_(tau in [M]), Pi_"AGG", Pi_"FINAL")
  $
  consisting of the AIR-type family $cal(C)$, the components of
  @sec:components with the carriers of the ZisK instantiation, a statistically sound bus fingerprint
  $cal(F)$ (@def:fingerprint) admitting every nonzero multiset, and argument
  systems attesting to the relations of
  @sec:relations-def, the key hard-coded by $Pi_"FINAL"$ is the key of
  $Pi_"AGG"$, and the parameters satisfy the standing assumptions of
  @sec:relations.
] <def:zisk>

#definition(title: "Bounded global satisfiability")[
  The _target relation_ $cal(R)_Zisk$ has public statements
  $bold(p) in cal(P)$ and typed witness collections $L$ as witnesses:
  $
    (bold(p); L) in cal(R)_Zisk
    <=>
    cases(
      1 <= abs(L) < 2^B\,,
      Local_(tau_i)(bold(p), w_i) "for every" i in [abs(L)]\,,
      Balanced(L).
    )
  $
  The family $cal(C)$, the local predicates and $B$ are implicit in the
  notation.
] <def:r-zisk>

The relation is invariant under permutations of $L$; it requires neither that
every type occur nor that witnesses be distinct. Its three conjuncts are
exactly what the recursion adds to the individual AIR proofs: a bound on the
number of instances, one common public statement, and global bus balancing.
Everything else that a ZisK proof establishes about the guest execution is a
consequence of $Local$ and $Balanced$ for the specific AIRs of the circuit and
is outside this section.

#definition(title: "Final argument system")[
  The _final argument system_ of $Zisk$ is the non-interactive
  argument system $Pi^*$ for $cal(R)_Zisk$ whose proofs are Final
  proofs and whose verifier is
  $
    Pi^* . Verify(bold(p), pi_"FIN") := V_"FINAL"(bold(p), pi_"FIN").
  $
  Its prover is the honest proving pipeline (execute, split, prove every
  instance, aggregate) and plays no role below.#footnote[
    Knowledge soundness depends only on the verification algorithm.
  ]
] <def:final-as>

Unlike the reference architecture, where the external verifier first commits
to the boundary states, $Pi^*$ coincides with $Pi_"FINAL"$ as an algorithm:
the Final statement is exactly the external public statement $bold(p)$. The
two systems differ only in the relation against which they are judged.

#definition(title: "Correct-witness extractability")[
  $Zisk$ is _correct-witness extractable_ (CWE) if $Pi^*$ is
  knowledge-sound for $cal(R)_Zisk$ in the sense of @def:ks. We write
  $
    Adv("cwe", Zisk)(cal(A)) := Adv("ks", Pi^*)(cal(A))
  $
  for the _CWE advantage_ of a PPT adversary $cal(A)$ and $cal(E)_Zisk$
  for the extractor whose existence is asserted; the running-time convention
  of @def:ks applies to it unchanged.
] <def:cwe>

== From the Root Check to Bus Balancing <sec:bus>

The Final Verifier checks a single field equation, $s = 0$, on a value
accumulated from the leaves under a challenge that the tree itself certifies
to be derived from the leaves' commitments. By additivity of the fingerprint
that value is $cal(F)_chi (cal(M)_L)$ for the extracted collection $L$, so
the check is a fingerprint zero test on the signed multiplicity of $L$,
whereas the target relation demands $cal(M)_L = 0$. This section bridges the
gap. We first record that LogUp is a bus fingerprint in the sense of
@def:fingerprint, then that a zero test at a random challenge certifies
balance, and finally that the challenge the tree certifies is random enough.

Recall ZisK's fingerprint from @sec:instantiation. A key is a challenge pair
$chi = (alpha, gamma) in KK^2$, a message $(b, v)$ is compressed to
$hat(e)_gamma (b, v) = b + sum_(j=1)^(ell_b) gamma^j v_j in KK$, and
$
  cal(F)^"LogUp"_chi (D) = sum_((b, v) in "supp" D) frac(D(b, v), alpha + hat(e)_gamma (b, v)),
$
with $cal(F)^"LogUp"_chi (D) := bot$ if some denominator vanishes.

#lemma(title: "LogUp fingerprint")[
  $cal(F)^"LogUp"$ is a statistically sound bus fingerprint, with key space
  $KK^2$, values in $KK$ and every nonzero multiset admissible, with error
  $
    epsilon_(cal(F))(Lambda) = frac(ell dot binom(Lambda, 2) + Lambda - 1, abs(KK)).
  $
] <lem:logup>

#proof[
  _Additivity._ $cal(F)^"LogUp"_chi (0) = 0$ is the empty sum. If
  $cal(F)^"LogUp"_chi (D)$ and $cal(F)^"LogUp"_chi (D')$ are both defined, no
  message of $"supp" D union "supp" D'$ is a pole; the support of $D + D'$ is
  contained in that union, and the sum defining $cal(F)^"LogUp"_chi (D + D')$
  splits message by message.

  _Soundness._ The key is drawn after the adversary has output its multiset,
  so it suffices to fix an arbitrary $D != 0$ with $abs(D) <= Lambda$ and to
  bound the probability over the key alone. Let $chi = (alpha, gamma)$ be
  uniform in $KK^2$ and write $z_gamma (b, v) := hat(e)_gamma (b, v)$ for
  $(b, v) in "supp" D$.

  _Compression collisions._ Let $E_gamma$ be the event that
  $z_gamma (b, v) = z_gamma (b', v')$ for two distinct messages in
  $"supp" D$. For a fixed pair of messages the difference is a polynomial in
  $gamma$ of degree at most $ell$, and it is nonzero: if $v != v'$ some
  coefficient of a positive power of $gamma$ is nonzero, and if $v = v'$ then
  $b != b'$ and the constant term is nonzero. A uniform $gamma$ is a root with
  probability at most $ell slash abs(KK)$, so
  $Pr[E_gamma] <= binom(Lambda, 2) dot ell slash abs(KK)$.

  _Zero test._ Fix $gamma$ with $not E_gamma$, so the values $z_gamma (b, v)$
  are pairwise distinct, and define
  $
    P(X) := sum_((b, v) in "supp" D) D(b, v) dot product_((b', v') in "supp" D \\ {(b, v)}) (X + z_gamma (b', v')) in KK[X].
  $
  For any $(b_0, v_0) in "supp" D$,
  $
    P(-z_gamma (b_0, v_0)) = D(b_0, v_0) dot product_((b', v') != (b_0, v_0)) (z_gamma (b', v') - z_gamma (b_0, v_0)) != 0
  $
  because all factors are nonzero. Hence $P != 0$ and
  $deg P <= abs(D) - 1 <= Lambda - 1$. If $cal(F)^"LogUp"_chi (D) = 0$, then
  all denominators are nonzero and multiplying through by their product gives
  $P(alpha) = 0$, so $alpha$ is a root of $P$. As $alpha$ is uniform and
  independent of $gamma$, this has probability at most
  $(Lambda - 1) slash abs(KK)$. A union bound over the two events gives the
  claim, and the bound is non-decreasing in $Lambda$.
]

#lemma(title: "Zero test")[
  Let $cal(F)$ be a statistically sound bus fingerprint with key space
  $cal(X)$ that admits every nonzero multiset, let $L$ be a typed witness
  collection with $not Balanced(L)$, and let $chi$ be uniform in $cal(X)$. Then
  $
    Pr_chi [ sum_(i=1)^(abs(L)) BusCont_chi (cal(I)_(tau_i), w_i) = 0 ]
    <= epsilon_(cal(F))(Lambda(L)).
  $
] <lem:zero-test>

#proof[
  If the sum is $0$, every summand $cal(F)_chi ("Msg"_(tau_i)(w_i))$ is
  defined, so by additivity the sum equals
  $cal(F)_chi (sum_i "Msg"_(tau_i)(w_i)) = cal(F)_chi (cal(M)_L)$. Since $L$ is
  unbalanced, $cal(M)_L != 0$, and $abs(cal(M)_L) <= Lambda(L)$
  (@def:balanced), so the soundness of $cal(F)$ bounds the probability by
  $epsilon_(cal(F))(Lambda(L))$.
]

The zero test is exactly where the field-valued definition of $Balanced$
enters: it certifies that every signed multiplicity vanishes in $FF$, no
more. We now define the game that captures what the root checks certify about
an extracted collection, and bound it.

#definition(title: "Bus-argument soundness game")[
  For an adversary $cal(A)$ with access to the random oracles, the experiment
  $Exp("bus", cal(A))(lambda)$ proceeds as follows.
  + *Adversary.* $cal(A)(1^lambda)$ outputs a typed witness collection
    $L = ((tau_i, w_i))_(i in [abs(L)])$ and commitments $("com"_i)_(i in [abs(L)])$.
  + *Derivation.* Set $bold(c) := sum_(i=1)^(abs(L)) h(tau_i, "com"_i) in ZZ_p^n$
    and $chi := DeriveKey(bold(c))$.
  + *Winning condition.* Return $1$ if and only if $1 <= abs(L) < 2^B$;
    $Commit(w_i) = "com"_i$ for every $i$;
    $sum_(i=1)^(abs(L)) BusCont_chi (cal(I)_(tau_i), w_i) = 0$; and
    $not Balanced(L)$.
  We write $Adv("bus")(cal(A)) := Pr[Exp("bus", cal(A))(lambda) = 1]$.
] <def:bus-game>

Substituting $s_i := BusCont_chi (cal(I)_(tau_i), w_i)$ and
$bold(c)_i := h(tau_i, "com"_i)$ shows that the winning condition is
precisely "the root checks $s = 0$ and $chi = DeriveKey(bold(c))$ pass on
values honestly computed from $L$, yet $L$ is unbalanced". This is the form in
which the game is invoked in the proof of @thm:main.

#proposition(title: "Bus soundness")[
  Let $cal(F)$ be the bus fingerprint of the system. Under the idealizations
  of @rem:idealized, for every PPT adversary $cal(A)$ making at most $Q$
  random-oracle queries there are reduction adversaries $cal(D)^"cr"$ and
  $cal(D)^"ext"$, each running $cal(A)$ once in time
  $Time(cal(A)) + poly(lambda)$, such that
  $
    Adv("bus")(cal(A))
    <= (Q + 1) dot epsilon_(cal(F))(Lambda_"max")
    + Adv("cr", cal(H))(cal(D)^"cr")
    + Adv("ext", Com)(cal(D)^"ext")
    + frac(Q + 2^B, p^n).
  $
] <prop:bus-soundness>

#proof[
  Let $(L, ("com"_i)_i)$ be $cal(A)$'s output and $bold(c)$, $chi$ as in the
  game. Number the $DeriveKey$ queries in the order they are made and let
  $t^* in [Q + 1]$ be the index of the first query at $bold(c)$, with
  $t^* := Q + 1$ if $cal(A)$ never queried $bold(c)$; in the latter case the
  game's own derivation plays the role of a final, fresh query. For
  $t in [Q + 1]$ write $bold(c)_t$ for the $t$-th query point, $chi_t$ for its
  answer and $cal(T)_(<t)$ for the transcript of all oracle queries and answers
  made before it; a typed commitment is _known at time $t$_ if it was queried
  to $h$ before the $t$-th $DeriveKey$ query. We define bad events, bound
  each by a reduction or a counting argument, and show that off all of them
  the adversary cannot win.

  _Bad events._
  - $E_"fresh"$: some pair $(tau_i, "com"_i)$ of the output is not known at
    time $t^*$. Order the $h$-evaluations of the output pairs in time,
    counting the game's own evaluations last, and consider the last pair to
    receive its value $g$. At that moment $bold(c)$ has been fixed (since
    time $t^*$) and so have the values of all other pairs, so
    $bold(c) = sum_i h(tau_i, "com"_i)$ forces $mu dot g$ to equal a fixed
    target, where $mu in [1, 2^B)$ is the multiplicity of the pair in the
    collection and is invertible modulo $p$ because $2^B < p$. A fresh oracle
    output hits the required value with probability $p^(-n)$, and there are
    at most $Q + 2^B$ candidates for the last evaluation, so
    $Pr[E_"fresh"] <= (Q + 2^B) slash p^n$.
  - $E_"ext"$: $not E_"fresh"$ and $cal(E)_Com (cal(T)_(<t^*), "com"_i) != w_i$
    for some $i$. Off $E_"fresh"$ the commitment $"com"_i$ was announced (queried
    to $h$) before time $t^*$, so this is the failure event of @def:ext-com for
    the adversary $cal(D)^"ext"$ that runs $cal(A)$, announces $"com"_i$ at its
    first $h$-query, and outputs $("com"_i, w_i)$. Hence
    $Pr[E_"ext"] <= Adv("ext", Com)(cal(D)^"ext")$.
  - $E_"uniq"$: at time $t^*$ there are two distinct multisets
    $cal(S) != cal(S)'$ of typed commitments known at time $t^*$, both of
    cardinality below $2^B$, with $cal(H)(cal(S)) = cal(H)(cal(S)') = bold(c)$.
    The reduction $cal(D)^"cr"$ runs $cal(A)$ and outputs $(cal(S), cal(S)')$,
    so $Pr[E_"uniq"] <= Adv("cr", cal(H))(cal(D)^"cr")$. Exhibiting the second
    multiset is the step covered by the second idealization of
    @rem:idealized: the pair is determined by the transcript, but a
    straight-line reduction cannot in general compute it for an algebraic
    accumulator (@rem:forking).
  - $E_chi^((t))$ for $t in [Q + 1]$: define the _candidate collection_
    $L^*_t$ as follows. If there is a unique multiset $cal(S)_t$ of typed
    commitments known at time $t$, of cardinality below $2^B$, with
    $cal(H)(cal(S)_t) = bold(c)_t$, let
    $L^*_t := ((tau, cal(E)_Com (cal(T)_(<t), "com")))_((tau, "com") in cal(S)_t)$
    in a canonical order, discarding the collection if some extraction
    returns $bot$; otherwise $L^*_t := bot$. The event $E_chi^((t))$ is that
    $L^*_t != bot$, $not Balanced(L^*_t)$ and
    $sum_i BusCont_(chi_t)(cal(I)_(tau_i), w_i) = 0$ over the entries of
    $L^*_t$. The candidate is a function of $cal(T)_(<t)$ alone, whereas
    $chi_t$ is uniform in $KK^2$ and independent of $cal(T)_(<t)$; since
    $abs(L^*_t) < 2^B$ implies $Lambda(L^*_t) <= Lambda_"max"$, @lem:zero-test gives
    $Pr[E_chi^((t))] <= epsilon_(cal(F))(Lambda_"max")$.

  _Step A: off all events, the adversary does not win._ Suppose $cal(A)$
  wins and none of $E_"fresh"$, $E_"ext"$, $E_"uniq"$, $E_chi^((t^*))$ occurs.
  Off $E_"fresh"$ every $(tau_i, "com"_i)$ is known at time $t^*$, so the
  multiset $cal(S) := {(tau_i, "com"_i)}_i$ is a known multiset of cardinality
  $abs(L) < 2^B$ with $cal(H)(cal(S)) = bold(c) = bold(c)_(t^*)$; off
  $E_"uniq"$ it is the unique such multiset, so $cal(S)_(t^*) = cal(S)$. Off
  $E_"ext"$, $cal(E)_Com (cal(T)_(<t^*), "com"_i) = w_i$ for every $i$, so
  $L^*_(t^*)$ is a reordering of $L$; every quantity in the winning condition
  is invariant under reordering. The winning condition then says
  $not Balanced(L^*_(t^*))$ and $sum_i BusCont_(chi_(t^*))(cal(I)_(tau_i), w_i) = 0$
  with $chi = chi_(t^*)$, which is $E_chi^((t^*))$: a contradiction.

  _Conclusion._ By Step A a win implies one of the bad events, and a union
  bound over $E_"fresh"$, $E_"ext"$, $E_"uniq"$ and $E_chi^((1)), dots, E_chi^((Q+1))$
  gives the stated sum. Both reductions run $cal(A)$ once and perform a
  scan of the transcript, so they run in $Time(cal(A)) + poly(lambda)$.
]

#remark(numbered: true, title: "Removing the idealization")[
  Without the second idealization of @rem:idealized, the event $E_"uniq"$ must
  be handled by rewinding. Run $cal(A)$ a second time from its state just
  before the query $t^*$, answering it with a fresh $chi'$. If both runs win
  with the same accumulator and the extracted collections differ, the two
  multisets (or two openings of one commitment) form a collision for $cal(H)$
  or a break of @def:ext-com; if they coincide, a single unbalanced collection
  has passed the zero test at two independent challenges, which @lem:zero-test
  bounds. The general forking lemma @CCS:BelNev06 then yields, schematically,
  $
    Adv("bus")(cal(A)) <= epsilon_(cal(F))(Lambda_"max") + sqrt((Q + 1) (epsilon_(cal(F))(Lambda_"max") + Adv("cr", cal(H))(cal(D)^"cr") + Adv("ext", Com)(cal(D)^"ext"))) + frac(Q + 1, abs(KK)),
  $
  with reductions that run $cal(A)$ twice. The square-root loss is inherent to
  rewinding at a Fiat–Shamir query @C:FiaSha86 and is far from concretely
  tight. Making the linear bound of @prop:bus-soundness rigorous is a proof
  obligation for the full security argument: either a knowledge-type
  assumption on LtHash (an efficient extractor that recovers the multiset from
  an accumulator the adversary produced), or an accumulator that is
  straight-line extractable in the ROM, at the cost of the homomorphism that
  makes independent aggregation possible.
] <rem:forking>

#remark(numbered: true, title: "Field versus integer balance")[
  @prop:bus-soundness delivers $Balanced(L)$ with multiplicities in $FF$. To
  conclude that every message is sent and received the same number of times
  as integers one needs, in addition, that every multiplicity column of every
  AIR is range-checked to $[0, m_"max"]$ (or to a symmetric interval with a
  fixed signed encoding) and that $Lambda_"max" dot m_"max" < p$, so that
  vanishing in $FF$ lifts to vanishing in $ZZ$. Whether the receiving sides of
  ZisK's lookup tables satisfy such a bound is a property of the individual
  AIRs and is recorded as an open item in @sec:discussion.
] <rem:integer-balance>

== Lemmas: Descending the Aggregation Tree <sec:lemmas>

We state one extraction game and one lemma per layer of the aggregation
tree, proceeding from the Final Verifier inward to the AIR arguments. Each
lemma composes the straight-line extractors guaranteed by @def:ks.

*Advantage notation.* We collect the advantages introduced above:
$Adv("ks", Pi)$ (knowledge-soundness error, @def:ks), $Adv("ext", Com)$
(@def:ext-com), $Adv("cr", cal(H))$ (@def:cr) and $Adv("bus")$
(@def:bus-game). All advantages are functions of $lambda$. In each lemma we
exhibit explicit reduction adversaries $cal(D)$ and state their running
times; when a bound has the form $k dot Adv(dot)(cal(D))$, the reduction
$cal(D)$ denotes the maximum-advantage adversary among the $k$ per-node
reductions constructed in the proof, each of which runs in
$Time(cal(A)) + poly(lambda)$. Probabilities in the games below are over the
coins of the adversary, the extractor and the random oracles; verification is
deterministic.

=== Final Layer

#definition(title: "Final extraction game")[
  For an extractor $cal(E)_"FIN"$ and a PPT adversary $cal(A)$, the
  experiment $Exp("fin", (cal(E)_"FIN", cal(A)))(lambda)$ is:
  #game(
    [$cal(A)(1^lambda)$ outputs a public statement $bold(p) in cal(P)$ and a
      proof $pi_"FIN"$.],
    [If $V_"FINAL"(bold(p), pi_"FIN") != accept$, return $0$.],
    [Run $(chi, sigma, pi) <- cal(E)_"FIN"(bold(p), pi_"FIN")$, with
      $sigma = (tau, kappa, bold(c), s)$.],
    [Return $1$ if and only if $(bold(p); (chi, sigma, pi)) in.not cal(R)_"FINAL"$,
      i.e. unless $sans("Typed")(tau, kappa)$,
      $V_"REC"^((tau))[vk_"AGG"]((bold(p), chi, sigma, vk_"AGG"), pi) = accept$,
      $s = 0$ and $chi = DeriveKey(bold(c))$.],
  )
  We write $Adv("fin", cal(E)_"FIN")(cal(A))$ for the probability that the
  experiment $Exp("fin", (cal(E)_"FIN", cal(A)))(lambda)$ returns $1$.
] <def:game-fin>

#lemma(title: "Final extraction")[
  Assume $Pi_"FINAL"$ is knowledge-sound and let $cal(E)_"FIN" := cal(E)_(Pi_"FINAL")$
  be its extractor. For every PPT adversary $cal(A)$ there is a reduction
  $cal(D)_"FIN"$ with $Time(cal(D)_"FIN") = Time(cal(A)) + poly(lambda)$ and
  $
    Adv("fin", cal(E)_"FIN")(cal(A)) = Adv("ks", Pi_"FINAL")(cal(D)_"FIN").
  $
] <lem:fin>

#proof[
  $cal(D)_"FIN"$ runs $cal(A)(1^lambda)$ and forwards $(bold(p), pi_"FIN")$ to
  the knowledge-soundness challenger of $Pi_"FINAL"$. The challenger applies
  the same filter and runs the same extractor, and @def:game-fin returns $1$
  exactly when $pi_"FIN"$ verifies but $(bold(p); (chi, sigma, pi)) in.not cal(R)_"FINAL"$,
  which is the event that $cal(D)_"FIN"$ wins. Since $Pi^*$ and $Pi_"FINAL"$
  are the same algorithm, this is the base of the composition and no
  additional work is required.
]

=== Aggregation Layer

The aggregation extractor unrolls the tree below the Final Verifier's child
until it reaches leaf-verifier proofs. The counter $kappa$ of the child
statement tells it in advance how many leaves to expect, and it guarantees that it never has to descend further than
$kappa - 1$ aggregation nodes.

#definition(title: "Aggregation extraction game")[
  For a counter $kappa in [1, 2^B)$, an extractor $cal(E)_"REC"$ and a PPT
  adversary $cal(A)$, the experiment $Exp("agg", (kappa, cal(E)_"REC", cal(A)))(lambda)$ is:
  #game(
    [$cal(A)(1^lambda)$ outputs $(bold(p), chi, sigma, pi)$ with
      $sigma = (tau, kappa, bold(c), s)$.],
    [If $not sans("Typed")(tau, kappa)$ or
      $V_"REC"^((tau))[vk_"AGG"]((bold(p), chi, sigma, vk_"AGG"), pi) != accept$,
      return $0$. (These are the conjuncts of $cal(R)_"FINAL"$ that concern the
      child.)],
    [Run $((sigma_1, pi_1), dots, (sigma_kappa, pi_kappa)) <- cal(E)_"REC"(bold(p), chi, sigma, pi)$,
      with $sigma_i = (tau_i, kappa_i, bold(c)_i, s_i)$.],
    [Return $1$ unless, for every $i in [kappa]$, $tau_i in [M]$, $kappa_i = 1$
      and $V_"LEAF"^((tau_i))((bold(p), chi, sigma_i, vk_"AGG"), pi_i) = accept$,
      and moreover $sum_(i=1)^kappa s_i = s$ and $sum_(i=1)^kappa bold(c)_i = bold(c)$.],
  )
  We write $Adv("agg", (kappa, cal(E)_"REC"))(cal(A))$ for the probability
  that the experiment returns $1$.
] <def:game-agg>

#lemma(title: "Aggregation tree unrolling")[
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

  _Step 1: recursion tree and bad events._ $cal(E)_"REC"$ unrolls a binary
  tree depth-first. A node $v$ is a pair $(x_v, pi_v)$ with
  $x_v = (bold(p), chi, sigma_v, vk_"AGG")$; the root is $cal(A)$'s output. If
  $sigma_v . tau in [M]$, the node is a _leaf_ and the extractor records
  $(sigma_v, pi_v)$. If $sigma_v . tau = M + 1$, the extractor runs
  $cal(E)_(Pi_"AGG")(x_v, pi_v)$ to obtain a candidate witness
  $((sigma_L, pi_L), (sigma_R, pi_R))$ and recurses into the left child
  $((bold(p), chi, sigma_L, vk_"AGG"), pi_L)$ and then the right child; if the
  candidate is not a valid $cal(R)_"AGG"$-witness, the extractor aborts. For
  $t >= 1$ let
  $
    B_t & : quad "the first " cal(E)_(Pi_"AGG") " invocation in unroll order that does not return " \
        & quad "a valid " cal(R)_"AGG""-witness for its node's statement is invocation " t "."
  $
  The events are disjoint, and at every invocation the node's proof verifies
  under $V(vk_"AGG", dot, dot)$: the root's by the filter (since
  $sans("Typed")(tau, kappa)$ with $tau = M + 1$ and
  $V_"REC"^((M+1))[vk_"AGG"] = V(vk_"AGG", dot, dot)$), a child's by its parent's
  valid witness. Now count. Before the first failure, the $t - 1$ valid
  aggregation nodes form a binary tree whose frontier consists of $t$ nodes,
  each not yet expanded; by the counter invariant every frontier node carries
  an integer counter at least $1$, and the counters of the frontier sum to
  $kappa$. Hence $t <= kappa$. Moreover, a frontier node of type $M + 1$ has
  counter at least $2$ by $sans("Typed")$, so if $kappa - 1$ valid nodes exist
  the frontier has $kappa$ nodes with counter exactly $1$, all of type in
  $[M]$, and no further invocation exists. Only $B_1, dots, B_(kappa - 1)$ are
  possible, and off all of them the tree has exactly $kappa - 1$ aggregation
  nodes and $kappa$ leaves; for $kappa = 1$ the root is a leaf and there is
  nothing to extract.

  _Step 2: one reduction per invocation._ $cal(D)_"AGG"^((t))$ runs
  $cal(A)(1^lambda)$, unrolls the tree up to the $t$-th invocation (which is
  deterministic given $cal(A)$'s output and the earlier extractions) and
  forwards that node's $(x_v, pi_v)$ to the knowledge-soundness challenger of
  $Pi_"AGG"$. It wins whenever $B_t$ occurs, so
  $Pr[B_t] <= Adv("ks", Pi_"AGG")(cal(D)_"AGG"^((t)))$, and it runs in
  $Time(cal(A)) + poly(lambda)$.

  _Step 3: off the bad events, the extractor succeeds._ Assume
  $not B_1 and dots and not B_(kappa - 1)$; every statement below is then
  deterministic. We show by strong induction on the counter $kappa_v$ that
  for every node $v$ of the unrolled tree, the leaves recorded below $v$
  number exactly $kappa_v$, each has a type in $[M]$ and counter $1$, each
  verifies under $V_"LEAF"^((tau_i))$ on the statement
  $(bold(p), chi, sigma_i, vk_"AGG")$, and their partial sums and challenge
  contributions add up to $sigma_v . s$ and $sigma_v . bold(c)$.
  - _Leaf nodes._ If $sigma_v . tau in [M]$, then $sans("Typed")$ (asserted by the
    parent's valid witness, or by the filter for the root) gives
    $kappa_v = 1$, and the same source gives
    $V_"REC"^((tau_v))[vk_"AGG"](x_v, pi_v) = V_"LEAF"^((tau_v))(x_v, pi_v) = accept$.
    The sums are trivial.
  - _Aggregation nodes._ If $sigma_v . tau = M + 1$, the valid witness
    returned for $v$ provides typed children with $kappa_L + kappa_R = kappa_v$
    over the integers and $kappa_X in [1, kappa_v - 1]$, each verifying under
    $V_"REC"^((tau_X))[vk_"AGG"]$ on a statement that, by the propagation
    invariant, carries the same $(bold(p), chi, vk_"AGG")$; a child of type
    $M + 1$ is therefore verified by $V(vk_"AGG", dot, dot) = V_"AGG"$ and
    is itself an aggregation node of the tree. The induction hypothesis
    applies to both children; concatenating their leaf lists gives
    $kappa_L + kappa_R = kappa_v$ leaves, and
    $s_v = s_L + s_R$, $bold(c)_v = bold(c)_L + bold(c)_R$ make the sums
    telescope.
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
soundness does not exclude: a child of type $M + 1$ with counter $1$ (whose
statement has no witness), a child of type in $[M]$ with a counter other than
$1$ (outside the support of the leaf relation), and a child type outside
$[M + 1]$ (for which no verifier is selected). In each case the parent's valid
witness excludes the child, so the offending proof is charged to the parent's
invocation. This is the role played by the step-count typing in the reference
architecture's combine layer.

=== Leaf-Verifier Layer

#definition(title: "Leaf-verifier extraction game")[
  For $tau in [M]$, an extractor $cal(E)_"LEAF"^((tau))$ and a PPT adversary
  $cal(A)$, the experiment $Exp("leaf", (tau, cal(E)_"LEAF"^((tau)), cal(A)))(lambda)$ is:
  #game(
    [$cal(A)(1^lambda)$ outputs $(bold(p), chi, sigma, vk)$ with
      $sigma = (tau', kappa, bold(c), s)$, and a proof $pi_"LEAF"$.],
    [If $V_"LEAF"^((tau))((bold(p), chi, sigma, vk), pi_"LEAF") != accept$,
      return $0$.],
    [Run $("com", pi_"AIR") <- cal(E)_"LEAF"^((tau))((bold(p), chi, sigma, vk), pi_"LEAF")$.],
    [Return $1$ if and only if
      $((bold(p), chi, sigma, vk); ("com", pi_"AIR")) in.not cal(R)_"LEAF"^((tau))$,
      i.e. unless $tau' = tau$, $kappa = 1$,
      $V_"AIR"^((tau))((bold(p), chi, s, "com"), pi_"AIR") = accept$ and
      $bold(c) = h(tau, "com")$.],
  )
  We write $Adv("leaf", (tau, cal(E)_"LEAF"^((tau))))(cal(A))$ for the
  probability that the experiment returns $1$.
] <def:game-leaf>

#lemma(title: "Leaf-verifier extraction")[
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
  filter, same extractor, and the winning condition is membership of the
  extracted pair in $cal(R)_"LEAF"^((tau))$. A statement with $tau' != tau$ or
  $kappa != 1$ lies outside the support of the relation; a verifying proof for
  it is a knowledge-soundness break, and the experiment returns $1$ for it as
  well, so the two advantages coincide. The key $vk$ is not constrained at
  this layer and is only forwarded.
]

The type under which a leaf is extracted is the type $sigma_i . tau$ read from
its statement, which is also the type that selected the verifier in the
aggregation layer. The extracted AIR proof is therefore a proof for
$cal(A)_(sigma_i . tau)$, and this is what makes the output of the composed
extractor a _typed_ collection.

=== AIR Layer

#definition(title: "AIR extraction game")[
  For $tau in [M]$, an extractor $cal(E)_"AIR"^((tau))$ and a PPT adversary
  $cal(A)$, the experiment $Exp("air", (tau, cal(E)_"AIR"^((tau)), cal(A)))(lambda)$ is:
  #game(
    [$cal(A)(1^lambda)$ outputs a statement $x = (bold(p), chi, s, "com")$ and
      a proof $pi_"AIR"$.],
    [If $V_"AIR"^((tau))(x, pi_"AIR") != accept$, return $0$.],
    [Run $(bold(T), bold(a)) <- cal(E)_"AIR"^((tau))(x, pi_"AIR")$.],
    [Return $1$ if and only if $(x; (bold(T), bold(a))) in.not cal(R)_"AIR"^((tau))$,
      i.e. unless $Local_tau (bold(p), (bold(T), bold(a)))$,
      $s = BusCont_chi (cal(I)_tau, (bold(T), bold(a)))$ and
      $Commit(bold(T), bold(a)) = "com"$.],
  )
  We write $Adv("air", (tau, cal(E)_"AIR"^((tau))))(cal(A))$ for the
  probability that the experiment returns $1$.
] <def:game-air>

#lemma(title: "AIR extraction")[
  Assume $Pi_"AIR"^((tau))$ is knowledge-sound and let
  $cal(E)_"AIR"^((tau)) := cal(E)_(Pi_"AIR"^((tau)))$. For every PPT adversary
  $cal(A)$,
  $
    Adv("air", (tau, cal(E)_"AIR"^((tau))))(cal(A)) = Adv("ks", Pi_"AIR"^((tau)))(cal(D)_"AIR"^((tau))),
    quad cal(D)_"AIR"^((tau)) := cal(A),
  $
  and whenever the experiment returns $0$ after passing the filter, the
  extracted witness $(bold(T), bold(a)) in cal(W)_tau$ satisfies
  $Local_tau (bold(p), (bold(T), bold(a)))$, has bus contribution $s$ under
  $chi$, and commits to $"com"$.
] <lem:air>

#proof[
  The experiment is the knowledge-soundness game of $Pi_"AIR"^((tau))$, and
  the structure of the extracted witness is the definition of
  $cal(R)_"AIR"^((tau))$.
]

== Main Theorem <sec:theorem>

#theorem(title: "Correct-witness extractability")[
  Let $Zisk$ be a ZisK proof system (@def:zisk) and let
  $kappa_"max" := 2^B - 1$. Under the idealizations of @rem:idealized, for
  every PPT adversary $cal(A)$ making at most $Q$ random-oracle queries, with
  CWE advantage $epsilon := Adv("cwe", Zisk)(cal(A))$, there exist PPT
  reduction adversaries $cal(D)_"FIN"$, $cal(D)_"AGG"$,
  ${cal(D)_"LEAF"^((tau))}_tau$, ${cal(D)_"AIR"^((tau))}_tau$, $cal(D)^"cr"$
  and $cal(D)^"ext"$ such that
  $
    epsilon <= & Adv("ks", Pi_"FINAL")(cal(D)_"FIN")
                 + (kappa_"max" - 1) dot Adv("ks", Pi_"AGG")(cal(D)_"AGG") \
               & + kappa_"max" dot max_(tau in [M]) Adv("ks", Pi_"LEAF"^((tau)))(cal(D)_"LEAF"^((tau)))
                 + kappa_"max" dot max_(tau in [M]) Adv("ks", Pi_"AIR"^((tau)))(cal(D)_"AIR"^((tau))) \
               & + (Q + 1) dot epsilon_(cal(F))(Lambda_"max")
                 + Adv("cr", cal(H))(cal(D)^"cr")
                 + Adv("ext", Com)(cal(D)^"ext")
                 + frac(Q + 2^B, p^n).
  $
  All reduction adversaries invoke $cal(A)$ exactly once and run in time at
  most $(3 kappa_"max" + 1) dot Time(cal(A)) + poly(lambda)$. In particular, if
  every advantage on the right-hand side is negligible in $lambda$, then
  $Zisk$ is correct-witness extractable (@def:cwe).
] <thm:main>

#proof[
  Let $cal(A)$ be a PPT adversary with CWE advantage $epsilon$; we bound
  $epsilon$. We construct $cal(E)_Zisk$ by composing the sub-extractors
  of @lem:fin, @lem:agg, @lem:leaf and @lem:air, each straight-line and each
  applied to the values extracted by the preceding layer. Let
  $(bold(p), pi_"FIN")$ be $cal(A)$'s output and assume
  $V_"FINAL"(bold(p), pi_"FIN") = accept$, since otherwise $cal(A)$ does not
  win.

  *Step 1 (Final layer).* Apply $cal(E)_"FIN"$ to $(bold(p), pi_"FIN")$ to
  obtain $(chi, sigma, pi)$ with $sigma = (tau, kappa, bold(c), s)$ such that
  $sans("Typed")(tau, kappa)$,
  $V_"REC"^((tau))[vk_"AGG"]((bold(p), chi, sigma, vk_"AGG"), pi) = accept$,
  $s = 0$ and $chi = DeriveKey(bold(c))$. This fails with probability at
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
  $V_"LEAF"^((tau_i))((bold(p), chi, sigma_i, vk_"AGG"), pi_i) = accept$,
  $sum_i s_i = s = 0$ and $sum_i bold(c)_i = bold(c)$. This fails with
  probability at most $(kappa - 1) dot Adv("ks", Pi_"AGG")(cal(D)_"AGG")$ by
  @lem:agg, and the extractor runs in $(kappa - 1) dot Time(cal(A)) + poly(lambda)$.

  *Step 3 (Leaf-verifier layer, applied $kappa$ times).* For each $i in [kappa]$
  apply $cal(E)_"LEAF"^((tau_i))$ to $((bold(p), chi, sigma_i, vk_"AGG"), pi_i)$
  to obtain $("com"_i, pi_i^"AIR")$ with
  $V_"AIR"^((tau_i))((bold(p), chi, s_i, "com"_i), pi_i^"AIR") = accept$ and
  $bold(c)_i = h(tau_i, "com"_i)$. Each invocation fails with probability at
  most $Adv("ks", Pi_"LEAF"^((tau_i)))(cal(D)_"LEAF"^((tau_i)))$ by @lem:leaf;
  the total over $kappa$ calls is at most
  $kappa dot max_tau Adv("ks", Pi_"LEAF"^((tau)))(cal(D)_"LEAF"^((tau)))$.

  *Step 4 (AIR layer, applied $kappa$ times).* For each $i in [kappa]$ apply
  $cal(E)_"AIR"^((tau_i))$ to $((bold(p), chi, s_i, "com"_i), pi_i^"AIR")$ to
  obtain $w_i = (bold(T)_i, bold(a)_i) in cal(W)_(tau_i)$ with
  $Local_(tau_i)(bold(p), w_i)$, $s_i = BusCont_chi (cal(I)_(tau_i), w_i)$ and
  $Commit(w_i) = "com"_i$. The total failure probability over $kappa$ calls is
  at most $kappa dot max_tau Adv("ks", Pi_"AIR"^((tau)))(cal(D)_"AIR"^((tau)))$
  by @lem:air.

  *Step 5 (Assembly).* Output $L := ((tau_1, w_1), dots, (tau_kappa, w_kappa))$.
  Deterministically, given that Steps 1 to 4 succeeded:
  $abs(L) = kappa in [1, 2^B)$; $Local_(tau_i)(bold(p), w_i)$ for every $i$;
  $bold(c) = sum_i h(tau_i, "com"_i) = sum_i h(tau_i, Commit(w_i))$;
  $chi = DeriveKey(bold(c))$; and
  $sum_i BusCont_chi (cal(I)_(tau_i), w_i) = sum_i s_i = s = 0$.

  *Step 6 (Bus soundness).* Let $cal(A)_"bus"$ be the algorithm that runs
  $cal(A)$ and Steps 1 to 5 and outputs $(L, ("com"_i)_i)$; it makes the same
  oracle queries as $cal(A)$ plus those of the extractors. When Steps 1 to 4
  succeed, Step 5 shows that the output satisfies every conjunct of the
  winning condition of @def:bus-game except possibly $not Balanced(L)$, and the
  game's derivation reproduces the extracted $bold(c)$ and $chi$. Hence
  $
    Pr["Steps 1 to 4 succeed" and not Balanced(L)] & <= Adv("bus")(cal(A)_"bus") \
    & <= (Q + 1) dot epsilon_(cal(F))(Lambda_"max") + Adv("cr", cal(H))(cal(D)^"cr") + Adv("ext", Com)(cal(D)^"ext") + frac(Q + 2^B, p^n)
  $
  by @prop:bus-soundness, where $cal(D)^"cr"$ and $cal(D)^"ext"$ run
  $cal(A)_"bus"$ once.

  *Conclusion.* If Steps 1 to 4 succeed and $L$ is balanced, then
  $(bold(p); L) in cal(R)_Zisk$ by Step 5 and @def:r-zisk, so
  $cal(A)$ does not win. Summing the failure probabilities,
  $
    epsilon <= & Adv("ks", Pi_"FINAL")(cal(D)_"FIN")                                     &  "(Step 1)" \
               & + (kappa - 1) dot Adv("ks", Pi_"AGG")(cal(D)_"AGG")                     &  "(Step 2)" \
               & + kappa dot max_tau Adv("ks", Pi_"LEAF"^((tau)))(cal(D)_"LEAF"^((tau))) &  "(Step 3)" \
               & + kappa dot max_tau Adv("ks", Pi_"AIR"^((tau)))(cal(D)_"AIR"^((tau)))   &  "(Step 4)" \
               & + Adv("bus")(cal(A)_"bus")                                              & "(Step 6)",
  $
  and replacing $kappa$ by $kappa_"max"$, which only increases the right-hand
  side, gives the stated bound. All coefficients are polynomially bounded, so
  the right-hand side is negligible whenever each advantage is. Unlike the
  step count of the reference architecture, $kappa$ is not a system parameter
  but part of the extracted witness; the bound with $kappa$ is therefore a
  per-tree refinement and the bound with $kappa_"max"$ the unconditional one.

  _Running time._ $cal(E)_Zisk$ never runs $cal(A)$; its cost is the
  straight-line sub-extractor calls plus deterministic work: one call to
  $cal(E)_(Pi_"FINAL")$, at most $kappa - 1$ calls to $cal(E)_(Pi_"AGG")$, and
  $kappa$ calls each to the leaf-verifier and AIR extractors, i.e. at most
  $3 kappa$ calls in total. Under the convention that each call costs at most
  $Time(cal(A)) + poly(lambda)$, $Time(cal(E)_Zisk) <= 3 kappa_"max" dot Time(cal(A)) + poly(lambda)$.
  Each reduction adversary runs $cal(A)$ once and re-runs the extraction chain
  above its own layer, hence runs in at most
  $(3 kappa_"max" + 1) dot Time(cal(A)) + poly(lambda)$. (Strictly, the
  convention of @def:ks bounds each extractor by the time of the composed
  adversary that produced its input, which compounds along the recursion to
  $O(kappa_"max"^2) dot Time(cal(A))$; the linear figure uses the per-call
  convention and is part of the idealization of @rem:idealized.) In particular
  $cal(E)_Zisk$ is PPT whenever $cal(A)$ is, since $2^B <= poly(lambda)$.
]

== Discussion <sec:discussion>

Every soundness, binding or extractability term that appears in @thm:main
is either defined in this document, inherited from the backend, or an
explicit idealization. @tbl:ledger records the status of each, together with
the obligations that a full security argument must discharge.

#figure(
  table(
    stroke: 0.3pt,
    columns: (27%, 21%, 52%),
    align: (left, left, left),
    table.header([*Term*], [*Status*], [*Where / what remains*]),
    [$Adv("ks", Pi_"AIR"^((tau)))$],
    [backend assumption],
    [Knowledge soundness of each STARK argument for $cal(R)_"AIR"^((tau))$ in commit-and-prove form (@def:r-air); quantified by the backend's own analysis.],

    [$Adv("ks", Pi_"LEAF"^((tau)))$, $Adv("ks", Pi_"AGG")$, $Adv("ks", Pi_"FINAL")$],
    [backend assumption],
    [Knowledge soundness of the recursive STARK circuits for @def:r-leaf, @def:r-agg, @def:r-final, including the typing predicate and the $vk$-dispatch.],

    [straight-line composition],
    [idealization],
    [@rem:idealized (first item); relativized arguments do not exist @EPRINT:BarChiGua24.],

    [$Adv("ext", Com)$], [defined (@def:ext-com)], [Standard for Merkle trees over a random oracle.],
    [$Adv("cr", cal(H))$],
    [defined (@def:cr)],
    [LtHash on multisets of cardinality below $2^B$; requires a collision-resistant inner digest of at least $2 lambda$ bits.],

    [accumulator uniqueness], [idealization], [@rem:idealized (second item); rigorous alternatives in @rem:forking.],
    [$epsilon_(cal(F))$],
    [defined (@def:fingerprint); proved for LogUp (@lem:logup)],
    [Statistical; requires the challenge pair to be a random-oracle output (@def:rom). The circuit proves a sub-relation of $cal(R)_"AIR"^((tau))$ (@sec:instantiation).],

    [$Balanced(L)$],
    [proved (@prop:bus-soundness)],
    [Field-valued; integer balance needs multiplicity range checks (@rem:integer-balance).],
  ),
  caption: [
    Definition and obligation ledger for the terms of @thm:main.
  ],
  kind: table,
) <tbl:ledger>

The following items are outside the theorem and are recorded as
obligations for the sections that build on it.

- *From witnesses to executions.* @thm:main yields a balanced collection of
  locally satisfying AIR witnesses for a common public statement. The
  semantic claim of ZisK, that such a collection encodes one execution of the
  committed program from the boot state to a halting state whose public
  outputs are $bold(p)$, requires the memory argument, the continuation
  stitching and the per-chip semantics, each with its own relation and
  lemma. These compose with @thm:main by strengthening $Local$ and by
  reading off the meaning of $Balanced$ for the specific buses.
- *Integer multiplicities.* See @rem:integer-balance: a bound on every
  multiplicity column, in particular on the receiving side of shared lookup
  tables, is needed to lift field balance to multiset equality.
- *The accumulator.* The linear bound of @prop:bus-soundness rests on the
  second idealization of @rem:idealized. Discharging it (@rem:forking) is the
  main cryptographic obligation left by this section; the bound that forking
  gives is valid but concretely loose.
- *Circuit requirements.* The relations of @sec:relations-def require the
  circuits to enforce the typing predicate on children, to hash the type
  together with the commitment into the challenge contribution, to expose
  the trace commitment as a public input of the AIR argument, and to have
  that commitment bind the cached columns, or else to feed the cached-column
  commitment into the challenge contribution by other means
  (@sec:instantiation). Each is a small change relative to the whitepaper's
  description and each is used by the proofs.
- *Fixed and cached data.* Fixed columns are prescribed by the AIR
  description, hence by the verification key. Cached columns, for instance
  the program ROM and precomputed operation tables, are bound through the
  cached-column commitment carried in the public statement (@def:columns):
  $Local_tau$ only asserts that they open it. Deciding whether the
  commitment in $bold(p)$ is that of the intended program is the task of the
  consumer of the Final proof, and the equality of the cached columns across
  all leaves of one type rests on the binding of that commitment, which the
  theorem does not need and does not charge.
- *Concrete parameters.* With $B = 20$ the running-time factor $3 kappa_"max"$
  is about $3 dot 10^6$ and the coefficient of the recursive
  knowledge-soundness terms is about $10^6$; both are polynomial but not
  small, and any concrete security claim must account for them together with
  the query bound $Q$ and the caveats of @rem:idealized.
- *Completeness.* The honest pipeline produces, for every balanced collection
  of at most $2^B - 1$ locally satisfying witnesses, an accepting Final proof;
  we have not stated this formally, and a complete treatment should.
