#import "../../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, game, lemma, mult, negl,
  poly, proof, proposition, remark, theorem, todo, vk, fwd,
)

We begin with the root check. The Final Verifier checks a single field
equation,
$s + cal(F)_chi (cal(G)(bold(p))) = 0$, on a value accumulated from the leaves
under a challenge that the tree itself certifies to be derived from the
statement and the leaves' commitments. By additivity of the fingerprint the
left-hand side is $cal(F)_chi (cal(M)_L + cal(G)(bold(p)))$ for the extracted
collection $L$, so the check is a fingerprint zero test on the signed
multiplicity of $L$ together with the global messages, whereas the target
relation demands $cal(M)_L + cal(G)(bold(p)) = 0$. This section bridges the
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

#lemma(title: "LogUp Fingerprint")[
  $cal(F)^"LogUp"$ is a statistically sound bus fingerprint, with key space
  $KK^2$, values in $KK$ and every nonzero multiset admissible, with error
  $
    epsilon_(cal(F))(Lambda) = frac(ell dot binom(Lambda, 2) + max(Lambda - 1, 0), abs(KK)).
  $
] <lem:logup>

#proof[
  _Additivity._ $cal(F)^"LogUp"_chi (0) = 0$ is the empty sum. If
  $cal(F)^"LogUp"_chi (D)$ and $cal(F)^"LogUp"_chi (D')$ are both defined, no
  message of $"supp" D union "supp" D'$ is a pole; the support of $D + D'$ is
  contained in that union, and the sum defining $cal(F)^"LogUp"_chi (D + D')$
  splits message by message.

  _Soundness._ If $Lambda = 0$, there is no admissible nonzero multiset,
  so the advantage and the stated error are both zero. Assume $Lambda >= 1$.
  The key is drawn after the adversary has output its multiset,
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
  $deg(P) <= abs(D) - 1 <= Lambda - 1$. If $cal(F)^"LogUp"_chi (D) = 0$, then
  all denominators are nonzero and multiplying through by their product gives
  $P(alpha) = 0$, so $alpha$ is a root of $P$. As $alpha$ is uniform and
  independent of $gamma$, this has probability at most
  $(Lambda - 1) slash abs(KK)$. A union bound over the two events gives the
  claim, and the bound is non-decreasing in $Lambda$.
]

#lemma(title: "Zero Test")[
  Let $cal(F)$ be a statistically sound bus fingerprint with key space
  $cal(X)$ that admits every nonzero multiset, let $bold(p) in cal(P)$, let $L$
  be a typed witness collection with $not Balanced_bold(p) (L)$, and let $chi$
  be uniform in $cal(X)$. Then
  $
    Pr_chi [ sum_(i=1)^(abs(L)) BusCont_chi (cal(I)_(tau_i), w_i) + cal(F)_chi (cal(G)(bold(p))) = 0 ]
    <= epsilon_(cal(F))(Lambda(L) + g).
  $
] <lem:zero-test>

#proof[
  If the sum is $0$, every summand is defined, so by additivity the sum
  equals $cal(F)_chi (cal(M)_L + cal(G)(bold(p)))$. Since $L$ is unbalanced
  for $bold(p)$, $cal(M)_L + cal(G)(bold(p)) != 0$, and its support has at
  most $Lambda(L) + g$ elements (@def:balanced), so the soundness of $cal(F)$
  bounds the probability by $epsilon_(cal(F))(Lambda(L) + g)$.
]

The zero test is exactly where the field-valued definition of $Balanced$
enters: it certifies that every signed multiplicity vanishes in $FF$, no
more. We now define the game that captures what the root checks certify about
an extracted collection, and bound it.

#definition(title: "Bus-Argument Soundness Game")[
  For an adversary $cal(A)$ with access to the random oracles, the experiment
  $Exp("bus", cal(A))(lambda)$ proceeds as follows.
  + *Adversary.* $cal(A)(1^lambda)$ outputs a public statement
    $bold(p) in cal(P)$, a typed witness collection
    $L = ((tau_i, w_i))_(i in [abs(L)])$ and commitments $("com"_i)_(i in [abs(L)])$.
  + *Derivation.* Set $bold(c) := sum_(i=1)^(abs(L)) h(tau_i, "com"_i) in ZZ_p^n$
    and $chi := DeriveKey(bold(p), bold(c))$.
  + *Winning condition.* Return $1$ if and only if $1 <= abs(L) < 2^B$;
    $Commit(w_i) = "com"_i$ for every $i$;
    $sum_(i=1)^(abs(L)) BusCont_chi (cal(I)_(tau_i), w_i) + cal(F)_chi (cal(G)(bold(p))) = 0$; and
    $not Balanced_bold(p) (L)$.
  We write $Adv("bus")(cal(A)) := Pr[Exp("bus", cal(A))(lambda) = 1]$.
] <def:bus-game>

Substituting $s_i := BusCont_chi (cal(I)_(tau_i), w_i)$ and
$bold(c)_i := h(tau_i, "com"_i)$ shows that the winning condition is
precisely "the root checks $s + cal(F)_chi (cal(G)(bold(p))) = 0$ and
$chi = DeriveKey(bold(p), bold(c))$ pass on values honestly computed from $L$,
yet $L$ is unbalanced for $bold(p)$". This is the form in
which the game is invoked in the proof of @thm:main.

#proposition(title: "Bus Soundness")[
  Let $cal(F)$ be the bus fingerprint of the system, and let $cal(A)$ be a PPT
  adversary making at most $Q$ random-oracle queries. Under the
  idealizations of @rem:idealized:
  + There are reduction adversaries $cal(D)^"pa"$ and $cal(D)^"ext"$, each
    running $cal(A)$ once in time $Time(cal(A)) + poly(lambda)$, such that
    $
      Adv("bus")(cal(A))
      <= (Q + 1) dot epsilon_(cal(F))(Lambda_"max")
      + Adv("pa", cal(H))(cal(D)^"pa")
      + Adv("ext", Com)(cal(D)^"ext").
    $
  + Let $t^*$ be the first query of $cal(A)$ to $DeriveKey$ at
    $(bold(p), bold(c))$, or the game's derivation if there is none. The
    probability that $cal(A)$ wins while the extractors of $cal(H)$ and of
    $Com$, run on the queries made before $t^*$, return the multiset
    ${(tau_i, "com"_i)}_i$ and the witnesses $w_i$, respectively, is at most
    $(Q + 1) dot epsilon_(cal(F))(Lambda_"max")$.
] <prop:bus-soundness>

#proof[
  Let $(bold(p), L, ("com"_i)_i)$ be $cal(A)$'s output and $bold(c)$, $chi$ as in the
  game, and let $cal(S) := {(tau_i, "com"_i)}_i$ be the multiset of typed
  commitments of the output, so that $bold(c) = cal(H)(cal(S))$. Number the
  $DeriveKey$ queries in the order they are made, counting only the first
  query at each point (a repeated query returns the answer already given),
  and let $t^* in [Q + 1]$ be the index of the query at $(bold(p), bold(c))$, with
  $t^* := Q + 1$ if $cal(A)$ never queried it; in the latter case the
  game's own derivation plays the role of a final, fresh query. For
  $t in [Q + 1]$ write $(bold(p)_t, bold(c)_t)$ for the $t$-th query point, $chi_t$ for its
  answer and $cal(T)_(<t)$ for the transcript of all oracle queries and answers
  made before it. We define bad events, bound each by a reduction to one of
  the assumptions or by @lem:zero-test, and show that off all of them the
  adversary cannot win.

  _Bad events._
  - $E_"pa"$: $abs(L) < 2^B$ and $cal(E)_(cal(H)) (cal(T)_(<t^*), bold(c)) != cal(S)$.
    The reduction $cal(D)^"pa"$ runs $cal(A)$, announces every $DeriveKey$
    query point at the time of the query, and outputs $cal(S)$. Its
    announcement at time $t^*$ is $bold(c)$ (if $t^* = Q + 1$, the game's
    derivation is that announcement), so $E_"pa"$ is its winning event of
    @def:cr for that announcement and $Pr[E_"pa"] <= Adv("pa", cal(H))(cal(D)^"pa")$.
  - $E_"ext"$: $not E_"pa"$ and $cal(E)_Com (cal(T)_(<t^*), "com"_i) != w_i$
    for some $i$. Off $E_"pa"$ the extracted multiset at time $t^*$ is
    $cal(S)$, so this is the failure event of @def:ext-com for the adversary
    $cal(D)^"ext"$ that runs $cal(A)$, at every $DeriveKey$ query $t$
    announces the commitments of $cal(E)_(cal(H)) (cal(T)_(<t), bold(c)_t)$,
    and outputs $("com"_i, w_i)_i$; its announcement at time $t^*$ contains
    every $"com"_i$. Hence $Pr[E_"ext"] <= Adv("ext", Com)(cal(D)^"ext")$.
  - $E_chi^((t))$ for $t in [Q + 1]$: define the _candidate collection_
    $L^*_t$ as follows. If $cal(E)_(cal(H)) (cal(T)_(<t), bold(c)_t)$ returns a
    multiset $cal(S)_t$, let
    $L^*_t := ((tau, cal(E)_Com (cal(T)_(<t), "com")))_((tau, "com") in cal(S)_t)$
    in a canonical order, discarding the collection if some extraction
    returns $bot$; otherwise $L^*_t := bot$. The event $E_chi^((t))$ is that
    $L^*_t != bot$, $abs(L^*_t) < 2^B$, $not Balanced_(bold(p)_t)(L^*_t)$ and
    $sum_i BusCont_(chi_t)(cal(I)_(tau_i), w_i) + cal(F)_(chi_t)(cal(G)(bold(p)_t)) = 0$
    over the entries of $L^*_t$. The candidate is a function of $cal(T)_(<t)$ alone, whereas
    $chi_t$ is uniform in $KK^2$ and independent of $cal(T)_(<t)$ because $t$
    is the first query at its point; since $abs(L^*_t) < 2^B$ implies
    $Lambda(L^*_t) + g <= Lambda_"max"$, @lem:zero-test gives
    $Pr[E_chi^((t))] <= epsilon_(cal(F))(Lambda_"max")$.

  _Step A: off all events, the adversary does not win._ Suppose $cal(A)$
  wins and none of $E_"pa"$, $E_"ext"$, $E_chi^((t^*))$ occurs. The win gives
  $abs(L) < 2^B$, so off $E_"pa"$, $cal(E)_(cal(H)) (cal(T)_(<t^*), bold(c)_(t^*)) = cal(S)$.
  Off $E_"ext"$, $cal(E)_Com (cal(T)_(<t^*), "com"_i) = w_i$ for every $i$, so
  $L^*_(t^*)$ is a reordering of $L$; every quantity in the winning condition
  is invariant under reordering. The winning condition then says
  $not Balanced_bold(p) (L^*_(t^*))$ and
  $sum_i BusCont_(chi_(t^*))(cal(I)_(tau_i), w_i) + cal(F)_(chi_(t^*))(cal(G)(bold(p))) = 0$
  with $chi = chi_(t^*)$ and $bold(p) = bold(p)_(t^*)$, which is $E_chi^((t^*))$: a contradiction.

  _Conclusion._ By Step A a win implies one of the bad events, and a union
  bound over $E_"pa"$, $E_"ext"$ and $E_chi^((1)), dots, E_chi^((Q+1))$
  gives the first statement. The condition of the second statement excludes
  $E_"pa"$ and $E_"ext"$, so a win under it implies one of
  $E_chi^((1)), dots, E_chi^((Q+1))$, which gives the second. Both reductions run $cal(A)$ once and perform a
  scan of the transcript, so they run in $Time(cal(A)) + poly(lambda)$.
]

#remark(numbered: true, title: "Removing the Idealization")[
  Without preimage awareness of $cal(H)$, the second idealization of
  @rem:idealized, the event $E_"pa"$ must be handled by rewinding, using only
  the collision resistance of $cal(H)$ on multisets of cardinality below
  $2^B$, with advantage
  $Adv("cr", cal(H))(cal(A)) := Pr[(cal(S), cal(S)') <- cal(A) : cal(S) != cal(S)' and abs(cal(S)), abs(cal(S)') < 2^B and cal(H)(cal(S)) = cal(H)(cal(S)')]$,
  which for LtHash reduces to the short-integer-solution problem. Run
  $cal(A)$ a second time from its state just before the query $t^*$,
  answering it with a fresh $chi'$. If both runs win with the same
  accumulator and the output collections differ, the two multisets (or two
  openings of one commitment) form a collision for $cal(H)$ or a break of
  @def:ext-com; if they coincide, a single unbalanced collection has passed
  the zero test at two independent challenges, which @lem:zero-test bounds.
  The general forking lemma @CCS:BelNev06 then yields, schematically,
  $
    Adv("bus")(cal(A)) <= epsilon_(cal(F))(Lambda_"max") + sqrt((Q + 1) (epsilon_(cal(F))(Lambda_"max") + Adv("cr", cal(H))(cal(D)^"cr") + Adv("ext", Com)(cal(D)^"ext"))) + frac(Q + 1, abs(KK)),
  $
  with reductions that run $cal(A)$ twice. The square-root loss is inherent to
  rewinding at a Fiat–Shamir query @C:FiaSha86 and is far from concretely
  tight. Making the linear bound of @prop:bus-soundness rigorous is a proof
  obligation for the full security argument: either preimage awareness of
  LtHash as a knowledge-type assumption (an efficient extractor that recovers
  the multiset from an accumulator the adversary produced), or an accumulator
  that is preimage aware in the ROM by construction, at the cost of the
  homomorphism that makes independent aggregation possible.
] <rem:forking>

#remark(numbered: true, title: "Field Versus Integer Balance")[
  @prop:bus-soundness delivers $Balanced_bold(p) (L)$ with multiplicities in $FF$. To
  conclude that every message is sent and received the same number of times
  as integers one needs, in addition, that every multiplicity column of every
  AIR is range-checked to $[0, m_"max"]$ (or to a symmetric interval with a
  fixed signed encoding) and that $Lambda_"max" dot m_"max" < p$, so that
  vanishing in $FF$ lifts to vanishing in $ZZ$. Whether the receiving sides of
  ZisK's lookup tables satisfy such a bound is a property of the individual
  AIRs and is recorded as an open item in #fwd(<sec:discussion>)[Part IV].
] <rem:integer-balance>
