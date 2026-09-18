#import "../../lib.typ": Adv, Local, Pr, Time, definition, lemma, negl, poly, proposition, remark, theorem, vk

This section states what is to be proved. The protocol of @sec:protocol is
analysed in two steps, in the order in which it was presented: first the
interactive protocol, for which we exhibit a _round-by-round_ state function
and bound, round by round, the probability that a verifier message rescues a
transcript that is already lost; then the Fiat-Shamir compilation, for which
the round-by-round bound and the random-oracle model together give knowledge
soundness with a straight-line extractor.

We give the definitions and the statements here, together with the provenance
of each bound: which are instances of a published theorem, which are
instances of one that has to be restated for the variant ZisK uses, and which
have no counterpart in the literature. Proofs are deferred.

== Round-by-Round Soundness <sec:rbr>

Round-by-round soundness @EPRINT:CCHLRRW18 is the property that makes the
Fiat-Shamir transform provably sound. It asks for a way of labelling every
partial transcript as _live_ or _doomed_, such that a false statement starts
doomed, a doomed transcript stays doomed under any prover message, a doomed
full transcript is rejected, and the only way out is a lucky verifier
message. The soundness of the whole protocol is then controlled by a single
quantity: how lucky.

#definition(title: "State function and round-by-round soundness")[
  Let $Pi$ be a public-coin interactive protocol for a relation $cal(R)$, in
  which the prover's messages may be oracles. A _state function_ for $Pi$ is
  a function $"St"$ assigning to every statement $x$ and every partial
  transcript $"tr"$ a value in ${"live", "doomed"}$, such that:
  + if $x$ has no witness, then $"St"(x, nothing) = "doomed"$;
  + if $"St"(x, "tr") = "doomed"$ and $"tr"'$ extends $"tr"$ by a prover
    message, then $"St"(x, "tr"') = "doomed"$;
  + if $"tr"$ is a complete transcript with $"St"(x, "tr") = "doomed"$, then
    the verifier rejects.
  The _round-by-round soundness error_ of $Pi$ with respect to $"St"$ is
  $
    epsilon_"rbr" := max_(x, "tr") Pr_(c)[ "St"(x, "tr" || c) = "live" ],
  $
  the maximum over statements $x$, over partial transcripts $"tr"$ that are
  doomed and await a verifier message, of the probability over that message
  $c$ that the extended transcript becomes live.
] <def:rbr>

The state function need not be efficiently computable; it is a proof device,
not an algorithm. For an oracle protocol it may inspect the whole of every
oracle the prover has sent, which is what lets it speak about the committed
functions rather than about the few positions the verifier opens.

== The State Function <sec:state>

Fix a statement $(bold(p), chi)$ and a _proximity parameter_
$theta in (0, 1 - sqrt(rho))$, below the Johnson bound, so that every
function within relative distance $theta$ of $"RS"[cal(D), N]$ has a unique
closest codeword; for such an $f$ we write $"dec"(f)$ for the polynomial of
degree less than $N$ that it decodes to. The state function of the protocol
is the following; each clause refers to the round of @sec:interactive or
@sec:fri that produces it, and a transcript is doomed as soon as any clause
that applies to it holds.

#definition(title: "State function of the protocol")[
  The transcript is _doomed_ if any of the following holds.
  + *Start.* There is no $w$ with $Local(bold(p), w; chi)$.
  + *Stages.* Some committed function --- a fixed column, a column of a stage
    committed so far, or, later, a quotient chunk --- is at relative distance
    at least $theta$ from $"RS"[cal(D), N]$.
  + *Stages.* All committed columns are within $theta$, and the witness
    $"dec"(w)$ they decode to does not satisfy $cal(C)$ under $chi$.
  + *Aggregation.* The aggregation challenge $zeta$ has been drawn and
    $Z_Omega$ does not divide $hat(C)_zeta$, the aggregated constraint of
    $"dec"(w)$.
  + *Quotient.* The quotient chunks have been committed and
    $hat(C)_zeta != Z_Omega dot sum_i X^(i N) "dec"(Q_i)$ as polynomials.
  + *Out of domain.* The point $xi$ and the values $bold(v)$ have been sent,
    and either the check of @def:ood-check fails, or some entry of $bold(v)$
    differs from the evaluation of the corresponding decoded polynomial at
    its opening point.
  + *Batching.* The batching challenges $bold(mu)$ have been drawn and the
    function $g_0$ they determine is at relative distance at least $theta$
    from $"RS"[cal(D), N]$.
  + *Folding.* A folding challenge $beta_i$ has been drawn and $g_i$ is at
    relative distance at least $theta$ from $"RS"[cal(D)_i, rho 2^(m_i)]$.
] <def:state>

#remark(numbered: true, title: "Reading the state function")[
  Clauses 3 to 6 are the chain that carries a false statement from the
  algebra to the low-degree test, and each link is a separate lemma below: a
  witness that does not satisfy the constraints makes the aggregated
  constraint indivisible (clause 4), an indivisible aggregated constraint
  admits no quotient (clause 5), and no quotient makes the out-of-domain
  identity fail at a random point (clause 6). A prover that wants to survive
  must therefore lie in $bold(v)$, and a lie in $bold(v)$ is exactly what
  makes the DEEP quotients of @sec:interactive fail to be low-degree, which
  clause 7 records and the query phase detects.
] <rem:state-chain>

== The Round Bounds <sec:round-bounds>

Each of the following statements bounds the probability that one verifier
message turns a doomed transcript live. Together they give
@thm:rbr. We write $abs(cal(C))$ for the number of constraints, $delta$ for
their maximum degree and $Lambda := sum_i n_i$ for the total number of
out-of-domain values.

#lemma(title: "Aggregation")[
  Let the committed columns decode to a witness that does not satisfy
  $cal(C)$ under $chi$. Then
  $
    Pr_(zeta <- KK)[ Z_Omega "divides" hat(C)_zeta ] <= frac(abs(cal(C)) - 1, abs(KK)).
  $
] <lem:agg-step>

#lemma(title: "Out-of-domain")[
  Let $Z_Omega$ not divide $hat(C)_zeta$, and let the quotient chunks decode
  to polynomials $"dec"(Q_i)$. Then, over a uniform $xi in KK$, the
  probability that the check of @def:ood-check holds for the _true_
  evaluations of the decoded polynomials is at most $delta N slash abs(KK)$.
] <lem:ood-step>

#lemma(title: "Batching")[
  Suppose some entry of $bold(v)$ differs from the evaluation of the
  corresponding decoded polynomial at its opening point. Then, over uniform
  $bold(mu) = (mu_1, mu_2) in KK^2$,
  $
    Pr[ Delta(g_0, "RS"[cal(D), N]) < theta ] <= epsilon_"batch" (theta, abs(Gamma), Lambda).
  $
] <lem:batch-step>

#lemma(title: "Folding")[
  Suppose $Delta(g_(i-1), "RS"[cal(D)_(i-1), rho 2^(m_(i-1))]) >= theta$.
  Then, over a uniform folding challenge $beta_i in KK$,
  $
    Pr[ Delta(g_i, "RS"[cal(D)_i, rho 2^(m_i)]) < theta ] <= epsilon_"fold" (theta, m_(i-1) - m_i).
  $
] <lem:fold-step>

#lemma(title: "Query phase")[
  Suppose the transcript is doomed when the query indices are drawn. Then the
  verifier accepts with probability at most $(1 - theta)^t$ over the choice of
  the $t$ indices.
] <lem:query-step>

#theorem(title: "Round-by-round soundness")[
  @def:state is a state function for the interactive protocol of
  @sec:protocol, and its round-by-round soundness error is
  $
    epsilon_"rbr" <= max{
      frac(abs(cal(C)) - 1, abs(KK)), quad
      frac(delta N, abs(KK)), quad
      epsilon_"batch", quad
      epsilon_"fold", quad
      (1 - theta)^t
    }.
  $
] <thm:rbr>

== From Round-by-Round Soundness to Knowledge Soundness <sec:compile>

The interactive protocol is an oracle protocol, and the compilation of
@sec:fs replaces its oracles by Merkle commitments and its verifier messages
by random-oracle outputs. This is the BCS transform @TCC:BenChiSpo16, whose
guarantee is what the recursion consumes.

#proposition(title: "Compilation")[
  Let the interactive protocol have $r$ rounds and round-by-round soundness
  error $epsilon_"rbr"$. Then the non-interactive argument of @sec:fs is
  knowledge-sound for $cal(R)_(cal(C))$ against adversaries making at most
  $Q$ random-oracle queries, with error
  $
    epsilon_"ks" <= c(Q, r) dot epsilon_"rbr" dot 2^(-b) + epsilon_"mt" (Q),
  $
  where $c(Q, r)$ is the loss of the passage from round-by-round to
  state-restoration soundness, $2^(-b)$ is the gain from grinding, and
  $epsilon_"mt" (Q)$ collects the Merkle-tree terms. The extractor is
  straight-line: it reads the committed functions off the adversary's oracle
  queries, decodes them, and outputs the witness.
] <prop:compile>

This is the statement that the analysis of the recursion assumes of each of
its four argument systems, and the extractor it produces is the same
Merkle-tree extractor that that analysis uses for the trace commitment, so
its two extractability assumptions are one mechanism rather than two.

#remark(numbered: true, title: "What the compilation does not give")[
  @prop:compile is a statement for a _fixed_ $chi$, because
  $cal(R)_(cal(C))$ is (@def:r-air-sat). In the global mode of @rem:vadcop
  the prover sees $chi$ before committing, so the guarantee is only as good
  as the caller's argument that $chi$ was fixed independently of the witness.
  Nothing in this section supplies that argument, and nothing in this section
  is weakened by its absence: the statement is simply conditional.
]

== Provenance <sec:provenance>

Every bound above is either an instance of a published theorem, an instance
of one that must first be restated for the variant used here, or without a
counterpart in the literature. @tbl:provenance records which.

#figure(
  {
    set text(size: 9pt, hyphenate: false)
    table(
      stroke: 0.3pt,
      columns: (22%, 24%, 54%),
      align: (left, left, left),
      table.header([*Bound*], [*Status*], [*What is needed*]),
      [@lem:agg-step],
      [new, but elementary],
      [Divisibility by $Z_Omega$ is a linear condition; power aggregation meets a proper subspace in at most $abs(cal(C)) - 1$ points (@rem:agg). Independent coefficients would give $1 slash abs(KK)$.],

      [@lem:ood-step],
      [standard],
      [Schwartz-Zippel on a polynomial of degree at most $delta N$.],

      [@lem:batch-step],
      [restatement required],
      [Proximity gaps @EPRINT:BCIKS20 for the curve traced by the nested powers of $(mu_1, mu_2)$, of degree $abs(Gamma) dot max_i n_i$, rather than for an affine space. The published statement covers low-degree parametrised curves; the degree here is what enters $epsilon_"batch"$.],

      [@lem:fold-step],
      [restatement required],
      [FRI folding @ICALP:BBHR18 @EPRINT:BCIKS20 with a per-layer arity $2^(m_(i-1) - m_i)$ rather than a fixed one, and with early stopping at layer $L$.],

      [@lem:query-step],
      [standard],
      [Each query lands on a disagreement point with probability at least $theta$.],

      [@prop:compile],
      [assembly, plus one restatement],
      [BCS @TCC:BenChiSpo16 applied to capped arity-$a$ Merkle trees (@def:mt); the passage from round-by-round to state-restoration soundness; and the accounting of grinding. The constant $c(Q, r)$ is to be pinned.],

      [$theta < 1 - sqrt(rho)$],
      [assumption],
      [The bounds hold in the provable Johnson regime. The configuration's proximity parameter may be set beyond it, in the conjectured regime up to $1 - rho$, which is a separate assumption and must be declared as one.],
    )
  },
  caption: [
    Provenance of the bounds of @sec:round-bounds.
  ],
  kind: table,
) <tbl:provenance>

Two entries deserve emphasis. @lem:batch-step is the one place where ZisK's
choices change the shape of a published statement rather than its
parameters, and it is the bound we are least able to quote. And the last row
is not a bound at all but a modelling decision: whether the analysis is
carried out in the regime where FRI is proved sound, or in the regime where
it is conjectured to be, is the largest single assumption in this document,
and it is the one a reader comparing security levels across zkVMs should look
at first.
