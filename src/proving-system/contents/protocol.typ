#import "../../lib.typ": Commit, Local, definition, remark, vk

We now specify the argument system. It is presented in two steps: first as an
interactive protocol between a prover and a verifier, in which the verifier's
messages are uniform elements of $KK$ and the prover answers queries to
committed vectors, and then as the non-interactive argument obtained by
deriving the verifier's messages from the transcript with the random oracle.

Throughout, fix a staged AIR $cal(C)$ with $S$ stages (@def:staged) and a
configuration $"cfg"$ (@tbl:cfg). Recall from @sec:encoding that $N = 2^n$ is
the trace height, $Omega = ⟨omega⟩$ the trace domain,
$cal(D) = eta ⟨omega_"ext"⟩$ the evaluation domain of size
$2^(n_"ext") = N slash rho$, that $Z_Omega (X) = X^N - 1$, and that the
quotient is split into $q = delta - 1$ chunks.

== What the Protocol Proves <sec:protocol-relation>

#definition(title: "AIR satisfaction relation")[
  For a staged AIR $cal(C)$ with prescribed data $bold(d)$ and bindings
  $beta, gamma$, the _AIR satisfaction relation_ is
  $
    cal(R)_(cal(C)) := { ((bold(p), chi); w) mid(|) w in cal(W) and Local(bold(p), w; chi) },
  $
  where $bold(p) in cal(P)$ is a public statement, $chi$ a challenge vector
  and $w = (bold(T), bold(a))$ a witness of height $N$.
] <def:r-air-sat>

Two features of this relation deserve comment, because they are what make it
usable by a caller that composes several proofs.

First, the challenge vector $chi$ is part of the _statement_, not of the
witness, and not something the protocol samples. The relation is a family
indexed by $chi$, and an argument system for it says nothing about where
$chi$ came from. @sec:fs describes the two ways the implementation supplies
it, and @rem:vadcop explains why the distinction is not cosmetic.

Second, a caller may need the proof to be bound to the prover's commitment to
the trace, rather than only to the public statement. The protocol commits to
the stage-$1$ columns before anything else happens, so its first message is
such a commitment; a caller that needs it can read it off the proof and treat
it as an additional public output. We write $"rt"_1$ for it below and return
to this in @sec:commit-and-prove.

== Setup <sec:setup>

The setup is deterministic and depends only on $cal(C)$ and $"cfg"$. It
computes the low-degree extensions of the fixed columns, that is the
restrictions to $cal(D)$ of the interpolants of $bold(d)$, commits to them
with @def:mt, and outputs
$
  vk := ("rt"_(cal(C)), cal(C), "cfg"),
$
where $"rt"_(cal(C))$ is that commitment. The verification key contains no
secret and no randomness: it is a digest of the circuit description, and two
parties that agree on $cal(C)$ and $"cfg"$ compute the same $vk$. Cached
columns are _not_ part of it; they are bound through the public statement
(@def:local).

== The Interactive Protocol <sec:interactive>

The prover holds $(bold(p), chi)$ and a witness $w$ with
$Local(bold(p), w; chi)$. All prover messages are either Merkle commitments
to matrices over $cal(D)$, elements of $KK$, or openings; all verifier
messages are uniform elements of $KK$.

+ *Stage commitments.* For $s = 1, dots, S$: the prover computes the columns
  of stage $s$, extends them to $cal(D)$, and sends the Merkle commitment
  $"rt"_s$ to the matrix whose rows are the values of those columns at the
  points of $cal(D)$, together with the AIR values of stage $s$. For
  $s < S$ the verifier replies with $chi^((s)) in KK^(c_s)$, which the stage
  $s + 1$ columns may use. After the last stage the verifier replies with the
  _aggregation challenge_ $zeta in KK$.

+ *Quotient.* The prover forms the aggregated constraint $hat(C)_zeta$ of
  @def:quotient, divides by $Z_Omega$, splits the quotient into the $q$
  chunks $Q_0, dots, Q_(q-1)$ of degree less than $N$, extends them to
  $cal(D)$ and sends the Merkle commitment $"rt"_(S+1)$ to them. The verifier
  replies with an _out-of-domain point_ $xi in KK$.

+ *Out-of-domain evaluations.* The prover sends the values
  $
    hat(f)(xi omega^o) quad "for every committed column" f "and every" o in Gamma,
  $
  and the values $hat(Q)_0 (xi), dots, hat(Q)_(q-1)(xi)$. Here $Gamma subset ZZ$
  is the set of opening offsets of $"cfg"$, and a negative offset means
  $omega^(-abs(o))$. Write $bold(v)$ for the tuple of all these values. The
  verifier replies with _batching challenges_ $bold(mu) in KK^2$.

+ *Low-degree test.* Write $Gamma = {o_1, dots, o_(abs(Gamma))}$ for the
  opening offsets in the order fixed by the circuit description, and, for each
  $i$, let $f_(i,1), dots, f_(i,n_i)$ be the committed columns that are opened
  at $xi omega^(o_i)$ --- among the fixed columns, the columns of every stage
  and the quotient chunks. Let $g_0 : cal(D) -> KK$ be the function
  $
    g_0 (x) := sum_(i=1)^(abs(Gamma)) mu_1^(abs(Gamma) - i) dot
      frac(1, x - xi omega^(o_i)) dot
      sum_(j=1)^(n_i) mu_2^(n_i - j) dot (f_(i,j)(x) - hat(f)_(i,j)(xi omega^(o_i))).
  $
  The prover and the verifier then run the FRI protocol of @sec:fri on $g_0$.

Both sums are Horner evaluations in a single challenge: $mu_2$ batches the
columns opened at one point, and $mu_1$ batches across the opening points.
Neither is a random linear combination with independent coefficients, and the
nesting means the coefficient of a given column is a product
$mu_1^(a) mu_2^(b)$ rather than a single power; @sec:deviations returns to
this. Note also that the columns opened at different offsets need not be the
same: an offset is present in $Gamma$ because some constraint refers to that
row, and only the columns that constraint reads are opened there.

The value $g_0 (x)$ is a _DEEP quotient_ @EPRINT:BGKS19: it is a low-degree
function precisely when every committed column agrees with a polynomial of
degree less than $N$ _and_ the claimed out-of-domain values are the
evaluations of those polynomials. Sampling $xi$ from the whole of $KK$,
rather than from $cal(D)$, is what lets a single evaluation pin down the
committed polynomial; it is the difference between DEEP-FRI and plain FRI,
and it is what makes the soundness error depend on $abs(KK)$ rather than on
$abs(cal(D))$.

The verifier's algebraic check is separate from the low-degree test, and uses
only the out-of-domain values:

#definition(title: "Out-of-domain constraint check")[
  Given $bold(v)$, the public statement $bold(p)$ and the challenges
  $chi, zeta$, the verifier evaluates the aggregated constraint
  $hat(C)_zeta$ at $xi$ by substituting the claimed values $bold(v)$ for the
  trace variables, and accepts this check if
  $
    hat(C)_zeta (xi) = Z_Omega (xi) dot sum_(i = 0)^(q - 1) xi^(i N) dot hat(Q)_i (xi).
  $
] <def:ood-check>

This is the _algebraic linking identity_ of the protocol: it is the only
place where the constraints of $cal(C)$ are used, and it is checked at a
single point of $KK$. Everything else in the protocol exists to make the
values $bold(v)$ trustworthy.

== FRI <sec:fri>

FRI @ICALP:BBHR18 tests that a function $g_0 : cal(D) -> KK$ is close to
$"RS"[cal(D), rho abs(cal(D))]$. The configuration fixes layer exponents
$m_0 = n_"ext" > m_1 > dots.c > m_L$; layer $i$ lives on the domain
$cal(D)_i$ of size $2^(m_i)$ obtained by raising $cal(D)$ to the power
$2^(m_0 - m_i)$, and folding from layer $i$ to layer $i + 1$ has arity
$2^(m_i - m_(i+1))$.

+ *Commit phase.* The prover sends a Merkle commitment to $g_0$, grouping the
  $2^(m_0 - m_1)$ values that share a layer-$1$ preimage into one row, so that
  a single opening reveals a whole folding group. For $i = 1, dots, L$ the
  verifier sends a folding challenge $beta_i in KK$ and the prover sends a
  commitment to
  $
    g_i := "Fold"_(beta_i)(g_(i-1)),
  $
  the unique function on $cal(D)_i$ whose value at $y$ is the evaluation at
  $beta_i$ of the interpolant of the $2^(m_(i-1) - m_i)$ values of $g_(i-1)$
  above $y$. For the last layer the prover sends $g_L$ in the clear.

+ *Query phase.* The verifier picks $t$ indices uniformly in
  $[0, 2^(m_0))$. For each index it opens the corresponding folding group of
  every layer, checks each Merkle opening, and checks that folding the group
  of layer $i$ with $beta_(i+1)$ gives the opened value of layer $i + 1$,
  down to $g_L$.

+ *Final check.* The verifier interpolates $g_L$ and checks that its
  coefficients of index at least $rho dot 2^(m_L)$ vanish, that is that $g_L$
  is a codeword of $"RS"[cal(D)_L, rho 2^(m_L)]$.

Layer $0$ is committed even though the verifier can compute $g_0$ at any
queried point from the openings of @sec:interactive. The consistency check
between the two --- the value recomputed from the stage openings against the
value opened from the layer-$0$ commitment --- is what ties the low-degree
test to the committed trace, and it is performed at every queried index.

== Fiat-Shamir <sec:fs>

The interactive protocol is made non-interactive in the usual way: the
verifier's messages are replaced by outputs of $cal(O)$ on the transcript so
far. The transcript is seeded, then absorbs each prover message and emits
each verifier message in the order of @sec:interactive and @sec:fri, and the
query indices are drawn last.

Two features of the compilation are specific to the implementation.

*Grinding.* After the last folding challenge the transcript emits one further
element $c^* in KK$. The prover must find a nonce $"nc" in FF$ with
$
  cal(O)(c^*, "nc")_1 < p slash 2^b,
$
and sends it; the verifier recomputes the check. The $t$ query indices are
then derived from $(c^*, "nc")$. Grinding raises by $b$ bits the cost of
resampling the query set, which is the step an adversary would otherwise
repeat cheaply after committing to everything else.

*Transcript seeding.* There are two modes. In the _standalone_ mode the
transcript is seeded with $vk$, the public statement $bold(p)$ and the
stage-$1$ commitment $"rt"_1$, so that $chi^((1))$ --- in ZisK, the LogUp
pair --- is a function of the committed trace. In the _global_ mode the
transcript is seeded with an externally supplied $chi^((1))$ and with nothing
else; the stage-$1$ commitment is absorbed afterwards, with the rest of the
transcript.

#remark(numbered: true, title: "The global mode does not bind the trace to the challenge")[
  In the standalone mode, $chi^((1))$ is drawn after $"rt"_1$ has entered the
  transcript, so a prover must fix the trace before learning the challenge,
  and the usual Fiat--Shamir argument applies. In the global mode it is not:
  $chi^((1))$ seeds the transcript and $"rt"_1$ enters it afterwards, so
  nothing in _this_ protocol prevents a prover from choosing the trace as a
  function of $chi^((1))$.

  This is deliberate and it is what makes proof aggregation possible: every
  instance in a run must compute its bus contribution under the _same_
  challenge, which cannot happen if each derives its own from its own
  commitment. The binding that the protocol gives up is supplied from
  outside, by whatever fixes $chi^((1))$ --- in ZisK, by a global challenge
  derived from an accumulation of all the stage-$1$ commitments of the run.

  For this document the consequence is a scoping one, and it is the reason
  @def:r-air-sat puts $chi$ in the statement. In the global mode the results
  below are statements _for a fixed $chi$_, and they carry no claim that
  $chi$ was chosen independently of the witness. Discharging that is the
  caller's obligation, and it is discharged where the global challenge is
  derived, not here.
] <rem:vadcop>

== The Verifier <sec:verifier>

Collecting the checks, the verifier $V(vk, (bold(p), chi), pi) in {0, 1}$
accepts if and only if all of the following hold.

+ The proof parses at the sizes dictated by $"cfg"$, and every field element
  in it is canonical.
+ Replaying the transcript of @sec:fs on the prover messages in $pi$
  reproduces the challenges $chi^((2)), dots$, $zeta$, $xi$, $bold(mu)$,
  $beta_1, dots, beta_L$ and $c^*$ used below, and in the standalone mode
  also $chi^((1))$.
+ The grinding check of @sec:fs holds for the nonce in $pi$.
+ The out-of-domain constraint check of @def:ood-check holds.
+ For each of the $t$ query indices: the Merkle openings of the fixed
  columns, of each stage and of the quotient chunks verify against
  $"rt"_(cal(C))$, $"rt"_1, dots, "rt"_S$ and $"rt"_(S+1)$; the value of
  $g_0$ recomputed from those openings agrees with the value opened from the
  layer-$0$ commitment; and the FRI folding checks of @sec:fri hold down to
  $g_L$.
+ The final polynomial $g_L$ has degree less than $rho 2^(m_L)$.

The verifier reads the witness only through the openings at $t$ points and
the $abs(bold(v))$ out-of-domain values, so its running time is polynomial in
$"cfg"$ and in the size of the AIR description, and independent of $N$ except
through the logarithmic depth of the Merkle openings.

== Commit-and-Prove <sec:commit-and-prove>

$"rt"_1$ is the first prover message, and it is a Merkle commitment to the
stage-$1$ columns, that is to the execution trace. A caller may therefore
treat it as a public output of the proof and impose its own conditions on it.
This is how the recursion binds a proof to a trace without re-proving
anything: it exposes $"rt"_1$ and hashes it, rather than hashing the witness.

Two cautions belong here rather than in the caller. First, $"rt"_1$ commits
to the stage-$1$ columns only. Cached columns are committed separately and
bound through $bold(p)$ (@def:local), and fixed columns through $vk$; a
caller that needs $"rt"_1$ to determine the whole witness must check that its
AIR places the columns it cares about in stage $1$. Second, the
commitment is to the _low-degree extension_ of the trace, not to the trace
itself; the two determine each other, but only for a codeword, which is what
the low-degree test establishes and only up to the proximity parameter.

== Deviations <sec:deviations>

The protocol above is a DEEP-ALI STARK with FRI as its low-degree test, and
each of its steps is standard. The following choices are not the textbook
ones, and each of them will cost a term or a hypothesis in the analysis; we
collect them here so that the analysis can refer to them.

+ *Power batching, at two levels.* The aggregation of the constraints
  (@def:quotient) uses powers of one challenge, and the batching of the DEEP
  quotients uses powers of two, nested: $mu_2$ within an opening point and
  $mu_1$ across opening points (@sec:interactive). None of the three is a
  random linear combination with independent coefficients. For the
  constraint aggregation the loss is linear in the number of constraints
  rather than a single inverse power of $abs(KK)$ (@rem:agg). For the DEEP
  batch the relevant proximity-gap statement is the one for low-degree
  parametrised curves rather than for affine spaces @EPRINT:BCIKS20, and the
  nesting means the curve has degree $abs(Gamma) dot max_i n_i$ in the pair
  $(mu_1, mu_2)$ rather than degree one in a single challenge.
+ *Non-uniform folding.* The FRI layer exponents are an arbitrary decreasing
  sequence, so folding arities vary from layer to layer; the usual analyses
  fix one arity.
+ *Early stopping.* FRI stops at layer $L$ and sends $g_L$ in the clear
  rather than folding to a constant.
+ *Capped Merkle trees.* Trees have arity $a$ and are capped at level $ell$
  (@def:mt), the capped level being transmitted and the root recomputed from
  it. Straight-line extraction has to be restated for this variant.
+ *Multiple opening offsets.* $Gamma$ is an arbitrary finite set of signed
  row offsets, so a constraint may refer to rows both above and below the
  current one.
+ *Externally supplied challenges.* The global mode of @rem:vadcop.
+ *One oracle.* The four hash roles are modelled as one (@rem:one-oracle).
