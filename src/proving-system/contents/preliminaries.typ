#import "../../lib.typ": Local, definition, negl, poly, remark

This section fixes the notation, recalls the arithmetization that the
protocol proves, and adds the two layers the protocol needs on top of it: the
encoding of a witness as a Reed--Solomon codeword, and the vector commitment
used to commit to such codewords. It closes with the configuration record
that parametrises every instance of the protocol.

== Notation and Parameters

Let $FF$ be a prime field of order $p$ and let $KK$ be an extension of $FF$ of
degree $d$, large enough that $abs(KK) = p^d$ is exponential in the security
parameter $lambda$; all verifier challenges are drawn from $KK$ and
all soundness errors below are measured against $abs(KK)$. For integers
$a <= b$ we write $[a, b]$ and $[a, b)$ for the closed and half-open integer
intervals and $[b] := [1, b]$. "PPT" means probabilistic polynomial time in
$lambda$, and $negl(lambda)$ and $poly(lambda)$ denote negligible and
polynomially bounded functions.

The protocol is analysed in the random-oracle model. We assume a single
random oracle $cal(O)$, used for the leaves and the internal nodes of the
vector commitment, for the Fiat--Shamir transcript and for the
proof-of-work check; the implementation instantiates these roles with
separate hash functions, and we treat them as domain-separated instances of
$cal(O)$ (@rem:one-oracle). We write $Q$ for a bound on the total number of
oracle queries an adversary makes.

== Arithmetization <sec:air>

The protocol proves that a witness satisfies an AIR.

#include "../../shared/air.typ"

Throughout this document we work with a single AIR type and suppress the
index $tau$, writing $cal(C)$, $N$, $W$, $D$, $V$, $bold(d)$, $beta$ and
$Local(bold(p), w)$. The recursion instantiates what follows once per type.

@def:air asks that every constraint polynomial vanish at every row. This is
the only _boundary condition_ we consider: constraints that are imposed on a
strict subset of the rows, such as a first-row or last-row condition, are
expressible by multiplying the constraint by a fixed selector column, and the
protocol below treats them no differently.

#remark(numbered: true, title: "One oracle")[
  The implementation uses four separately instantiable hash functions: one for
  the leaves of a Merkle tree, one for its internal nodes, one for the
  Fiat--Shamir transcript, and a fixed-width one for the proof of work. Modelling
  them as one oracle is a simplification. It is sound if the four are
  domain-separated instances of a single function, and it is the modelling
  under which the bounds below should be read.
] <rem:one-oracle>

=== Stages and challenges

The AIR of @def:air is static: its constraints are polynomials in the trace
variables and the AIR values alone. The arguments ZisK builds on top of an
AIR --- the lookup and permutation arguments that implement the buses
@EPRINT:Habock22b --- need columns that the prover can only compute _after_
seeing a verifier challenge, and constraints that mention that challenge.
The protocol therefore proves a _staged_ AIR.

#definition(title: "Staged AIR")[
  A _staging_ of an AIR $cal(C)$ into $S >= 1$ stages consists of a partition
  of the witness columns
  $
    J^"wit" = J^((1)) union.sq dots.c union.sq J^((S))
  $
  together with _challenge counts_ $c_1, dots, c_(S-1) in NN$. Writing
  $c := c_1 + dots.c + c_(S-1)$, the constraint polynomials of a staged AIR are
  allowed to depend on $c$ further variables $Z_1, dots, Z_c$, the
  _challenge variables_, which take values in $KK$; consequently the
  constraints and the AIR values of a staged AIR take values in $KK$ rather
  than in $FF$. The columns of the first stage are the ones that hold the
  execution trace proper; they depend on no challenge.

  A _challenge vector_ is a tuple $chi = (chi^((1)), dots, chi^((S-1)))$ with
  $chi^((s)) in KK^(c_s)$. For a fixed $chi$, binding the challenge
  variables to $chi$ turns the staged AIR into an ordinary AIR over $KK$, and
  we write $Local(bold(p), w; chi)$ for the predicate of @def:local of that
  AIR. The staging constrains the prover, not the predicate: the columns of
  $J^((s))$ must be determined before $chi^((s))$ is drawn, and may depend on
  $chi^((1)), dots, chi^((s-1))$.
] <def:staged>

In ZisK, $S = 2$: the first stage holds the execution trace, the second holds
the auxiliary columns of the bus arguments, and $c_1 = 2$, the two challenges
being the LogUp pair. We keep $S$ and the $c_s$ general, since the compiler
emits them per circuit.

== Polynomial Encoding <sec:encoding>

Fix a trace height $N = 2^n$ and assume $2^n$ divides $p - 1$, so that $FF^*$
has a subgroup
$
  Omega = ⟨omega⟩ subset FF^*, quad abs(Omega) = N,
$
of order $N$ with generator $omega$. We identify the row index $r in [N]$ with
the point $omega^r in Omega$; the row shift $r |-> r + 1$ of @def:air becomes
multiplication by $omega$, and row indices taken modulo $N$ become the group
structure of $Omega$.

#definition(title: "Trace polynomials and the constraint polynomial")[
  Let $w = (bold(T), bold(a))$ be a witness of height $N$. For every column
  $j in [W]$ let $hat(T)_j in KK[X]$ be the unique polynomial of degree less
  than $N$ with $hat(T)_j (omega^r) = T_j (r)$ for all $r in [N]$. For a
  constraint polynomial $C in cal(C)$ and a challenge vector $chi$, the
  _constraint polynomial_ of $C$ on $w$ is
  $
    hat(C)(X) := C(hat(T)_1 (X), dots, hat(T)_W (X), dots, hat(T)_1 (omega^D X), dots, hat(T)_W (omega^D X), bold(a), chi) in KK[X],
  $
  obtained by substituting $hat(T)_j (omega^k X)$ for the variable
  $X_j^((k))$, the AIR values for the variables $Y$, and $chi$ for the
  challenge variables $Z$.
] <def:trace-poly>

Write $Z_Omega (X) := X^N - 1$ for the vanishing polynomial of $Omega$. Since
$hat(C)(omega^r)$ is exactly the evaluation of $C$ at row $r$, the
satisfaction condition of @def:air becomes a divisibility condition.

#definition(title: "Quotient")[
  Let $chi$ be a challenge vector and $zeta in KK$. The _aggregated
  constraint_ of $cal(C) = {C_1, dots, C_(abs(cal(C)))}$ at $zeta$ is
  $
    hat(C)_zeta (X) := sum_(i = 1)^(abs(cal(C))) zeta^(i - 1) dot hat(C)_i (X),
  $
  and, when $Z_Omega$ divides $hat(C)_zeta$, the _quotient_ is
  $Q(X) := hat(C)_zeta (X) slash Z_Omega (X)$.
] <def:quotient>

#remark(numbered: true, title: "Satisfaction as divisibility")[
  A witness $w$ satisfies $cal(C)$ under $chi$ if and only if $Z_Omega$
  divides $hat(C)_i$ for every $i$, and then $Z_Omega$ divides
  $hat(C)_zeta$ for every $zeta$. Conversely, if some $hat(C)_i$ is not
  divisible by $Z_Omega$, then $Z_Omega$ divides $hat(C)_zeta$ for at most
  $abs(cal(C)) - 1$ values of $zeta$, since divisibility is a linear
  condition and the map $zeta |-> (1, zeta, dots, zeta^(abs(cal(C)) - 1))$
  meets any proper subspace in at most $abs(cal(C)) - 1$ points. Aggregating
  with the _powers_ of one challenge rather than with $abs(cal(C))$
  independent challenges is what makes this count linear in
  $abs(cal(C))$ rather than a single inverse power of $abs(KK)$; the
  implementation aggregates with powers.
] <rem:agg>

If every constraint has total degree at most $delta$ in the trace variables,
then $deg hat(C)_zeta < delta N$ and $deg Q < (delta - 1) N$. The quotient is
committed in $q := delta - 1$ chunks of degree less than $N$,
$
  Q(X) = sum_(i = 0)^(q - 1) X^(i N) dot Q_i (X), quad deg Q_i < N,
$
so that all committed polynomials have the same degree bound.

=== The evaluation domain

#definition(title: "Reed-Solomon code")[
  Let $cal(D) subset KK$ be a set with $abs(cal(D)) > N$. The
  _Reed--Solomon code_ $"RS"[cal(D), N]$ is the set of functions
  $f : cal(D) -> KK$ that agree with a polynomial of degree less than $N$.
  Its _rate_ is $rho := N slash abs(cal(D))$, and the relative Hamming
  distance of $f$ from the code is written $Delta(f, "RS"[cal(D), N])$.
] <def:rs>

The protocol evaluates the trace polynomials on a domain disjoint from
$Omega$. Fix a blowup exponent $nu >= 1$, put $n_"ext" := n + nu$,
assume $2^(n_"ext")$ divides $p - 1$, let $omega_"ext"$ generate the subgroup
of $FF^*$ of order $2^(n_"ext")$, and fix a shift $eta in FF^*$ outside that
subgroup. The _evaluation domain_ is the coset
$
  cal(D) := eta dot ⟨omega_"ext"⟩, quad abs(cal(D)) = 2^(n_"ext") = N slash rho, quad rho = 2^(-nu),
$
which is disjoint from $Omega$, so the quotient of @def:quotient may be
evaluated on all of $cal(D)$ without dividing by zero. The _low-degree
extension_ of a column $T_j$ is the restriction of $hat(T)_j$ to $cal(D)$; it
is a codeword of $"RS"[cal(D), N]$, and the prover commits to it rather than
to the column itself.

== Vector Commitment <sec:mt>

#include "../../shared/commitment.typ"

The protocol uses one such scheme, a Merkle tree over the random oracle,
applied to matrices whose rows are indexed by the evaluation domain.

#definition(title: "Merkle commitment")[
  Fix an _arity_ $a >= 2$ and a _cap level_ $ell >= 0$. The Merkle
  commitment to a matrix $bold(M) in KK^(abs(cal(D)) times u)$ hashes each
  row to a leaf, $cal(O)(M_(x, 1), dots, M_(x, u))$ for $x in cal(D)$, and
  then repeatedly hashes groups of $a$ consecutive nodes until a level of at
  most $a^ell$ nodes is reached; the commitment is the hash of that level. An
  _opening_ at $x in cal(D)$ consists of the row $bold(M)_x$, the $a - 1$
  siblings at each level above the leaf and below the cap, and the whole
  capped level.
] <def:mt>

Taking $ell = 0$ gives the usual Merkle tree; a positive cap level shortens
the authentication path at the cost of transmitting the capped level once per
proof, and the verifier recomputes the commitment from it. Committing to a
matrix rather than to a vector means that all columns of one stage are opened
together at a queried point, which is what the protocol needs.

We will use that a Merkle commitment over a random oracle is _straight-line
extractable_: from the list of oracle queries made before a commitment is
announced, one can reconstruct the only matrix the announcer can later open
it to, except with probability $O(Q^2 slash abs(KK))$.

== The Configuration <sec:cfg>

Every instance of the protocol is determined by an AIR together with the
following record. It is exactly the data the setup emits per circuit.

#figure(
  {
    set text(size: 9pt, hyphenate: false)
    table(
      stroke: 0.3pt,
      columns: (18%, 52%, 30%),
      align: (left, left, left),
      table.header([*Symbol*], [*Meaning*], [*Implementation*]),
      [$n$], [trace height exponent, $N = 2^n$], [`n_bits`],
      [$nu$], [blowup exponent, $rho = 2^(-nu)$], [`n_bits_ext` $-$ `n_bits`],
      [$S$, $(c_s)_s$], [stages and challenges per stage (@def:staged)], [`n_stages`, `challengesMap`],
      [$delta$], [maximum constraint degree; $q = delta - 1$ quotient chunks], [`air_max_degree`, `q_deg`],
      [$Gamma$], [opening offsets, a finite subset of $ZZ$], [`opening_points`],
      [$a$, $ell$], [Merkle arity and cap level (@def:mt)], [`arity`, `last_level_verification`],
      [$L$, $(m_0, dots, m_L)$], [number of FRI layers and their size exponents], [`n_fri_steps`, `fri_steps`],
      [$t$], [number of FRI queries], [`n_fri_queries`],
      [$b$], [proof-of-work bits], [`pow_bits`],
      [$theta$], [proximity parameter of the low-degree test], [`proximity_gap`],
    )
  },
  caption: [
    The configuration record $"cfg"$.
  ],
  kind: table,
) <tbl:cfg>

As an illustration of the orders of magnitude, ZisK's Final circuit is
configured with $n = 16$ and $nu = 4$, so $rho = 1 slash 16$; $S = 2$ stages
over $46$ fixed columns; $delta = 8$, hence $q = 7$ quotient chunks;
$Gamma = {-1, 0, 1, 2}$; Merkle arity $a = 4$ capped at $ell = 2$; FRI layer
exponents $(20, 16, 12, 8, 5)$, so $L = 4$ layers folded with arities
$16, 16, 16, 8$; $t = 54$ queries; and $b = 22$ grinding bits. The other
circuits differ in every one of these numbers.

The record contains one further Boolean, recorded here for completeness: the
transcript either absorbs the public inputs, the out-of-domain evaluations
and the final FRI polynomial directly, or absorbs a hash of each. The choice
changes the Fiat--Shamir transcript but none of the checks, and we fix the
first alternative in the description below.
