#import "../../../lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, corollary, definition, game, lemma,
  mult, negl, poly, proof, proposition, prover, remark, theorem, todo, verifier, vk,
)

// Protocols share the counter and the layout of the theorem-like environments.
#let protocol(body, title: none) = figure(
  body,
  kind: "theorem",
  supplement: [Protocol],
  numbering: "1",
  caption: title,
)

#let Fold = math.sans("Fold")
#let State = math.sans("State")
#let err = math.sans("err")
#let Gen = math.sans("Gen")
#let tr = math.sans("tr")
#let RS = math.sans("RS")
#let et = math.sans("et")
#let Powers = math.sans("Powers")
#let Block = math.sans("Block")
#let AccQueries = math.sans("AccQueries")

Every AIR of ZisK is proved with one proving system: a univariate STARK @EPRINT:BBHR18 in the DEEP-ALI style, with FRI @ICALP:BBHR18 as low-degree
test, Merkle trees as vector commitments, and the BCS transformation
@TCC:BenChiSpo16 to make it non-interactive. This section describes the full deployed protocol, the prover and verifier used by ZisK, so that
the soundness analysis refers to the actual protocol rather than to an
idealized one.

We describe the protocol as an interactive oracle proof, in which the
prover's committed functions are oracles and the challenges are uniformly
random, and prove its round-by-round knowledge soundness. Its compilation into
a non-interactive argument, with ZisK's Merkle trees and Fiat–Shamir
transcript, is the subject of @sec:compilation.

// - In @sec:stark-domains, @sec:rs-tools and @sec:iop-defs we fix the
//   notation: fields and domains; Reed–Solomon codes, proximity generators,
//   mutual correlated agreement, and the folding of a function along the
//   fibres of a power map; interactive oracle proofs and round-by-round
//   knowledge soundness.
// - In @sec:stark-constraints and @sec:stark-bus we turn the constraints of an
//   AIR, and its bus interactions, into polynomial identities.
// - In @sec:stark-protocol we present the setup, the relation that the protocol
//   proves, and the protocol.
// - In @sec:iop-rbr we prove its round-by-round knowledge soundness, and
//   instantiate the bound in the unique-decoding regime.

*Notation.* Throughout, $FF$ is the Goldilocks field, of order $p = 2^(64) - 2^(32) + 1$,
and $KK = FF[X] \/ (X^3 - X - 1)$ its cubic extension. We identify $FF$ with
the constant polynomials of $KK$ and write elements of $KK$ as
$c = c_0 + c_1 X + c_2 X^2$ with $(c_0, c_1, c_2) in FF^3$. Since
$2^(32)$ divides $p - 1$, for every $b <= 32$ the group $FF^times$ has a unique
subgroup $H_b$ of order $2^b$. We fix generators $omega_b$ of $H_b$ with
$omega_(b+1)^2 = omega_b$, and the _coset shift_ $sigma := 7$, a generator of
$FF^times$. For an integer $d >= 0$, we write $FF^(< d)[X]$ and
$KK^(< d)[X]$ for the sets of polynomials over $FF$ and over $KK$ of degree
less than $d$.

An AIR $cal(C)$ is proved at a trace height $N = 2^n$ with a
_blowup_ $2^k$, $k >= 1$, the _rate_ being $rho := 2^(-k)$. We write
$n_e := n + k$, and define
$
  H := H_n = {omega^r : r in [0, N)}, quad omega := omega_n, quad quad
  D := sigma H_(n_e) = {x_i := sigma omega_(n_e)^i : i in [0, 2^(n_e))}.
$
$H$ is the _trace domain_: row $r$ of the trace corresponds to the point
$omega^r$. $D$ is the _evaluation domain_; it is disjoint from $H$ because
$sigma in.not H_(n_e)$. For a column $T_j : [0, N) -> KK$ of a trace, its
_interpolant_ $hat(T)_j$ is the unique polynomial in $KK^(< N)[X]$ with
$hat(T)_j (omega^r) = T_j (r)$ for every $r$. For an integer
$o$, the polynomial $hat(T)_j (omega^o X)$ interpolates the column shifted by
$o$ rows, $r |-> T_j (r + o mod N)$. The _vanishing polynomial_ of $H$ is
$Z_H (X) := X^N - 1$, and the _first-row selector_ $L_1 in FF^(< N)[X]$ is
the polynomial with $L_1 (1) = 1$ and $L_1 (omega^r) = 0$ for
$r in (0, N)$.

== Reed–Solomon Codes <sec:rs-tools>

This section collects the facts about Reed–Solomon codes on which the
analysis of the protocol rests: list decoding up to the Johnson bound,
mutual correlated agreement, and folding.

Let $cal(L) subset FF^times$ be a coset of a subgroup of order a power of two.
For a degree bound $d$, the _Reed–Solomon code_ $RS[KK, cal(L), d]$ is the
set of functions $cal(L) -> KK$ that are evaluations of a polynomial in
$KK^(< d)[X]$, that is:
$
  RS[KK, cal(L), d] := { f : cal(L) -> KK : exists p in KK^(< d)[X], f(x) = p(x) thick forall x in cal(L) }
$
and $rho := d \/ abs(cal(L))$ is its rate. For a function $f : cal(L) -> KK$
and a set $S subset cal(L)$, $f[S]$ is the restriction of $f$ to $S$, so that
$f[S] = g[S]$ means that $f$ and $g$ agree on $S$; and for an integer $m$,
$cal(L)^m := {x^m : x in cal(L)}$ and $S^m := {x^m : x in S}$. For
functions $f, g : cal(L) -> KK$, $Delta(f, g)$ is the fraction of points of
$cal(L)$ where they differ, and for a set $cal(S)$ of functions,
$Delta(f, cal(S)) := min_(g in cal(S)) Delta(f, g)$.

For a code $cal(C)$ of functions $cal(L) -> KK$ and $t >= 1$, the
_$t$-interleaved code_ $cal(C)^t$ is the set of $t$-tuples
$(u_1, dots, u_t)$ of codewords, viewed as functions $cal(L) -> KK^t$,
$x |-> (u_1 (x), dots, u_t (x))$. Two tuples agree at a point only if all
their coordinates agree there, so a tuple of functions $(f_1, dots, f_t)$ is
$delta$-close to $cal(C)^t$ if and only if there is a set $S subset cal(L)$
with $abs(S) >= (1 - delta) abs(cal(L))$ on which every $f_j$ agrees with a
codeword: a _common_ agreement set. The analysis decodes the committed
columns in an interleaved code, because they are opened together, one row
per query.

#definition(title: "List Decoding")[
  For a code $cal(C) subset Sigma^(cal(L))$, a function $f : cal(L) -> Sigma$ and
  $delta in [0, 1]$, let
  $
    Lambda(cal(C), f, delta) := { u in cal(C) : Delta(f, u) <= delta }.
  $
  The code is _$(delta, ell)$-list decodable_ if
  $abs(Lambda(cal(C), f, delta)) <= ell$ for every $f$. Every code of
  minimum relative distance $delta_cal(C)$ is $(delta, 1)$-list decodable for
  $delta < delta_cal(C) \/ 2$, the _unique-decoding_ regime.
] <def:list>

The minimum distance of $RS[KK, cal(L), d]$ is $1 - (d - 1) \/ abs(cal(L))$, and up to
the Johnson bound its lists remain small, also when the code is interleaved
@EC:ACFY25.

#theorem(title: "Johnson Bound")[
  For every $eta in (0, 1 - sqrt(rho))$ and every $t >= 1$, the code
  $RS[KK, cal(L), d]^t$ is $(1 - sqrt(rho) - eta, 1 \/ (2 eta sqrt(rho)))$-list
  decodable.
] <thm:johnson>

A random linear combination of functions that are far from a code is, with
high probability, itself far from the code.

#definition(title: "Proximity Generator, Mutual Correlated Agreement")[
  A _proximity generator_ is a randomized algorithm $Gen$ that, on input a
  length $m >= 1$, outputs coefficients $(r_1, dots, r_m) in KK^m$ for a
  linear combination of $m$ functions. Let $cal(C) := RS[KK, cal(L), d]$. The
  generator $Gen$ has _mutual correlated agreement_ for $cal(C)$ with error
  $epsilon^"mca"$ if for every $f_1, dots, f_m : cal(L) -> KK$ and every
  $theta in [0, 1]$,
  $
    Pr_((r_1, dots, r_m) <- Gen(m)) [ exists S subset cal(L) "s.t." cases(
        delim: #none,
        abs(S) >= (1 - theta) dot abs(cal(L)),
        and exists u in cal(C)"," thin u[S] = sum_(j in [m]) r_j dot f_j [S],
        and exists i in [m]"," thin forall u' in cal(C)"," thin u'[S] != f_i [S]
      ) ] <= epsilon^"mca" (cal(C), m, theta).
  $
  We call $(r_1, dots, r_m)$ _bad_ for $(f_1, dots, f_m)$ at $theta$ if such
  a set $S$ exists.
] <def:mca>

The usual correlated agreement guarantees that, for good coefficients, the
combined functions agree with codewords on _some_ common set as large as the
agreement set of their combination. Mutual correlated agreement guarantees
it on _every_ such set, and it is this form that lets the analysis of FRI
track where agreement holds. ZisK combines functions with powers of a single
challenge.

#lemma(title: [@EPRINT:BCHKS25])[
  Let $cal(C) := RS[KK, cal(L), d]$ have rate $rho$. The _powers generator_,
  which samples $r <- KK$ and outputs
  $
    Powers(m; r) := (1, r, dots, r^(m - 1)) in KK^m,
  $
  has, for every $m >= 1$, mutual correlated agreement for $cal(C)$ with
  error
  $
    epsilon^"mca" (cal(C), m, theta) := cases(
      frac(m - 1, abs(KK)) dot (frac(2 (eta + 1 \/ 2)^5 + 3 (eta + 1 \/ 2) dot theta dot rho, 3 rho^(3 \/ 2)) dot abs(cal(L)) + frac(eta + 1 \/ 2, sqrt(rho)))\, quad & "if" theta < 1 - sqrt(rho)\,,
      1\, & "otherwise",
      gap: #0.8em
    )
  $
  where $eta := max(ceil(frac(sqrt(rho), (1 - sqrt(rho) - theta))), 3)$. We
  call $r$ _bad_ for $(f_1, dots, f_m)$ at $theta$ if $Powers(m; r)$ is.
] <lem:mca-jbr>

*Folding.* FRI folds a function along the blocks of a power map.

#definition(title: "Fold")[
  Let $m$ be an integer dividing $abs(cal(L))$. For $y in cal(L)^m$, the
  _block_ of $y$ is $Block(cal(L), m, y) := {x in cal(L) : x^m = y}$, a set
  of $m$ points; we write $Block(y)$ when $cal(L)$ and $m$ are clear. For
  $f : cal(L) -> KK$ and $y in cal(L)^m$, let $hat(p)_(f, y) in KK^(< m)[X]$
  be the polynomial with $hat(p)_(f, y)(x) = f(x)$ for every
  $x in Block(y)$. For $alpha in KK$, the _fold_ of $f$ is
  $
    Fold(f, m, alpha) : cal(L)^m -> KK, quad Fold(f, m, alpha)(y) := hat(p)_(f, y)(alpha).
  $
] <def:fold>

// $Fold(f, m, alpha)(y)$ is computed from the $m$ values of $f$ on $Block(y)$.
// The prover and the verifier of ZisK compute it in normalized form: if $x_y$
// is the first point of $Block(y)$, so that
// $Block(y) = {x_y zeta^j : j in [0, m)}$ for a primitive $m$-th root of unity
// $zeta$, and $P_y in KK^(< m)[U]$ interpolates $P_y (zeta^j) = f(x_y zeta^j)$,
// then $hat(p)_(f, y)(X) = P_y (X \/ x_y)$ and
// $Fold(f, m, alpha)(y) = P_y (alpha \/ x_y)$.
Writing $hat(p)_(f, y)(X) = sum_(i in [m]) f_i (y) X^(i - 1)$ defines the
_coefficient functions_ $f_1, dots, f_m : cal(L)^m -> KK$ of $f$, and then
$
  Fold(f, m, alpha) = sum_(i in [m]) alpha^(i - 1) dot f_i,
$
the combination of the coefficient functions by $Powers(m; alpha)$.

#lemma(title: [@EPRINT:GarMohWag25])[
  Let $m$ divide $d$ and $abs(cal(L))$, and let $cal(C) := RS[KK, cal(L), d]$
  and $cal(C)' := RS[KK, cal(L)^m, d \/ m]$. Then:
  + If $f in cal(C)$, then $Fold(f, m, alpha) in cal(C)'$ for every
    $alpha in KK$.
  + If $Powers$ has
    mutual correlated agreement for $cal(C)'$ with error $epsilon^"mca"$,
    then for every $f : cal(L) -> KK$ and every $theta in [0, 1]$,
    $
      Pr_(r <- KK) [ exists S subset cal(L) "s.t." cases(
          gap: #0.6em,
          delim: #none,
          abs(S^m) >= (1 - theta) dot abs(cal(L)^m),
          and exists u' in cal(C)'"," thin Fold(f, m, r)[S^m] = u'[S^m],
          and forall u in cal(C)"," thin u[S] != f[S]
        ) ] <= epsilon^"mca" (cal(C)', m, theta).
    $
    We call $r$ _bad_ for $f$ at $theta$ if such a set $S$ exists.
] <lem:fold>

// #proof[
//   (1) If $f = hat(f)[cal(L)]$ with $hat(f) in KK^(< d)[X]$, write
//   $hat(f)(X) = sum_(i in [m]) X^(i - 1) G_i (X^m)$ with
//   $G_i in KK^(< d \/ m)[X]$. Then $f_i = G_i [cal(L)^m]$, and
//   $Fold(f, m, alpha) = sum_i alpha^(i - 1) G_i [cal(L)^m] in cal(C)'$.

//   (2) Since $Fold(f, m, r) = sum_i r^(i - 1) f_i$, an $r$ that is bad for
//   $f$ at $theta$, with a set $S$, is bad for $(f_1, dots, f_m)$ at $theta$,
//   with the set $S^m$, unless every $f_i$ agrees on $S^m$ with a codeword
//   $u'_i in cal(C)'$. In that case $f$ agrees on $S$ with
//   $u := (sum_i X^(i - 1) u'_i (X^m))[cal(L)] in cal(C)$: for $x in S$, the
//   values $(f_i (x^m))_i$ are the coefficients of $hat(p)_(f, x^m)$, so
//   $f(x) = sum_i x^(i - 1) f_i (x^m) = sum_i x^(i - 1) u'_i (x^m) = u(x)$.
//   This contradicts the third condition, so the event is contained in the
//   event of @def:mca for $cal(C)'$, whose probability is at most
//   $epsilon^"mca" (cal(C)', m, theta)$.
// ]

== Interactive Oracle Proofs <sec:iop-defs>

Interactive oracle proofs @TCC:BenChiSpo16 combine interactive proofs with
probabilistically checkable proofs: in every round the prover sends a message
that the verifier may read only at the positions of its choice. We follow
@EC:ACFY25 and define them as a special case of
interactive oracle proofs of proximity, for _public-coin_ protocols, in which
the verifier's messages are uniformly random and independent of what it has
seen. For a ternary relation $cal(R) = {(bb(x), bb(y), bb(w))}$, the
_instance_ $bb(x)$ is read in full by the verifier, the _input_ $bb(y)$ only
as an oracle, and the _witness_ $bb(w)$ is known to the prover;
$L(cal(R)) := {(bb(x), bb(y)) : exists bb(w), (bb(x), bb(y), bb(w)) in cal(R)}$
is the language of $cal(R)$.

#definition(title: "Interactive Oracle Proof of Proximity")[
  A _$k$-round public-coin IOP of proximity_ (IOPP) for a ternary relation
  $cal(R)$ is a pair $(prover, verifier)$ of an interactive algorithm
  $prover$, the prover, and an interactive oracle algorithm $verifier$, the
  verifier. The prover receives $(bb(x), bb(y), bb(w))$; the verifier
  receives $bb(x)$ and oracle access to $bb(y)$. In round $i in [k]$ the
  prover sends a message $pi_i$, and the verifier replies with a uniformly
  random message $alpha_i$. A message $pi_i$ consists of _oracles_,
  functions that the verifier may query at points of its choice, and of plain
  values, which it reads in full. After round $k$ the verifier queries
  $bb(y)$ and the oracles, its queries being part of $alpha_k$, and outputs a
  bit $verifier^(bb(y), pi_1, dots, pi_k)(bb(x), alpha_1, dots, alpha_k)$.
  The IOPP has _perfect completeness_ if, for every $(bb(x), bb(y), bb(w)) in cal(R)$,
  $
    Pr_(alpha_1, dots, alpha_k) lr([ verifier^(bb(y), pi_1, dots, pi_k)(bb(x), alpha_1, dots, alpha_k) = 1 mid(|) mat(delim: #none, pi_1 <- prover(bb(x), bb(y), bb(w)); dots.v; pi_k <- prover(bb(x), bb(y), bb(w), alpha_1, dots, alpha_(k-1))) ]) = 1.
  $
] <def:iopp>

An _interactive oracle proof_ (IOP) is an IOPP whose input is
empty, $bb(y) = bot$, for a relation $cal(R) = {(bb(x), bot, bb(w))}$; we
then omit $bot$ and write $(bb(x); bb(w)) in cal(R)$,
$L(cal(R)) = {bb(x) : exists bb(w), (bb(x); bb(w)) in cal(R)}$ and
$verifier^(pi_1, dots, pi_k)(bb(x), alpha_1, dots, alpha_k)$.

A _transcript_ $tr = (pi_1, alpha_1, dots, pi_i, alpha_i)$ is the sequence
of the messages exchanged up to some round, and $tr || alpha$ its extension
by a message. Soundness is measured round by round @STOC:CCHLRR19, through a
function that assigns a state to each partial transcript. In the knowledge
version that we use @AC:BGKTTZ23 @EC:ACFY25, state $1$ means that a witness
can be extracted from the transcript, and a transcript in state $0$ is
flipped to state $1$ by the next challenge only with small probability,
unless it already determines a witness.

#definition(title: "State Function")[
  Let $(prover, verifier)$ be a $k$-round IOPP for $cal(R)$. A _state
  function_ is a function $State(bb(x), bb(y), tr) in {0, 1}$ with the
  following properties.
  + _Empty transcript._ $State(bb(x), bb(y), emptyset) = 0$ for every
    $(bb(x), bb(y))$.
  + _Prover moves._ If $tr$ ends with a verifier message, or is empty, then
    $State(bb(x), bb(y), tr || pi) = State(bb(x), bb(y), tr)$ for every
    prover message $pi$.
  + _Full transcript._ If $tr$ is a full transcript and
    $State(bb(x), bb(y), tr) = 0$, then $verifier$ rejects in the interaction
    described by $tr$, for every choice of its queries.
  + _Default._ If $State(bb(x), bb(y), tr) = 1$, then
    $State(bb(x), bb(y), tr') = 1$ for every extension $tr'$ of $tr$.
] <def:state>

The query phase of the verifier is folded into the last round: its queries
are part of $alpha_k$, and $verifier$'s decision is a function of the full
transcript and of the answers. The default property, from
@EPRINT:GarMohWag25, says that a prover who gets lucky in one round has won,
whatever happens later; it makes every prefix of a transcript in state $0$
also be in state $0$.

#definition(title: "Round-by-Round Knowledge Soundness")[
  A $k$-round IOPP $(prover, verifier)$ for $cal(R)$ has _round-by-round
  knowledge soundness_ with errors $(epsilon_1, dots, epsilon_k)$ and
  extraction time $et$ if it has a state function and a deterministic
  algorithm $E$, the _extractor_, running in time $et$, such
  that for every $(bb(x), bb(y))$, every $i in [k]$ and every partial
  transcript $tr = (pi_1, alpha_1, dots, alpha_(i-1), pi_i)$ with
  $State(bb(x), bb(y), tr) = 0$,
  $
    Pr_(alpha_i) [State(bb(x), bb(y), tr || alpha_i) = 1] > epsilon_i
    quad ==> quad (bb(x), bb(y), E(bb(x), bb(y), tr)) in cal(R).
  $
] <def:rbr>

The empty transcript is in state $0$ even when $(bb(x), bb(y)) in L(cal(R))$:
the state records whether a witness can be extracted from the transcript, not
whether one exists. For $(bb(x), bb(y)) in.not L(cal(R))$ the extractor
cannot succeed, so every round flips the state with probability at most
$epsilon_i$. A prover that convinces the verifier ends in state $1$, by the
full-transcript property, so some round flipped the state, and a union bound
gives soundness error $sum_i epsilon_i$; the compiled argument pays the
maximum $max_i epsilon_i$ instead, per query to the random oracle
(@sec:bcs). For an IOP we omit $bb(y) = bot$ and write $State(bb(x), tr)$
and $E(bb(x), tr)$.

== Constraint Polynomials <sec:stark-constraints>

The columns of a witness
$w = (bold(T), bold(v))$ follow the classes of @def:columns. The fixed
columns are given by the setup, and the cached columns by their commitment
in the publics. The proving system computes the witness columns in two
_stages_. The _first-stage_ columns are those of the AIR, over $FF$
(@def:air), and do not depend on any challenge. The _second-stage_ columns
are the bus columns of @sec:stark-bus, which depend on the challenges
$(alpha, gamma)$ sampled after the first stage is committed. The second
stage is over $KK$: its columns, its AIR values $bold(a)^((2))$ and the
_airgroup value_ $s$ of the instance, its bus contribution, take values in
$KK$, and its constraints are polynomials over $KK$ whose coefficients
include the challenges. We call the AIR with both stages the _expanded AIR_.
Its values are the public statement $bold(p) = (bold(p)_"ext", bold(p)_"pv")$
of @def:proof-values, the AIR values
$bold(a) = (bold(a)^((1)), bold(a)^((2)))$, split by stage, and $s$.

#definition(title: "Constraint Polynomial")[
  Let $C in KK[(X_j^((o)))_(j in [W], o in O), (Y_l)_(l in [V])]$ be a
  constraint, let $hat(T)_1, dots, hat(T)_W in KK^(< N)[X]$ be the
  interpolants of the columns of a trace $bold(T)$, and let
  $bold(v) in KK^V$ be values. The _constraint polynomial_ of $C$ is
  $
    hat(C)(X) := C((hat(T)_j (omega^o X))_(j in [W], o in O), bold(v)) in KK[X].
  $
] <def:constraint-poly>

At $X = omega^r$ the constraint polynomial evaluates $C$ at row $r$, so the
witness $(bold(T), bold(v))$ satisfies $C$ at every row if and only if
$hat(C)$ vanishes on $H$, that is, if and only if $Z_H$ divides $hat(C)$.
Moreover $deg(hat(C)) <= deg(C) dot (N - 1)$, where $deg(C)$ is the total
degree of $C$ in the column variables. The setup (@def:setup) bounds this
degree by $d_"max" := 2^k + 1$: a constraint of larger degree is rewritten by
introducing _intermediate columns_ $I$, witness columns each defined by a
constraint $I - E = 0$ for a subexpression $E$ of degree at most
$d_"max"$, and computed in the first stage in which $E$ can be computed.
After this rewriting the AIR has constraints $C_0, dots, C_(n_C - 1)$, all of
degree at most $d_"max"$, and we write $d <= d_"max"$ for the largest of
their degrees.

=== The Bus Columns <sec:stark-bus>

Let $chi = (alpha, gamma) in KK^2$ be the key of the bus argument
(@sec:arithmetization), and for an interaction
$iota = (b_iota, m_iota, bold(e)_iota)$ and a row $r$ write
$
  delta_iota (r) := alpha + hat(e)_gamma (b_iota, bold(e)_iota (r)), quad
  hat(e)_gamma (b, v) := b + sum_(j=1)^(ell_b) gamma^j v_j .
$
The interactions of the AIR are partitioned into
_row interactions_, whose multiplicity and message read the trace, and
_direct interactions_, whose multiplicity and message read only scalar values. The row interactions are
further partitioned into groups $G_1, dots, G_h$, chosen at setup so that the
constraints below have degree at most $d_"max"$. As in @def:constraint-poly,
substituting the interpolants of the columns into $m_iota$ and $delta_iota$
gives polynomials $hat(m)_iota, hat(delta)_iota in KK[X]$ with
$hat(m)_iota (omega^r) = m_iota (r)$ and
$hat(delta)_iota (omega^r) = delta_iota (r)$. The key enters the constraints
below as coefficients, which is why the constraint polynomials have
coefficients in $KK$.

#definition(title: "Bus Columns")[
  The second stage of an AIR proof commits to the following columns, with
  the following constraints, each of which must vanish on $H$:
  + For each group $G_t$, the _fraction column_
    $"im"_t (r) := sum_(iota in G_t) m_iota (r) \/ delta_iota (r)$,
    with the constraint polynomial:
    $
      hat("im")_t (X) dot product_(iota in G_t) hat(delta)_iota (X) - sum_(iota in G_t) hat(m)_iota (X) product_(iota' in G_t \\ {iota}) hat(delta)_(iota') (X).
    $
  + The _running sum column_
    $"S"(r) := sum_(r' <= r) sum_(t=1)^h "im"_t (r')$, with the constraint polynomial:
    $
      hat("S")(X) - hat("S")(omega^(-1) X) dot (1 - L_1 (X)) - sum_(t=1)^h hat("im")_t (X).
    $
  The fractions of the direct interactions are added once. Some of them are
  committed as second-stage AIR values $"im"^"dir"_u$, constrained like the
  fraction columns; the remaining ones are combined into a single fraction
  $nu \/ Delta$ computed in place from the AIR values. The _bus contribution_
  of the proof is an _airgroup value_ $s in KK$ constrained at the last row by the polynomial:
  $
    L_1 (omega X) dot ((s - hat("S")(X) - sum_u "im"^"dir"_u) dot Delta - nu).
  $
] <def:bus-columns>

#lemma(title: "Bus Contribution")[
  Let $w$ be a witness and $chi$ a key such that $delta_iota (r) != 0$ for every
  row interaction and every row, and such that the denominators of the direct
  interactions do not vanish. If the bus columns and $s$ satisfy the
  constraints of @def:bus-columns, then
  $
    s = sum_(r=0)^(N-1) sum_("row" iota) frac(m_iota (r), delta_iota (r)) + sum_("direct" iota) frac(m_iota, delta_iota) = BusCont_chi (cal(I), w),
  $
  where, in the notation of @def:interaction, a direct interaction is an
  interaction whose multiplicity is multiplied by the first-row selector, so
  that it is counted once.
] <lem:bus-contribution>

#proof[
  The fraction constraints determine $"im"_t (r)$ uniquely when the
  denominators are nonzero. At $X = omega^0$ the running-sum constraint gives
  $"S"(0) = sum_t "im"_t (0)$, since $L_1 (1) = 1$; at $X = omega^r$ with
  $r > 0$ it gives $"S"(r) = "S"(r - 1) + sum_t "im"_t (r)$. Hence
  $"S"(N - 1) = sum_r sum_t "im"_t (r)$, which is the sum over all rows and
  all row interactions. At $X = omega^(N - 1)$ the selector
  $L_1 (omega X) = L_1 (1) = 1$ is active, and the last constraint gives $s$ as stated; at every other row
  it is void. The last equality is the definition of $BusCont_chi$
  (@def:fingerprint), grouping the row terms by message.
]

== The Protocol <sec:stark-protocol>

We fix an AIR and its trace height $N = 2^n$ and blowup $2^k$. The FRI
schedule fixes the number $R$ of folding rounds and the _folding factors_
$m_1, dots, m_R$, powers of two with $m_1 dot dots dot m_R$ dividing $N$. The layers of FRI are
$
  cal(L)_0 := D, quad cal(L)_i := cal(L)_(i-1)^(m_i), quad N_0 := N, quad N_i := N_(i-1) \/ m_i, quad cal(C)_i := RS[KK, cal(L)_i, N_i]
$
for $i in [R]$, so that $cal(C)_0 = RS[KK, D, N]$, every $cal(C)_i$ has rate
$rho$, and by @lem:fold the fold of a codeword of $cal(C)_(i-1)$ with
factor $m_i$ is a codeword of $cal(C)_i$. We write $2^(b_i) := abs(cal(L)_i)$,
so that $b_0 = n_e$, and for a point $x in cal(L)_0$ we write $x^((0)) := x$
and $x^((i)) := (x^((i-1)))^(m_i) in cal(L)_i$. We also write
$cal(C)^+ := RS[KK, D, N + 1]$, of rate $rho^+ := rho + 1 \/ abs(D)$, for the
code in which the analysis decodes the committed columns (@rem:off-by-one).

The _setup_ fixes everything about an AIR that does not depend on a
particular proof.

#definition(title: "Setup")[
  The _setup_ is a deterministic, public procedure, run once for a version of
  ZisK, whose input is the description of the chips and the
  security target. For every chip it fixes:
  + The trace height $N = 2^n$, the blowup $2^k$, the FRI schedule and the
    number of queries $q$, and, for the compiled argument, the arity $a$
    and the verification level $L$ of the Merkle trees and the grinding bits
    $g_"pow"$.
  + The rewriting of the constraints into constraints of bounded degree with
    intermediate columns (@sec:stark-constraints), the grouping of the
    interactions into fraction columns (@sec:stark-bus), the order
    $C_0, dots, C_(n_C - 1)$ of the constraints, and the orderings $kappa$ and
    $kappa_o$ of the evaluations used by @prot:stark.
  + The evaluations on $D$ of the fixed columns, and a commitment to them,
    which is the verification key $vk_cal(C)$ of the chip.
  It also generates the recursive verifiers and their verification keys
  (@sec:relations-def). The setup does not depend on the program: the program
  code, which is cached data of the Rom chip, is committed once per program,
  and its root is one of the publics.
] <def:setup>

After the rewriting, the AIR has $W$ columns, of which the fixed ones are
given by the setup, and constraints $C_0, dots, C_(n_C - 1)$ of degree at most
$d$ that read the offsets $O$. Let $cal(E)$ be the set of pairs $(f, o)$ such
that column $f$ is read at offset $o$ by some constraint, together with the
pairs $(q_t, 0)$ for the quotient chunks $q_0, dots, q_(d-2)$ below; let $O_(cal(E))$
be the set of offsets occurring in $cal(E)$ and
$t_o := abs({f : (f, o) in cal(E)})$. The orderings of the setup are
bijections $kappa : O_(cal(E)) -> [0, abs(O_(cal(E))))$ and
$kappa_o : {f : (f, o) in cal(E)} -> [0, t_o)$.

The protocol proves the constraints of the AIR after the setup's rewriting,
with the bus key and the bus contribution in the instance. We call the
columns of all stages, including the intermediate and bus columns, and the AIR
values of both stages, the _expanded witness_.

#definition(title: "Expanded AIR Relation")[
  For $tau in [M]$, $cal(R)_"STARK"^((tau))$ is the set of pairs
  $((bold(p), chi, s); (bold(T)^+, bold(a)^+))$ such that $bold(T)^+$ assigns
  to every column of the expanded AIR, at every row of $[0, N)$, a value in
  $FF$ for the fixed, cached and first-stage columns and in $KK$ for the
  second-stage ones, the fixed columns taking their prescribed values,
  $bold(a)^+ = (bold(a)^((1)), bold(a)^((2)))$ with $bold(a)^((1))$ over
  $FF$, and every constraint
  $C_0, dots, C_(n_C - 1)$ of the expanded AIR holds at every row, with
  the values $bold(p)$, $bold(a)^+$ and $s$ of @sec:stark-constraints and
  the challenges $chi$ as coefficients.
] <def:r-stark>

The relation $cal(R)_"AIR"^((tau))$ of @def:r-air, whose statement is
$(bold(p), chi, s, "com")$ and whose witness is $w = (bold(T), bold(v))$,
differs from it in three respects.
- *Witness.* $bold(T)$ consists of the fixed, cached and first-stage columns,
  and the AIR values of $bold(v)$ are $bold(a)^((1))$. The intermediate
  columns, the bus columns and $bold(a)^((2))$ are functions of $(w, chi)$,
  which the constraints force.
- *Commitments.* $cal(R)_"AIR"^((tau))$ binds the witness to the trace
  commitment $"com"$, and its local satisfaction requires the cached columns
  to open the commitment carried in $bold(p)$. Both are properties of the
  compiled argument (@sec:binding).
- *Bus contribution.* The constraints force $s = BusCont_chi (cal(I)_tau, w)$
  only when the key is not a pole of the witness. For a witness $w$, a key
  $chi$ is a _pole_ of $w$ if a
  denominator $delta_iota (r)$ of a row interaction, or a denominator of a
  direct interaction, vanishes.

#lemma(title: "From the Expanded to the AIR Relation")[
  Let $((bold(p), chi, s); (bold(T)^+, bold(a)^+)) in cal(R)_"STARK"^((tau))$,
  and let $w = (bold(T), bold(v))$ be its restriction to the fixed, cached
  and first-stage columns, with values $bold(v)$ whose AIR values are the
  first-stage ones $bold(a)^((1))$ and whose publics and proof values are
  $bold(p)$. If $chi$ is not a pole of $w$, then $w$ satisfies every
  constraint of the AIR before the rewriting, and
  $s = BusCont_chi (cal(I)_tau, w)$.
] <lem:r-stark>

#proof[
  An intermediate column $I$ is constrained by $I - E = 0$, so it equals the
  subexpression it replaces, and every original constraint holds. If $chi$ is
  not a pole of $w$, @lem:bus-contribution applies to the bus columns and to
  $s$.
]

#remark(numbered: true, title: "Poles")[
  At a pole the bus constraints do not determine $s$. If
  $delta_iota (r) = 0$ for a row interaction $iota$ of a group $G_t$ with
  $m_iota (r) = 0$, the fraction constraint of @def:bus-columns holds at row
  $r$ for every value of $"im"_t (r)$, and the prover may choose that value,
  and with it $s$, freely. Since $chi$ is part of the instance, an IOP for
  $cal(R)_"STARK"^((tau))$ cannot exclude this. In ZisK the key is derived
  after the witness is committed (@sec:tree), and a fixed witness has a pole
  at a uniformly random key with probability at most
  $(N abs(cal(I)_tau) + abs(cal(I)_tau)) \/ abs(KK)$: for every $gamma$, each
  row of each interaction excludes one value of $alpha$. The binding lemma of
  @sec:compilation charges this probability.
] <rem:poles>

We describe the protocol as an IOP (@sec:iop-defs). Its instance is the public
statement, the bus key and the bus contribution; the key is an input rather
than a challenge because ZisK derives it once for all the AIR proofs of an
execution (@sec:tree).

#protocol(title: "ZisK Proving Protocol")[
  *Inputs.* The instance is $bb(x) = (bold(p), chi, s)$, with $chi = (alpha, gamma)$.
  In the honest case, the prover holds an expanded witness
  (@def:r-stark) for $bb(x)$.

  *Interaction phase.*
  + *Trace (Stages 1 and 2).* The prover sends the oracles $D -> FF$ of the
    cached and first-stage columns, including the intermediate columns of
    that stage, and the first-stage AIR values $bold(a)^((1))$, over $FF$. It
    then sends the oracles $D -> KK$ of the bus columns of @def:bus-columns,
    computed with $chi$,
    and of the remaining intermediate columns, and the second-stage AIR
    values $bold(a)^((2))$. In the honest case every oracle is the evaluation
    on $D$ of the interpolant of its column. Together with the evaluations of
    the fixed columns, these oracles form the tuple
    $bold(f) := (f_1, dots, f_W)$. The verifier samples $v_c <- KK$.
  + *Quotient (Stage 3).* The prover sends oracles
    $bold(q) := (q_0, dots, q_(d-2))$, $q_t : D -> KK$. In the honest case
    $
      hat(Q)(X) := frac(sum_(j < n_C) v_c^j dot hat(C)_j (X), Z_H (X)) = sum_(t = 0)^(d - 2) (X^N)^t dot hat(q)_t (X), quad hat(q)_t in KK^(< N)[X],
    $
    which is in $KK^(< (d - 1) N)[X]$ because
    $deg(hat(C)_j) <= d (N - 1)$, and $q_t := hat(q)_t|_D$. The verifier
    samples $xi <- KK$.
  + *Evaluations (Stage 4).* The prover sends
    $bold(y) := (y_(f, o))_((f, o) in cal(E))$; in the honest case
    $y_(f, o) := hat(f)(xi omega^o)$. The verifier samples $v_1, v_2 <- KK$.
  + *FRI (Stage 5).* Let $F : D -> KK$ be the _DEEP function_
    $
      F := sum_(o in O_(cal(E))) v_1^(kappa(o)) sum_(f : (f, o) in cal(E)) v_2^(kappa_o (f)) dot g_(f, o),
      quad g_(f, o) (x) := frac(f(x) - y_(f, o), x - xi omega^o).
    $
    The prover sends an oracle $F_0 : cal(L)_0 -> KK$; in the honest case
    $F_0 := F$. For $i = 1, dots, R$, the verifier samples $beta_i <- KK$
    and the prover sends $F_i : cal(L)_i -> KK$; in the honest case
    $F_i := Fold(F_(i-1), m_i, beta_i)$. The last function, $F_R$, is sent
    in full, as its $abs(cal(L)_R)$ values.
  + *Queries.* The verifier samples $x_1, dots, x_q <- cal(L)_0$.

  *Decision phase.* The verifier accepts if and only if:
  + _Constraint check._ With $bold(v)$ the values of @sec:stark-constraints,
    $
      sum_(j < n_C) v_c^j dot C_j ((y_(f, o))_((f, o)), bold(v)) = (xi^N - 1) sum_(t = 0)^(d - 2) xi^(t N) dot y_(q_t, 0).
    $
  + _Final function check._ $F_R in cal(C)_R$.
  + _Local fold checks._ For every query $x = x_ell$: the verifier computes
    $F(x)$ from the values of the oracles $bold(f), bold(q)$ at $x$ and
    checks $F(x) = F_0 (x)$; and for every $i in [R]$ it reads $F_(i-1)$ on
    $Block(cal(L)_(i-1), m_i, x^((i)))$, computes
    $Fold(F_(i-1), m_i, beta_i)(x^((i)))$ from these values, and checks that
    it equals $F_i (x^((i)))$.
] <prot:stark>

The honest prover's functions satisfy every check. Its constraint
polynomials vanish on $H$, so $Q$ is a polynomial and the constraint check
holds at every $xi$. Every $g_(f, o)$ is the evaluation of a polynomial in
$KK^(< N - 1)[X]$, so $F in cal(C)_0$, and by @lem:fold
$F_i in cal(C)_i$ for every $i$. The only exception is a point
$xi omega^o in D$, where $g_(f, o)$ is undefined. The verifier computes
$1 \/ (x - xi omega^o)$ without checking for it, and for $xi$ uniform in $KK$
it occurs with probability at most $abs(O_(cal(E))) abs(D) \/ abs(KK)$.

#remark(numbered: true, title: "The Off-by-One in the DEEP Quotients")[
  For an honest column in $KK^(< N)[X]$, the quotient $g_(f, o)$ is in
  $KK^(< N - 1)[X]$, but the low-degree test only certifies membership in
  $KK^(< N)[X]$. If $g_(f, o)$ agrees with a polynomial
  $hat(w) in KK^(< N)[X]$, then $f$ agrees with
  $(X - xi omega^o) hat(w) + y_(f, o) in KK^(< N + 1)[X]$. This is why the analysis decodes $bold(f)$ and $bold(q)$
  in $cal(C)^+ = RS[KK, D, N + 1]$. The slack is harmless. A column
  $hat(u) in KK^(< N + 1)[X]$ equals $hat(u)_0 + c Z_H$ with
  $hat(u)_0 in KK^(< N)[X]$, so it takes
  the same values on $H$. Since $hat(u)(omega^o X) = hat(u)_0(omega^o X) + c Z_H (X)$,
  the constraint polynomials of $hat(u)$ and $hat(u)_0$ are congruent
  modulo $Z_H$. A quotient with chunks in $KK^(< N + 1)[X]$ is in
  $KK^(< (d - 1) N + 1)[X]$.
] <rem:off-by-one>

== Round-by-Round Soundness <sec:iop-rbr>

#theorem(title: "Round-by-Round Knowledge Soundness")[
  Consider @prot:stark for the chip of type $tau$, with the parameters of
  @sec:stark-protocol, and assume that $Powers$ has mutual correlated
  agreement, with error $epsilon^"mca"$, for $cal(C)_0, dots, cal(C)_R$. Let
  $delta in (0, 1 - rho^+)$ be such that the interleaved code
  $(cal(C)^+)^(W + d - 1)$ is $(delta, ell)$-list decodable, with a
  list-decoding algorithm running in time $et_"RS"$, and let
  $theta in [0, 1]$ be a _tradeoff parameter_. Then @prot:stark is an IOP for
  $cal(R)_"STARK"^((tau))$ with round-by-round knowledge soundness errors
  $
    (epsilon^"ali", epsilon^"ood", epsilon^"deep", epsilon^"fold"_1, dots, epsilon^"fold"_R, epsilon^"qry")
  $
  and extraction time $et_"RS" + O(ell dot n_C dot N)$, where
  $
    epsilon^"ali" & <= frac(ell dot (n_C - 1), abs(KK)), &
    epsilon^"ood" & <= frac(ell dot d dot N + abs(O_(cal(E))) dot abs(D), abs(KK)), \
    epsilon^"deep" & <= epsilon^"mca" (cal(C)_0, abs(O_(cal(E))), delta) + sum_(o in O_(cal(E))) epsilon^"mca" (cal(C)_0, t_o, delta), quad &
    epsilon^"fold"_i & <= epsilon^"mca" (cal(C)_i, m_i, theta), \
    epsilon^"qry" & <= (1 - min{theta, delta})^q .
  $
] <thm:iop-rbr>

The rounds are named after the challenge that ends them: the constraint
combination $v_c$ (_ali_, for algebraic linking), the out-of-domain point
$xi$, the DEEP coefficients $(v_1, v_2)$, the folding challenges
$beta_1, dots, beta_R$ and the queries. The round in which the prover sends
$F_0$ ends with $beta_1$, and we count it as the first folding round. The
tradeoff parameter $theta$ trades the folding errors, which grow with
$theta$, against the query error, which the factor $1 - min{theta, delta}$
clamps at $1 - theta$ @EPRINT:GarMohWag25.

#proof[
  We first fix notation, then define a state function and an extractor, and
  finally bound the probability that each round flips the state.

  *Notation.* For a tuple $bold(u) = (hat(u)_f)_f$ of polynomials, one per
  column, we write $hat(C)_j [bold(u)]$ for the constraint polynomial of
  @def:constraint-poly computed from $bold(u)$ and the values $bold(v)$,
  which the instance and the transcript determine. For a tuple $bold(u)$ that also
  contains chunks $hat(u)_(q_0), dots, hat(u)_(q_(d-2))$, let
  $hat(Q)_bold(u) := sum_t X^(t N) hat(u)_(q_t)$ and
  $
    cal(D)_bold(u) (X) := sum_(j < n_C) v_c^j hat(C)_j [bold(u)](X) - Z_H (X) dot hat(Q)_bold(u) (X).
  $
  The constraint check for $bold(y)$ states that
  $sum_j v_c^j C_j ((y_(f, o)), bold(v)) = (xi^N - 1) sum_t xi^(t N) y_(q_t, 0)$;
  when $y_(f, o) = hat(u)_f (xi omega^o)$ for every $(f, o) in cal(E)$, it
  states that $cal(D)_bold(u) (xi) = 0$. We call $xi$ _bad_ if
  $xi omega^o in D$ for some $o in O_(cal(E))$. We write
  $Lambda_1 := Lambda((cal(C)^+)^W, bold(f), delta)$ and
  $Lambda_2 := Lambda((cal(C)^+)^(W + d - 1), (bold(f), bold(q)), delta)$,
  identifying codewords with their interpolants. Both lists have at most
  $ell$ elements (a list of the shorter tuple is at most as long), and the
  restriction of an element of $Lambda_2$ to its first $W$ coordinates is in
  $Lambda_1$.

  *The state function.* We define $State(bb(x), tr)$ for transcripts that end
  with a verifier message; on the other transcripts it is given by the
  prover-moves property of @def:state, and on the empty transcript it is $0$. In
  every round the state is $1$ if it already was, which gives the default
  property; otherwise:

  + _Ali._ $State(bb(x), tr || v_c) = 1$ if and only if some $bold(u) in Lambda_1$
    satisfies $sum_(j < n_C) v_c^j hat(C)_j [bold(u)] equiv 0 mod Z_H$.
  + _Out of domain._ $State(bb(x), tr || xi) = 1$ if and only if $xi$ is bad, or
    some $bold(u) in Lambda_2$ satisfies $cal(D)_bold(u) (xi) = 0$.
  + _DEEP._ $State(bb(x), tr || (v_1, v_2)) = 1$ if and only if the constraint
    check holds for $bold(y)$ and $Delta(F, cal(C)_0) <= delta$.
  + _Folding._ $State(bb(x), tr || beta_i) = 1$ if and only if $beta_i$ is bad
    for $F_(i-1)$ at $theta$ (@lem:fold, with $cal(L) = cal(L)_(i-1)$,
    $m = m_i$, $cal(C) = cal(C)_(i-1)$ and $cal(C)' = cal(C)_i$): there is
    $S subset cal(L)_(i-1)$ with
    $abs(S^(m_i)) >= (1 - theta) dot abs(cal(L)_i)$ such that
    $Fold(F_(i-1), m_i, beta_i)$ agrees on $S^(m_i)$ with a codeword of
    $cal(C)_i$, but $F_(i-1)$ agrees on $S$ with no codeword of
    $cal(C)_(i-1)$.
  + _Queries._ $State(bb(x), tr || (x_1, dots, x_q)) = 1$ if and only if the
    verifier accepts.

  The empty-transcript and prover-moves properties of @def:state hold by
  definition, and the default
  property by construction. The full-transcript property holds because, if
  the state of a full transcript is $0$, then in particular the verifier
  does not accept.

  *The extractor.* On $(bb(x), tr)$, where $tr$ ends with the first prover
  message, $E$ list-decodes $bold(f)$ to obtain $Lambda_1$, and outputs the
  values on $H$ of the first $bold(u) in Lambda_1$ such that every
  $hat(C)_j [bold(u)]$ vanishes on $H$, together with
  $(bold(a)^((1)), bold(a)^((2)))$, if there is one. On all other
  transcripts it outputs $bot$. It runs in time
  $et_"RS" + O(ell dot n_C dot N)$. The first-stage columns of its output
  are over $FF$: if $hat(u) in KK^(< N + 1)[X]$ agrees with an $FF$-valued
  oracle on a set $S subset D$ with $abs(S) >= (1 - delta) abs(D) > N$, then
  the coordinates of $hat(u)$ in an $FF$-basis of $KK$ containing $1$, other
  than the first, are polynomials over $FF$ of degree at most $N$ that vanish
  on $S$, since $D subset FF$; hence they are zero and $hat(u) in FF[X]$.

  *Bounding the errors.* We bound, for each round, the probability that the
  state flips from $0$ to $1$. Only in the first round do we need the
  extractor; in every other round the probability is bounded whatever the
  transcript.

  + *Ali.* Suppose
    $Pr_(v_c) [State(bb(x), tr || v_c) = 1] > ell (n_C - 1) \/ abs(KK)$. For a
    fixed $bold(u) in Lambda_1$, if some $hat(C)_j [bold(u)]$ does not vanish
    at some $h in H$, then $sum_j v_c^j hat(C)_j [bold(u)](h)$ is a nonzero
    polynomial in $v_c$ of degree at most $n_C - 1$, so
    $sum_j v_c^j hat(C)_j [bold(u)] equiv 0 mod Z_H$ for at most $n_C - 1$
    values of $v_c$. By a union bound over the at most $ell$ elements of
    $Lambda_1$, some $bold(u)$ makes every $hat(C)_j [bold(u)]$ vanish on $H$.
    Its values on $H$, with the AIR values, satisfy every constraint at
    every row, so $E$ outputs a witness of $cal(R)_"STARK"^((tau))$.

  + *Out of domain.* Suppose $State(bb(x), tr) = 0$: no $bold(u) in Lambda_1$
    makes $sum_j v_c^j hat(C)_j [bold(u)]$ divisible by $Z_H$. Then for every
    $bold(u) in Lambda_2$ the polynomial $cal(D)_bold(u)$ is nonzero, for
    otherwise $Z_H$ would divide the combination for the restriction of
    $bold(u)$, which is in $Lambda_1$. Its degree is at most $d N$: the
    columns of $bold(u)$ are in $KK^(< N + 1)[X]$, so
    $deg(hat(C)_j [bold(u)]) <= d N$, and $deg(Z_H hat(Q)_bold(u)) <= N + (d - 1) N$.
    Hence $Pr_xi [cal(D)_bold(u) (xi) = 0] <= d N \/ abs(KK)$, and a union
    bound over $Lambda_2$ and over the $abs(O_(cal(E))) dot abs(D)$ values of $xi$
    that are bad gives $epsilon^"ood"$.

  + *DEEP.* Suppose $State(bb(x), tr) = 0$, and that the constraint check holds
    for $bold(y)$; otherwise the new state is $0$. Write
    $G_o := sum_f v_2^(kappa_o (f)) g_(f, o)$, so that
    $F = sum_o v_1^(kappa(o)) G_o$. The functions $g_(f, o)$ are fixed before
    $(v_1, v_2)$ is sampled. Call $(v_1, v_2)$ good if $v_2$ is not bad, in
    the sense of @lem:mca-jbr at $delta$, for the tuple $(g_(f, o))_f$ of any
    $o in O_(cal(E))$, and $v_1$ is not bad at $delta$ for the tuple
    $(G_o)_(o in O_(cal(E)))$, which is fixed once $v_2$ is. Since $kappa$
    and every $kappa_o$ are bijections onto initial segments of $NN$, these
    are combinations by $Powers$, so $(v_1, v_2)$ is good except with
    probability $epsilon^"deep"$. We show that if $(v_1, v_2)$ is good then
    $Delta(F, cal(C)_0) > delta$.

    Suppose $Delta(F, cal(C)_0) <= delta$, and let $S subset D$, with
    $abs(S) >= (1 - delta) abs(D)$, be a set on which $F$ agrees with a
    codeword. As $v_1$ is good, every $G_o$ agrees with a codeword on $S$; as
    $v_2$ is good, every $g_(f, o)$ agrees on $S$ with a codeword
    $hat(w)_(f, o)$ of $cal(C)_0$. Then $f$ agrees on $S$ with
    $hat(u)_f^((o)) := (X - xi omega^o) hat(w)_(f, o) + y_(f, o) in KK^(< N + 1)[X]$,
    for every $o$ with $(f, o) in cal(E)$. Two such polynomials
    agree on $S$, and $abs(S) >= (1 - delta) abs(D) > N$ because
    $delta < 1 - rho^+$, so they are equal; call the common polynomial
    $hat(u)_f$. It satisfies $hat(u)_f (xi omega^o) = y_(f, o)$ for every
    $(f, o) in cal(E)$, since $xi$ is not bad. The tuple
    $bold(u) := (hat(u)_f)_f$, over the columns and the chunks, agrees with
    $(bold(f), bold(q))$ on $S$, so $bold(u) in Lambda_2$; and the constraint
    check for $bold(y)$ is $cal(D)_bold(u) (xi) = 0$. Hence
    $State(bb(x), tr) = 1$, a contradiction.

  + *Folding.* The oracle $F_(i-1)$ is fixed before $beta_i$ is sampled,
    and the state flips exactly when $beta_i$ is bad for $F_(i-1)$ at
    $theta$, which by @lem:fold has probability at most
    $epsilon^"mca" (cal(C)_i, m_i, theta)$.

  + *Queries.* Suppose $State(bb(x), tr) = 0$, and that the constraint check
    holds and $F_R in cal(C)_R$; otherwise the verifier rejects whatever the
    queries. Unwinding the definition of the state,
    $Delta(F, cal(C)_0) > delta$ and no $beta_i$ is bad for $F_(i-1)$ at
    $theta$. Let $AccQueries subset cal(L)_0$ be the set of queries that pass
    the local fold checks. By @clm:queries below,
    $abs(AccQueries) <= max{1 - theta, 1 - delta} dot abs(cal(L)_0)$. The
    $q$ queries are independent and uniform, so all of them are in
    $AccQueries$ with probability at most $(1 - min{theta, delta})^q$.

  It remains to prove @clm:queries.
]

#lemma(title: "Query Phase")[
  Let
  $
    AccQueries := { x in cal(L)_0 : F(x) = F_0 (x) "and" Fold(F_(i-1), m_i, beta_i)(x^((i))) = F_i (x^((i))) "for every" i in [R] }
  $
  be the set of queries that pass the local fold checks, and suppose that
  $F_R in cal(C)_R$ and that no $beta_i$ is bad for $F_(i-1)$ at $theta$.
  Then
  $
    abs(AccQueries) <= max{1 - theta, 1 - Delta(F, cal(C)_0)} dot abs(cal(L)_0).
  $
] <clm:queries>

#proof[
  Following @EPRINT:GarMohWag25, let $W_0 := AccQueries$ and
  $W_i := W_(i-1)^(m_i) subset cal(L)_i$ for $i in [R]$, the layers of the
  subgraph of accepted queries.

  _Folds are honest on the $W_i$._ For every $i in [R]$,
  $F_i [W_i] = Fold(F_(i-1), m_i, beta_i)[W_i]$: every $w in W_i$ is
  $x^((i))$ for some $x in AccQueries$, and the local fold check of $x$ at
  layer $i$ is this equality at $w$.

  _A small layer makes $W_0$ small._ Since $W_(i-1)$ is contained in the
  union of the blocks of the points of $W_i$, each of size $m_i$,
  $abs(W_(i-1)) \/ abs(cal(L)_(i-1)) <= abs(W_i) \/ abs(cal(L)_i)$. Hence, if
  $abs(W_i) < (1 - theta) abs(cal(L)_i)$ for some $i$, then
  $abs(W_0) < (1 - theta) abs(cal(L)_0)$.

  _Large layers propagate agreement._ Suppose
  $abs(W_i) >= (1 - theta) abs(cal(L)_i)$ for every $i$. We show by
  induction, from $i = R$ down to $0$, that $F_i$ agrees on $W_i$ with a
  codeword of $cal(C)_i$. For $i = R$ this holds since $F_R in cal(C)_R$.
  If $F_i [W_i] = u_i [W_i]$ with $u_i in cal(C)_i$, then
  $Fold(F_(i-1), m_i, beta_i)[W_i] = u_i [W_i]$ by honesty of the folds, and
  $W_i = W_(i-1)^(m_i)$ is large; since $beta_i$ is not bad for $F_(i-1)$ at
  $theta$, the set $S = W_(i-1)$ does not witness badness, so $F_(i-1)$
  agrees on $W_(i-1)$ with a codeword of $cal(C)_(i-1)$.

  In the first case $abs(AccQueries) < (1 - theta) abs(cal(L)_0)$. In the
  second, $F_0 [W_0] = u_0 [W_0]$ for some $u_0 in cal(C)_0$, and
  $F[W_0] = F_0 [W_0]$ by definition of $AccQueries$, so $F$ agrees with
  $u_0$ on $W_0$ and
  $abs(AccQueries) <= (1 - Delta(F, u_0)) abs(cal(L)_0) <= (1 - Delta(F, cal(C)_0)) abs(cal(L)_0)$.
]

@lem:mca-jbr discharges the hypothesis on $epsilon^"mca"$ of @thm:iop-rbr up to
the Johnson bound, and @thm:johnson bounds the list size $ell$; the natural
choice is $theta = delta$.

#corollary(title: "Johnson Regime")[
  Let $eta in (0, 1 - sqrt(rho^+))$ and $theta = delta := 1 - sqrt(rho^+) - eta$.
  Then @prot:stark has round-by-round knowledge soundness with
  $ell <= 1 \/ (2 eta sqrt(rho^+))$ and errors
  $
    epsilon^"ali" <= frac(ell dot (n_C - 1), abs(KK)), quad
    epsilon^"ood" <= frac(ell dot d dot N + abs(O_(cal(E))) dot abs(D), abs(KK)), \
    epsilon^"deep" <= epsilon^"mca" (cal(C)_0, abs(cal(E)), delta), quad
    epsilon^"fold"_i <= epsilon^"mca" (cal(C)_i, m_i, delta), \
    epsilon^"qry" <= (sqrt(rho^+) + eta)^q,
  $
  with $epsilon^"mca"$ as in @lem:mca-jbr, and extraction time polynomial in
  $abs(D) dot (W + d)$.
] <cor:iop-jbr>

#proof[
  Since $delta < 1 - sqrt(rho^+)$ and every $cal(C)_i$ has rate
  $rho <= rho^+$, @lem:mca-jbr applies to every code at $delta$, and
  @thm:johnson bounds the list size of $(cal(C)^+)^(W + d - 1)$ at $delta$
  by $1 \/ (2 eta sqrt(rho^+))$; lists of this size can be computed in
  polynomial time. @thm:iop-rbr with $theta = delta$ gives the errors, and
  $1 - min{theta, delta} = 1 - delta = sqrt(rho^+) + eta$.

  For the DEEP
  round, the error of @lem:mca-jbr at $delta < 1 - sqrt(rho)$ has the form
  $epsilon^"mca" (cal(C)_0, m, delta) = (m - 1) dot c$, with $c$ independent
  of $m$. Since $sum_(o in O_(cal(E))) t_o = abs(cal(E))$, the two terms of
  $epsilon^"deep"$ in @thm:iop-rbr add up to
  $
    (abs(O_(cal(E))) - 1) dot c + sum_(o in O_(cal(E))) (t_o - 1) dot c = (abs(cal(E)) - 1) dot c = epsilon^"mca" (cal(C)_0, abs(cal(E)), delta),
  $
  the error of batching all the quotients $g_(f, o)$ with the powers of a
  single challenge.
]

With $abs(KK) approx 2^(192)$, every error except $epsilon^"qry"$ is
negligible for the trace heights of ZisK, and the soundness of a proof is
governed by the query phase and by grinding, which enters at compilation
(@sec:bcs). @sec:theorem-i computes the resulting security levels.
