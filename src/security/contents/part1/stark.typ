#import "../../../lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, game, lemma, mult, negl,
  poly, proof, proposition, remark, theorem, todo, vk,
)

Every circuit of ZisK ---the AIRs of the zkVM and the recursive circuits of
@sec:tree --- is proved with one proving system: a (slightly modified) univariate STARK @EPRINT:BBHR18 in the DEEP-ALI style, with FRI @ICALP:BBHR18 as low-degree
test, Merkle trees as vector commitments, and the BCS transformation
@TCC:BenChiSpo16 to make it non-interactive. This section describes the full deployed protocol, the prover and verifier used by ZisK, so that
the soundness analysis of the next sections refers to the actual protocol
rather than to an idealized one.

*Notation.* Fix an AIR $cal(C)$ of width $W$ with $V$ AIR values, used at
height $N = 2^n$ (@sec:arithmetization). Let $H = chevron.l omega chevron.r
subset FF^times$ be the subgroup of order $N$ on which the trace is
interpolated, and $D = s_0 H'$ a coset of the subgroup $H'$ of order
$2^(n + k)$, the _evaluation domain_, where $2^k$ is the _blowup factor_ and
$rho = 2^(-k)$ the _rate_. For a column $T_j$ we write $hat(T)_j in
FF^(< N)[X]$ for its interpolant on $H$. All challenges are drawn from the
cubic extension $KK$. The parameters $k$, the folding schedule, the number of
queries $q$ and the grinding bits $g$ are fixed per circuit and listed in
@app:parameters.

== Commitments <sec:stark-commitments>

All commitments are Merkle trees over Poseidon2 @AFRICACRYPT:GraKhoSch23 in
the Goldilocks field. A tree has arity $4$: an internal node is the
compression of its four children by the Poseidon2 permutation of width $16$,
and a digest consists of $4$ field elements, about $256$ bits. When a group of
polynomials is committed, they are evaluated on $D$, and the leaf at position
$x in D$ is the sponge hash of the row of evaluations at $x$. A proof opens a
leaf by giving the row and an authentication path; to shorten proofs the paths
stop at a fixed level $L$ below the root, and the proof carries all
$4^L$ nodes of that level, which the verifier hashes into the root. The
compressed Final Verifier uses arity $2$ instead.

An AIR proof involves the following trees.
- The _fixed tree_ commits to the fixed columns of the AIR. It is computed
  at setup, and its root is the AIR's verification key $vk_cal(C)$: two AIRs
  with different fixed columns have different keys.
- A _custom tree_ commits to a group of cached columns. In ZisK the only
  one is the program ROM of the Rom AIR. It is computed once per program, and
  the AIR declares its root to be a public input: the root carried by the
  proof is tied to the coordinates of the public statement designated for it,
  so the cached columns are bound to $bold(p)$.
- The _stage-1 tree_ commits to the witness columns of the first stage. Its
  root $"root"_1$ and the AIR values of the first stage form the trace
  commitment of the proof.
- The _stage-2 tree_ commits to the columns of the bus argument, computed
  after the bus key is known.
- The _quotient tree_ commits to the quotient polynomial, split into chunks.
- The _FRI trees_ commit to the successive layers of the low-degree test.

== Protocol <sec:stark-protocol>

The prover holds a witness $(bold(T), bold(a))$; the verifier holds the
verification key and the inputs of the proof. The protocol proceeds in the
following stages, each ending with challenges drawn from the transcript of
@sec:transcripts.

+ *Stage 1: witness.* The prover commits to the witness columns of the first
  stage in the stage-1 tree. The first-stage AIR values are sent in the clear.

+ *Stage 2: bus argument.* Two challenges are drawn, which form the bus key
  $chi = (alpha, gamma) in KK^2$ of @sec:arithmetization. The prover computes
  the columns of the bus argument and commits to them in the stage-2 tree:
  - _grouped fractions_: for each group of interactions, a column holding
    $sum m_iota (w, r) \/ (alpha + hat(e)_gamma (b_iota, bold(e)_iota (w, r)))$
    over the interactions of the group, constrained by multiplying out the
    denominators; the groups are chosen so that these constraints stay within
    the degree bound;
  - the _running sum_ $"gsum"$, constrained by
    $"gsum"(r) = "gsum"(r - 1) dot (1 - L_1 (r)) + sum_j "im"_j (r)$, where
    $L_1$ selects the first row.
  Interactions whose multiplicity and message depend only on AIR values are
  not summed row by row. Their fractions are added once, at the last row,
  either as second-stage AIR values $"im"^"direct"_j$ sent in the clear or
  computed in place from the AIR values; schematically,
  $
    L_N (r) dot (s - "gsum"(r) - sum_j "im"^"direct"_j - "direct terms") = 0,
  $
  where $L_N$ selects the last row and $s$ is the bus contribution of the
  proof, an _airgroup value_ (a value of the proof that the recursion reads
  and aggregates). In the implementation the compression uses the first
  challenge and the denominators the second; we keep the notation of
  @sec:arithmetization, in which the roles are the opposite.

+ *Stage 3: quotient.* A challenge $v_c$ is drawn. With $C_1, dots, C_m$ the
  constraint polynomials of the AIR, evaluated on the interpolants of all
  committed columns and on the AIR values, the prover computes
  $
    Q(X) = frac(sum_(i=1)^m v_c^(i-1) C_i (X), Z_H (X)), quad Z_H (X) = X^N - 1,
  $
  splits it into chunks of degree less than $N$, and commits to them in the
  quotient tree. Constraints of degree larger than $2^k + 1$ are first
  reduced by introducing intermediate columns, committed with the stage in
  which they become computable, so that $deg Q < 2^k N$.

+ *Stage 4: out-of-domain evaluation.* A challenge $xi in KK$ is drawn. The
  prover sends the evaluations of every committed polynomial at the points
  $xi omega^o$, for $o$ in the set $O$ of row offsets at which the
  constraints read the columns (typically three offsets around the current
  row, more for precompiles that read several rows of a cycle). From these values, the
  AIR values and $s$, the verifier recomputes $sum_i v_c^(i-1) C_i (xi)$ and
  checks it against $Z_H (xi) Q(xi)$, where $Q(xi)$ is recombined from the
  evaluations of the chunks.

+ *Stage 5: low-degree test.* Two challenges $v_1, v_2$ are drawn, and the
  prover forms the DEEP polynomial
  $
    F(X) = sum_(o in O) v_1^(o') sum_(j) v_2^j frac(f_j (X) - f_j (xi omega^o), X - xi omega^o),
  $
  where $f_j$ ranges over the polynomials opened at $xi omega^o$ and $o'$ is
  the index of $o$ in $O$. FRI then proves that the evaluations of $F$ on $D$
  are close to a polynomial of degree less than $N$. Starting from $D$, each
  round folds the current layer by a factor of $2^(f)$ with a fresh challenge
  ---$f = 3$ for most rounds, a smaller last fold where the sizes do not
  divide---, and commits to the folded layer in a FRI tree whose leaves are
  the cosets that the next fold combines. When the layer has $2^5$ or $2^6$
  points the prover sends it in full as the _final polynomial_, and the
  verifier checks that it has the expected degree.

+ *Grinding and queries.* Let $c in KK$ be the last FRI challenge. The prover
  finds a nonce $nu$ such that the first output of the Poseidon2 permutation
  of width $4$ on $(c, nu)$ is smaller than $2^(64 - g)$. The query positions
  $x_1, dots, x_q in D$ are then derived from a fresh transcript that absorbs
  only $c$ and $nu$. For every query the prover opens all trees of stages 1,
  2 and 3, the fixed tree and the custom trees at $x_i$, and every FRI tree
  at the corresponding folded positions; the verifier checks the paths, the
  DEEP quotients at $x_i$ against the openings and the claimed evaluations,
  and the consistency of every fold.

The proof consists of the roots of the stage, quotient and FRI trees, the
truncated levels, the evaluations, the final polynomial, the AIR values, the
airgroup values, the nonce and the openings.

== Transcripts <sec:transcripts>

Challenges are derived with a Poseidon2 sponge of width $16$. Absorbed field
elements are buffered; when $12$ are pending, they are permuted together with
the first $4$ elements of the current state, and the $16$ outputs become both
the new state and the squeeze buffer. A challenge in $KK$ consumes $3$ squeezed
elements. Large objects ---the public inputs of a recursive circuit, the
vector of evaluations and the final polynomial--- are first hashed into a
$4$-element digest, and the digest is absorbed instead.

What a transcript absorbs depends on the kind of circuit (@tbl:transcripts).

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (0.7fr, 2fr, 2fr),
      align: (left, left, left),
      table.header([*Step*], [*AIR proof*], [*Recursive circuit*]),
      [seed],
      [the global challenge (@sec:tree) only],
      [the verification key, the digest of the public inputs, $"root"_1$],

      [stage 2],
      [draw $alpha, gamma$; absorb $"root"_2$ and the stage-2 AIR values],
      [draw the stage-2 challenges, if any; absorb $"root"_2$ and the stage-2 AIR values],

      [stage 3], [draw $v_c$; absorb the quotient root], [same],
      [stage 4], [draw $xi$; absorb the digest of the evaluations], [same],
      [stage 5],
      [draw $v_1, v_2$; per FRI round, draw a folding challenge and absorb the next root, then the digest of the final polynomial],
      [same],

      [queries], [fresh sponge over the last challenge and the nonce], [same],
    )
  },
  caption: [Absorption order of the Fiat–Shamir transcript.],
  kind: table,
) <tbl:transcripts>

Three features of the AIR transcript matter for the analysis.

+ *The bus key is external.* The transcript of an AIR proof is seeded with
  the global challenge and nothing else, so the stage-2 challenges
  $(alpha, gamma)$ are the same for every AIR proof of an execution: they are
  the key $chi = DeriveKey(bold(p), bold(c))$ of @sec:tree, recomputed from
  the global challenge by a fixed squeeze.
+ *The first stage is not absorbed.* Neither $"root"_1$ nor the first-stage AIR
  values enter the AIR transcript. They are bound instead through the global
  challenge, which is derived from $h(tau, "com")$ with
  $"com" = ("root"_1, "first-stage AIR values")$ (@sec:instantiation).
  Likewise, the public statement is not absorbed by the AIR transcript but by
  the derivation of the global challenge.
+ *The bus contribution is not absorbed.* The airgroup value $s$ is part of the
  proof and enters the last-row constraint of stage 2, but it is absorbed
  neither before $v_c$ nor later.

#todo[The second and third features are deviations from the textbook
  Fiat–Shamir transformation, where everything the verifier reads is absorbed
  before the challenges that depend on it. The second is the subject of the
  binding lemma of @sec:compilation. For the third, the prover can choose $s$
  after seeing $v_c$, so the last-row combination of constraints can be made to
  vanish whatever the residual of the other constraints at that row; the proof
  then certifies $s$ only up to a shift that is a function of the committed
  data and of $v_c$. @sec:compilation must either show that such a shift cannot
  be steered to balance the buses at the root, or require $s$ to be absorbed
  before $v_c$, which is a one-line change of the prover and the verifier
  circuits.]

== The Relation Proved <sec:stark-relation>

We now match the protocol with the relation $cal(R)_"AIR"^((tau))$ of
@def:r-air, whose statement is $(bold(p), chi, s, "com")$ and whose witness
is $w = (bold(T), bold(a))$.

- *Witness.* $bold(T)$ consists of the fixed, cached and first-stage witness
  columns, and $bold(a)$ of the first-stage AIR values. The columns of the
  later stages ---the grouped fractions, the running sum, the intermediate
  columns--- and the second-stage AIR values are not part of the witness:
  they are functions of $(w, chi)$, which the constraints of the AIR force
  and an extractor recomputes.
- *Trace commitment.* $"com"$ is the pair of $"root"_1$ and the first-stage
  AIR values. The type of the proof is identified separately, by the root of
  its fixed tree, when the challenge accumulator hashes the commitment
  (@sec:instantiation).
- *Public statement.* The public statement enters the AIR through the custom
  tree of the Rom AIR, whose root is read from $bold(p)$, and through the
  global challenge. No other AIR reads $bold(p)$ in its constraints: the public
  outputs are bound by the global messages $cal(G)(bold(p))$
  (@def:balanced), which belong to no AIR.
- *Key and bus contribution.* $chi$ is the pair of stage-2 challenges and $s$
  the airgroup value of the proof. Row interactions are summed by the running
  sum; interactions that depend only on AIR values are modelled, in the
  notation of @def:interaction, as interactions whose multiplicity carries the
  first-row selector, so that each contributes once. With this convention
  $s = BusCont_chi (cal(I)_tau, w)$ whenever all constraints hold.

The protocol therefore proves $cal(R)_"AIR"^((tau))$ up to three caveats,
each handled in a later section: it rejects witnesses for which some
denominator vanishes, which only strengthens the relation (@sec:instantiation);
its first stage is bound through the global challenge rather than through its
own transcript; and the bus contribution is not absorbed into the transcript
(@sec:transcripts). Recursive circuits prove the relations of
@sec:relations-def with the same protocol and their own transcripts; they
take no external bus key.
