#import "../../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, corollary, definition, fwd, game,
  lemma, mult, negl, poly, proof, proposition, prover, remark, theorem, todo, verifier, vk,
)

// Protocols share the counter and the layout of the theorem-like environments.
#let protocol(body, title: none) = figure(
  body,
  kind: "theorem",
  supplement: [Protocol],
  numbering: "1",
  caption: title,
)

#let State = math.sans("State")
#let et = math.sans("et")
#let Block = math.sans("Block")
#let AccQueries = math.sans("AccQueries")

The IOP of @sec:stark becomes a non-interactive argument through the
transformation of Ben-Sasson, Chiesa and Spooner @TCC:BenChiSpo16. Oracles
are replaced by Merkle roots and their queries by openings, and challenges by
the outputs of a hash function applied to the transcript. This section
describes the compiled argument as ZisK implements it, bounds its
knowledge-soundness error, and identifies where ZisK departs from the
textbook transformation.

// - In @sec:stark-commitments and @sec:transcripts we define ZisK's Merkle
//   trees and Fiat–Shamir transcript, and the compiled protocol.
// - In @sec:bcs we recall the transformation and its straight-line
//   extractability in the random-oracle model, including the effect of
//   grinding and of the derivation of query indices.
// - In @sec:binding we treat the departure that matters: the first stage of an
//   AIR proof is not observed by its transcript, and is bound instead through
//   the global challenge. An AIR proof on its own is not knowledge-sound, but
//   the AIR proofs of an aggregation tree are, jointly.

== Merkle Commitments <sec:stark-commitments>

All hashing is done with Poseidon2 @AFRICACRYPT:GraKhoSch23 over $FF$. We
write $P_w : FF^w -> FF^w$ for the Poseidon2 permutation of width $w$, and
$[u]_(4)$ for the first four coordinates of a vector $u$. A _digest_ is an
element of $FF^4$. Merkle trees are parametrized by their _arity_
$a >= 2$, and a tree of arity $a$ uses the permutation of width
$4 a$, which compresses $a$ digests at once.

#definition(title: "Linear Hash")[
  Fix an arity $a$ and let $r_a := 4 (a - 1)$. For
  $u = (u_1, dots, u_ell) in FF^ell$ with $ell >= 1$, split $u$ into chunks
  $u^((1)), dots, u^((t))$ of $r_a$ consecutive elements, the last one
  possibly shorter, and let $overline(u)^((i)) in FF^(r_a)$ be $u^((i))$
  padded with zeros. The _linear hash_ of $u$ is $"LH"_a (u) := [s_t]_4$,
  where
  $
    s_1 := P_(4 a)(overline(u)^((1)) || 0^4), quad
    s_i := P_(4 a)(overline(u)^((i)) || [s_(i-1)]_4) "for" 1 < i <= t.
  $
  That is, a sponge of width $4 a$, rate $r_a$ and capacity $4$.
] <def:linear-hash>

#definition(title: "Merkle Commitment")[
  Fix an arity $a$ and a _verification level_ $L >= 0$. Let $M$ be a
  matrix with $R$ rows $M_0, dots, M_(R-1)$ over $FF$ (rows over $KK$ are
  flattened coordinatewise). The _leaves_ of its Merkle tree are
  $lambda_i := "LH"_a (M_i)$. Nodes are computed level by level: a level
  of $u$ digests is padded with zero digests to a multiple of $a$, and
  each group of $a$ consecutive digests $(d_1, dots, d_a)$ is
  compressed into the parent
  $
    "Comp"_a (d_1, dots, d_a) := [P_(4 a)(d_1 || dots || d_a)]_4,
  $
  until a single digest remains, the _root_ $"MT"_a (M)$. An _opening_ of
  row $i$ is the row $M_i$ together with, at each level up to level $L$ below
  the root, the $a - 1$ siblings of the current node. The proof carries,
  once per tree, the at most $a^L$ nodes of level $L$. The verifier
  recomputes the path of each opening up to level $L$, compares the result
  with the corresponding node of that level, and hashes the level into the
  root. With $L = 0$ this is the usual Merkle tree.
] <def:merkle>

The arity and the verification level are parameters of each AIR; ZisK uses
arity $a = 4$ and, for most AIRs, a level with $4$ or $16$ nodes. Nothing below
depends on the values of $a$ and $L$, and we drop the subscript $a$
when it is clear from the context. A group of polynomials
$f_1, dots, f_c$ is _committed on $D$_ by committing to the matrix whose row
$i$ is $(f_1 (x_i), dots, f_c (x_i))$, so that one opening reveals the values
of all of them at one point of $D$.

// An AIR proof involves the following trees, all on $D$ except the FRI trees.
// - The _fixed tree_ commits to the interpolants of the fixed columns. It is
//   computed at setup, and its root is the verification key $vk_cal(C)$ of the
//   AIR.
// - A _custom tree_ commits to the interpolants of a group of cached columns.
//   The only one in ZisK holds the program ROM of the Rom chip. Its root is not
//   taken from the proof: the verifier reads it from the coordinates of the
//   public statement that the AIR designates, so the cached columns are bound
//   to $bold(p)$.
// - The _stage trees_ commit to the columns computed in the first and second
//   stage (@prot:stark), with roots $"root"_1$ and $"root"_2$.
// - The _quotient tree_ commits to the chunks of the quotient polynomial, with
//   root $"root"_Q$.
// - The _FRI trees_ commit to the layers of the low-degree test, with leaves
//   grouped as described in @prot:stark.

== The Fiat–Shamir Transcript <sec:transcripts>

#definition(title: "Fiat–Shamir Transcript")[
  A _transcript_ holds a state $S in FF^(16)$, initially zero, a buffer of
  pending elements of length at most $12$, and an output buffer.
  - _Observing_ $u in FF$ appends $u$ to the pending buffer and empties the
    output buffer; when the pending buffer has $12$ elements, the transcript
    sets $S <- P_(16)("pending" || [S]_4)$, empties the pending buffer, and
    fills the output buffer with the $16$ coordinates of the new $S$.
  - _Sampling_ a field element returns the next element of the output
    buffer; if the output buffer is empty, the pending buffer is first padded
    with zeros and the state updated as above. Sampling $c in KK$ samples its
    three coordinates in order.
  - The _digest_ of a vector $u$ is $[S]_4$ for a fresh transcript that has
    observed $u$ and then updated its state if elements were pending.
  Elements of $KK$ are observed coordinate by coordinate.
] <def:transcript>

An AIR proof is not compiled on its own. The prover first commits to the
first stage of every segment. The _global challenge_ $g in KK$ of the
execution is the hash of the public statement and of the accumulated typed
commitments $bold(c)$ of all the segments, and the bus key
$chi = DeriveKey(bold(p), bold(c)) = (alpha, gamma)$ is its expansion
(@sec:instantiation). Every AIR transcript is seeded with $g$ and samples
$(alpha, gamma)$ first, so the bus key is common to all the AIR proofs of an
execution and is fixed only after all their traces are.
The compiled protocol replaces the oracles and challenges of @prot:stark as
follows.

#protocol(title: "ZisK Proving Protocol, Compiled")[
  The transcript is initialized and observes the global challenge $g$.

  + *Trace.* The prover commits on $D$ to the first-stage columns, including
    the intermediate columns of that stage, with root $"root"_1$, and
    computes $bold(a)^((1))$. Neither $"root"_1$ nor $bold(a)^((1))$ is
    observed. The cached columns are committed in a _custom tree_, whose root
    is not part of the proof: the verifier reads it from the coordinates of
    $bold(p)$ that the AIR designates. The transcript samples $alpha$, then
    $gamma$. The prover commits to the second-stage columns (root
    $"root"_2$), and the transcript observes $"root"_2$, then $bold(a)^((2))$,
    then $s$, and samples $v_c$.
  + *Quotient.* The prover commits to $q_0, dots, q_(d-2)$ (root $"root"_Q$);
    the transcript observes $"root"_Q$ and samples $xi$.
  + *Evaluations.* The transcript observes the digest of $bold(y)$ and samples
    $v_1$, then $v_2$.
  + *FRI.* For $i = 1, dots, R$, the prover commits to $F_(i-1)$ by a
    Merkle tree on $cal(L)_(i-1)$ whose leaves are the blocks of
    $x |-> x^(m_i)$: the leaf of index $r in [0, 2^(b_i))$ is the vector of
    the $m_i$ values of $F_(i-1)$ at the positions $r + j 2^(b_i)$,
    $j in [0, m_i)$, of $cal(L)_(i-1)$, which form a block. The transcript
    observes the root and samples $beta_i$. The prover sends the
    $2^(b_R)$ values of $F_R$, and the transcript observes their digest.
  + *Grinding.* The transcript samples $c in KK$. The prover finds
    $nu in FF$ such that $[P_4 (c_0, c_1, c_2, nu)]_1 < 2^(64 - g_"pow")$,
    where $[dot]_1$ is the first coordinate read as an integer in $[0, p)$;
    the verifier checks this inequality.
  + *Queries.* A fresh transcript observes $(c_0, c_1, c_2, nu)$ and samples
    $ceil(q n_e \/ 63)$ field elements; the concatenation of the $63$ low
    bits of each is cut into $q$ indices $r_1, dots, r_q in [0, 2^(n_e))$ of
    $n_e$ bits each, and the queries are $x_(r_1), dots, x_(r_q) in D$. For a
    query of index $r$, the prover opens row $r$ of the fixed tree, the custom
    trees, the stage trees and the quotient tree, and, in every FRI tree
    $i in [R]$, the leaf of index $r mod 2^(b_i)$, which holds
    $F_(i-1)$ on $Block(cal(L)_(i-1), m_i, x^((i)))$.
  The verifier checks every opening against its root, the root of the fixed
  tree being the verification key, and runs the decision phase of
  @prot:stark on the opened values. The value $F_0 (x)$ is at slot
  $floor(r \/ 2^(b_1))$ of the opened leaf of tree $1$, and
  $F_i (x^((i)))$, for $i < R$, at the corresponding slot of the leaf of tree
  $i + 1$, or, for $i = R$, at index $r mod 2^(b_R)$ of $F_R$.
] <prot:compiled>

*Recursive verifiers.* The recursive verifiers of @sec:relations-def are proved
with the same protocol, with three differences: the transcript is initialized
with their verification key, the digest of their public inputs and
$"root"_1$, instead of the global challenge; their second-stage challenges,
if any, are sampled from that transcript; and they have no external bus key
and no airgroup value read by a parent.

@tbl:transcripts summarizes what the transcript of each kind of proof
observes and samples, in order.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (0.7fr, 2fr, 2fr),
      align: (left, left, left),
      table.header([*Step*], [*AIR proof*], [*Recursive verifier*]),
      [seed], [the global challenge $g$ only], [the verification key, the digest of the public inputs, $"root"_1$],

      [stage 2],
      [sample $alpha, gamma$; observe $"root"_2$, $bold(a)^((2))$ and $s$],
      [sample the stage-2 challenges, if any; observe $"root"_2$ and $bold(a)^((2))$],

      [stage 3], [sample $v_c$; observe $"root"_Q$], [same],
      [stage 4], [sample $xi$; observe the digest of the evaluations], [same],
      [stage 5],
      [sample $v_1, v_2$; per FRI round, observe the root and sample $beta_i$; observe the digest of $F_R$],
      [same],

      [grinding], [sample $c$], [same],
      [queries], [fresh transcript over $(c, nu)$], [same],
    )
  },
  caption: [What the Fiat–Shamir transcript observes and samples, in order.],
  kind: table,
) <tbl:transcripts>

Two features of the AIR transcript matter for the analysis.

+ *The bus key is external.* The transcript of an AIR proof observes the global
  challenge $g$ and nothing else before sampling $alpha$ and $gamma$, so the
  bus key is the same for every AIR proof of an execution: it is
  $chi = DeriveKey(bold(p), bold(c))$ of @sec:tree, the global challenge being
  the output of the hash and $(alpha, gamma)$ its fixed expansion.
+ *The first stage is not observed.* Neither $"root"_1$ nor $bold(a)^((1))$ is
  observed by the AIR transcript. They are bound instead through the global
  challenge, which is derived from $h(tau, "com")$ with
  $"com" = ("root"_1, bold(a)^((1)))$ (@sec:instantiation). Likewise, the
  public statement is not observed by the AIR transcript but by the
  derivation of the global challenge.

Both are deviations from the textbook Fiat–Shamir transformation, in which
everything the verifier reads is observed before the challenges that depend
on it. The first is harmless for a single proof, since the key is part of the
statement of $cal(R)_"AIR"^((tau))$; the second is not, and the binding lemma
of @sec:binding shows that the global challenge restores it. Everything
else the verifier of an AIR proof reads, the bus contribution $s$ included, is
observed before the challenges that depend on it.

== The BCS Transformation <sec:bcs>

Let $(prover, verifier)$ be an IOP whose oracles are functions on evaluation domains. Its
_BCS compilation_ is the non-interactive argument in which the prover:
+ Replaces every oracle by the root of a Merkle tree on its evaluation table
  (@def:merkle), grouping the oracles of one round in one tree.
+ Obtains every challenge by sampling the Fiat–Shamir transcript
  (@def:transcript), after having observed the instance and all the
  preceding prover messages, roots and plain values.
+ Answers every query of the verifier with a Merkle opening.

The verifier recomputes the challenges from the transcript, checks the
openings, and runs the decision of $verifier$ on the opened values. As in
@def:rom, we model the transcript as a random oracle, which, given the
sequence of observed elements, returns the sampled elements, and the
compression functions of the Merkle trees as independent random oracles with
outputs in $FF^4$. A proof is then determined by the adversary's oracle
queries, and a _straight-line_ extractor may read the list of these queries
and their answers, but may not rewind the adversary.

#theorem(title: [BCS Compilation @TCC:BenChiSpo16 @STOC:CCHLRR19 @AC:BGKTTZ23])[
  Let $(prover, verifier)$ be a public-coin IOP for $cal(R)$ with round-by-round
  knowledge soundness errors $(epsilon_1, dots, epsilon_k)$ and extraction
  time $et$. There is a straight-line extractor for its BCS compilation,
  running in time polynomial in the size of the query list and $et$, such
  that for every adversary making at most $Q$ queries to the random oracles,
  the probability that it outputs an instance $bb(x)$ and an accepting proof
  while the extractor outputs no $bb(w)$ with $(bb(x); bb(w)) in cal(R)$ is at most
  $
    Q dot max_(i in [k]) epsilon_i + epsilon_"MT" (Q),
  $
  where $epsilon_"MT" (Q) = O(Q^2 \/ p^4)$ bounds the probability that the
  query list contains a collision or an inversion of the hash.
] <thm:bcs>

// #proof(sketch: true)[
//   The extractor reconstructs, from the query list, every Merkle tree whose
//   root the adversary queried before the challenge that follows it. Except
//   with probability $epsilon_"MT" (Q)$, every root then has at most one
//   preimage in the list, and every opening that the verifier accepts is
//   consistent with the reconstructed tree; positions that the adversary never
//   queried can be filled arbitrarily, since a later opening of them would
//   require inverting the hash. Each query to the transcript oracle extends a
//   partial transcript of the IOP by one challenge. The state function of
//   @def:state assigns a state to every such transcript. An accepting proof
//   determines a full transcript in state $1$, starting from state $0$, so some
//   query flipped the state. The extractor runs $E$ on the transcript preceding
//   the first query that flipped it. A fixed query flips the state with
//   probability greater than $epsilon_i$ only if $E$ succeeds there, and a
//   union bound over the $Q$ queries concludes.
// ]

The theorem measures soundness by the maximum error over the rounds, per
query, rather than by their sum: the adversary may retry any round as often
as its budget allows. In @thm:iop-rbr the maximum is
$epsilon^"qry" = (1 - min{theta, delta})^q$, and two features of @prot:compiled refine it.

#lemma(title: "Grinding and Query Derivation")[
  In the BCS compilation of @prot:stark by @prot:compiled, the query round may be
  taken with error
  $
    epsilon^"qry"_"BCS" := frac(2^(64 - g_"pow"), p) dot kappa dot (1 - min{theta, delta})^q,
    quad kappa := (2^(64) \/ p)^(ceil(q dot n_e \/ 63)),
  $
  in place of $epsilon^"qry"$ in @thm:bcs.
] <lem:grinding>

#proof[
  In @prot:compiled the query indices are derived from a fresh transcript over
  $(c, nu)$, where $c$ is the grinding challenge and $nu$ a nonce with
  $[P_4 (c_0, c_1, c_2, nu)]_1 < 2^(64 - g_"pow")$. A query of the adversary
  that produces accepting query indices must evaluate both oracles at a pair
  $(c, nu)$; we model the grinding permutation and the query transcript as
  independent random oracles. For a fixed pair, the grinding check passes with
  probability $2^(64 - g_"pow") \/ p$. The query indices are obtained by
  concatenating the low $63$ bits of $ceil(q dot n_e \/ 63)$ uniform field
  elements. A uniform element of $[0, p)$ has each residue modulo $2^(63)$
  with probability at most $2 \/ p = 2^(-63) dot 2^(64) \/ p$. The joint
  distribution of the bits therefore assigns to every string at most $kappa$
  times its uniform probability, and so does the distribution of the indices
  to every tuple. Hence all $q$ indices land in the set $AccQueries$ of
  @clm:queries with probability at most $kappa dot (1 - min{theta, delta})^q$. The two events
  depend on independent oracles, so a single query achieves both with
  probability at most the product of the two bounds.
]

Since $2^(64) \/ p = 1 + 2^(-32) + O(2^(-64))$, $kappa$ is $1 + O(2^(-25))$
for every AIR of ZisK, and the grinding contributes a factor of about
$2^(-g_"pow")$. Grinding does not change the other rounds; their errors are
negligible in comparison (@cor:iop-jbr).

*The textbook transformation and ZisK.* The theorem applies to the recursive
verifiers as they are: their transcript observes every message before the
challenge that depends on it (@tbl:transcripts). For AIR proofs,
@prot:compiled departs from the transformation in the two ways listed in
@sec:transcripts. The first is harmless; the second is not, as we now show.

== Binding Through the Global Challenge <sec:binding>

#remark(numbered: true, title: "An AIR Proof Alone Is Not Sound")[
  Consider the knowledge-soundness game of @def:ks for one AIR argument, in
  which the adversary chooses the statement $(bold(p), chi, s, "com")$ and
  the proof. Since $"root"_1$ is not observed, the challenges $v_c$ and $xi$
  are functions of the global challenge and of the later commitments only.
  The adversary can choose the second-stage columns and the quotient,
  observe them, obtain $xi$, and only then choose first-stage columns in
  $FF^(< N)[X]$ that take, at the points $xi omega^o$, values
  satisfying the constraint check. One field equation suffices, and a column
  read at fewer than $N$ points can be interpolated through any values. Every
  committed function is then a low-degree polynomial, so the low-degree test
  passes, while the trace need not satisfy any constraint. Knowledge soundness of
  $Pi_"AIR"^((tau))$ in the sense of @def:ks therefore fails, and what holds
  is the joint statement of @lem:binding.
] <rem:standalone>

In ZisK the global challenge is not chosen by the prover: it is
$DeriveKey(bold(p), bold(c))$, where $bold(c) = sum_i h(tau_i, "com"_i)$
accumulates the typed commitments of all the leaves, and
$"com"_i = ("root"_(1, i), bold(a)^((1))_i)$ contains the first-stage root.
Preimage awareness of the accumulator (@def:cr) fixes the commitments when
the global challenge is first computed, and Merkle extractability fixes the
oracles behind them. We capture this in a joint game.

#definition(title: "Joint AIR Extraction Game")[
  For a PPT adversary $cal(A)$ and an extractor $cal(E)_"J"$, the experiment
  $Exp("joint", (cal(E)_"J", cal(A)))(lambda)$ is:
  #game(
    [$cal(A)(1^lambda)$ outputs a public statement $bold(p)$ and, for
      $i in [n]$ with $1 <= n < 2^B$, a type $tau_i$, a commitment
      $"com"_i$, a bus contribution $s_i$ and an AIR proof $pi_i$.],
    [Let $bold(c) := sum_i h(tau_i, "com"_i)$ and
      $chi := DeriveKey(bold(p), bold(c))$, with global challenge $g$. If
      some $pi_i$ is rejected by the verifier of @prot:compiled for type
      $tau_i$, transcript seed $g$, statement $(bold(p), chi, s_i)$ and
      first-stage commitment $"com"_i$, return $0$.],
    [Run $(w_i)_(i in [n]) <- cal(E)_"J" (cal(T), bold(p), (tau_i, "com"_i, s_i, pi_i)_i)$,
      where $cal(T)$ is the list of $cal(A)$'s oracle queries.],
    [Return $1$ if and only if
      $((bold(p), chi, s_i, "com"_i); w_i) in.not cal(R)_"AIR"^((tau_i))$
      for some $i$.],
  )
  We write $Adv("joint", cal(E)_"J")(cal(A))$ for the probability that the
  experiment returns $1$.
] <def:game-joint>

The game is the situation of the leaves of an accepting aggregation tree:
the Final Verifier checks that $chi$ was derived from $bold(p)$ and from the
accumulator of the leaves' typed commitments (@def:r-final), and every leaf
verifier checks an AIR proof under that key, directly or through a
compressor (@rem:air-compressors).

#lemma(title: "Binding Through the Global Challenge")[
  For every chip type $tau$ let $epsilon^*_tau$ be the largest of the errors of
  @thm:iop-rbr, with $epsilon^"qry"$ replaced by $epsilon^"qry"_"BCS"$
  (@lem:grinding), and let $epsilon^* := max_tau epsilon^*_tau$ and
  $Lambda_"pole" := (2^B - 1) dot max_tau (N_tau + 1) abs(cal(I)_tau)$.
  There is a straight-line extractor $cal(E)_"J"$ such that for every
  adversary $cal(A)$ making at most $Q$ oracle queries there is an adversary
  $cal(D)$ against preimage awareness, with
  $Time(cal(D)) = Time(cal(A)) + poly(lambda)$, and
  $
    Adv("joint", cal(E)_"J")(cal(A)) <= Q dot epsilon^* + Adv("pa", cal(H))(cal(D)) + epsilon_"MT" (Q) + frac(Q dot Lambda_"pole", abs(KK)).
  $
] <lem:binding>

#proof[
  The extractor $cal(E)_"J"$ locates in $cal(T)$ the first query to
  $DeriveKey$ at $(bold(p), bold(c))$, and runs the extractor $cal(E)_(cal(H))$
  of @def:cr on the prefix of $cal(T)$ before it, obtaining a multiset of
  typed commitments. It then reconstructs, as in @thm:bcs, the Merkle trees
  of every $"root"_(1, i)$, $"root"_(2, i)$, quotient and FRI root of every
  proof, and for each $i$ runs the extractor of @thm:iop-rbr for type
  $tau_i$ on the transcript of $pi_i$ preceding the query that flipped its
  state. It outputs the restriction (@lem:r-stark) of the expanded witnesses
  it obtains. We bound the probability that the experiment returns $1$ by
  four events.

  _Accumulator._ If the multiset extracted at the first query to $DeriveKey$
  differs from ${(tau_i, "com"_i)}_i$, then $cal(D)$, which runs $cal(A)$,
  announces $bold(c)$ at that query and outputs the multiset, breaks preimage
  awareness. Otherwise every $"com"_i$, and with it $"root"_(1, i)$ and
  $bold(a)^((1))_i$, was fixed in $cal(T)$ before $g$, and hence before every
  challenge of every AIR proof.

  _Merkle trees._ Except with probability $epsilon_"MT" (Q)$, every root in
  the proofs has a unique preimage in $cal(T)$, computed before the root was
  first used as an oracle input, and every accepted opening agrees with it.
  Together with the previous event, the first-stage oracles of every proof are
  determined before $g$. The cached columns are determined by the root that
  the verifier reads from $bold(p)$, which is an input of $DeriveKey$, so
  they too are fixed before $g$.

  _Rounds._ Under the two previous events, the transcript of $pi_i$ is a BCS
  transcript of @prot:stark with instance $(bold(p), chi, s_i)$. Its first
  message, the first- and second-stage oracles with $bold(a)^((1))_i$ and
  $bold(a)^((2))_i$, is fixed before $v_c$: the first stage before $g$, the
  second stage, $bold(a)^((2))_i$ and $s_i$ through the transcript, which
  observes them after $g$ and before sampling $v_c$. The instance is fixed
  before $v_c$ as well, since $bold(p)$ and $chi$ are determined by $g$ and
  $s_i$ is observed. Every later message is observed before the challenge that
  follows it. Every query of $cal(A)$ to the transcript oracle of any proof
  extends a partial transcript of one of the IOPs by one challenge, and the
  argument of @thm:bcs, with @lem:grinding for the query round, shows that,
  except with probability $Q dot epsilon^*$, the extractor of @thm:iop-rbr
  outputs an expanded witness of $cal(R)_"STARK"^((tau_i))$ for every $i$.

  _Poles._ The expanded witness contains the witness $w_i$ of @lem:r-stark,
  which, under the first two events, was fixed in $cal(T)$ before $g$. Every
  query to $DeriveKey$ returns a fresh key, which is a pole of a fixed
  collection of at most $2^B - 1$ witnesses with probability at most
  $Lambda_"pole" \/ abs(KK)$ (@rem:poles); a union bound over the $Q$
  queries bounds the probability that $chi$ is a pole of some $w_i$.

  Outside the four events, @lem:r-stark gives
  $s_i = BusCont_chi (cal(I)_(tau_i), w_i)$ and every constraint of
  $cal(C)_(tau_i)$; the cached columns open the commitment in $bold(p)$, so
  $Local_(tau_i) (bold(p), w_i)$ holds; and
  $Commit(w_i) = "com"_i$ because the extracted first-stage oracles are the
  preimage of $"root"_(1, i)$. Hence $((bold(p), chi, s_i, "com"_i); w_i) in cal(R)_"AIR"^((tau_i))$
  for every $i$.
]

The extractor $cal(E)_"J"$ uses the query list of the whole execution and the
preimage-awareness extractor; its output is a collection of witnesses, not a
witness per proof. This is the form in which the AIR arguments are used in
#fwd(<sec:lemmas>)[Part II]: the witnesses of all the leaves are extracted at
once.
