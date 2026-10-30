#import "../../../lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, fwd, game, lemma, mult,
  negl, poly, proof, proposition, remark, theorem, todo, verifier, vk,
)

This section states the knowledge soundness of every argument of ZisK. The
analysis of @sec:stark and the compilation of @sec:compilation apply to the
AIR of every chip and of every recursive verifier. Two further ingredients
connect them to the relations of @sec:relations-def: the assumption that
the AIR of every recursive verifier enforces its relation, which turns a
satisfying witness of that AIR into a witness of the relation, and the
compressor lemma, which shows that a compressor adds one term to the error.

== Statement <sec:theorem-i-statement>

For an argument $Pi$ of ZisK we write $epsilon^*_Pi$ for the largest of the
round-by-round errors of @thm:iop-rbr for its AIR, with $epsilon^"qry"$
replaced by $epsilon^"qry"_"BCS"$ (@lem:grinding), and $epsilon^*$ for the
largest of the $epsilon^*_(Pi_"AIR"^((tau)))$ over $tau in [M]$. The AIR
arguments and the recursive arguments are treated separately: an AIR proof is
not knowledge-sound on its own (@rem:standalone), and its guarantee is a
joint one.

The recursive arguments prove that the AIR of a recursive verifier is
satisfied, while the relations of @sec:relations-def state what that
verifier checks. Relating the two is a property of how the verifier is
arithmetized, not of the proof system, and this paper assumes it.

#definition(title: "Enforcing a Relation")[
  The AIR $cal(C)_X$ of a recursive verifier _enforces_ the relation
  $cal(R)_X$ if, for every $bb(x)$, every witness that satisfies the
  constraints of $cal(C)_X$ with publics $bb(x)$ contains a $bb(w)$ with
  $(bb(x); bb(w)) in cal(R)_X$.
] <def:enforces>

#theorem(title: "Knowledge Soundness of the Arguments")[
  Let $Q$ bound the number of oracle queries of the adversary.
  + (_AIR arguments._) There is a straight-line extractor $cal(E)_"J"$ that
    extracts the witnesses of all the AIR proofs of an execution at once: for
    every adversary $cal(A)$ there is an adversary $cal(D)$ against preimage
    awareness, with $Time(cal(D)) = Time(cal(A)) + poly(lambda)$, such that
    $
      Adv("joint", cal(E)_"J")(cal(A)) <= Q dot epsilon^* + Adv("pa", cal(H))(cal(D)) + epsilon_"MT" (Q) + frac(Q dot Lambda_"pole", abs(KK)).
    $
  + (_Recursive arguments._) Let $X$ be $"LEAF"^((tau))$ for some
    $tau in [M]$, $"AGG"$, $"FINAL"$, or a compressor, and assume that the
    AIR $cal(C)_X$ of its verifier enforces $cal(R)_X$ (@def:enforces). Then $Pi_X$
    is knowledge-sound for $cal(R)_X$ with a straight-line extractor, and for
    every adversary $cal(A)$
    $
      Adv("ks", Pi_X)(cal(A)) <= Q dot epsilon^*_(Pi_X) + epsilon_"MT" (Q).
    $
] <thm:arguments>

#proof[
  The first statement is @lem:binding. For the second, $Pi_X$ is the BCS
  compilation of @prot:stark for $cal(C)_X$ by @prot:compiled, whose
  transcript observes every message before the challenge that depends on it
  (@tbl:transcripts). @thm:bcs, with the round-by-round errors of
  @thm:iop-rbr and the query round refined by @lem:grinding, gives a
  straight-line extractor that, except with probability
  $Q dot epsilon^*_(Pi_X) + epsilon_"MT" (Q)$, outputs an expanded witness of
  the IOP relation for $cal(C)_X$. Its restriction to the columns of
  $cal(C)_X$ satisfies the constraints of $cal(C)_X$ with publics $bb(x)$
  (@lem:r-stark, for an AIR without interactions), and by hypothesis
  contains a $bb(w)$ with $(bb(x); bb(w)) in cal(R)_X$, which the extractor
  outputs.
]

// #remark(numbered: true, title: "What Enforcing the Relations Requires")[
//   For the AIR of a recursive verifier to enforce its relation, it must
//   satisfy the following.
//   + *The transcript.* The AIR recomputes every challenge exactly as the
//     native verifier does, observing the same elements in the same order
//     (@tbl:transcripts). In particular, the recursive verifier that verifies an
//     AIR proof, the leaf verifier or the compressor, must observe the bus
//     contribution $s$ after the second-stage AIR values and before $v_c$.
//   + *Field arithmetic.* Every division in the verifier is computed with a
//     constrained inverse, and every bit decomposition is canonical: the query
//     indices are decomposed with a strict decomposition, which rules out the
//     alias $u + p$ of a sampled element $u < 2^(64) - p$. The generator of the
//     recursive verifiers uses one for the query indices.
//   + *Selection of the child's key.* The verification key of a child is
//     selected by its type through the dispatch of @def:dispatch, and the
//     selection is constrained, not hinted.
//   + *Null children.* Verification of a child proof may be switched off only
//     for the null type, and only where the relation admits a null child: in an
//     aggregation node, never at the root.
//   + *The other clauses.* Besides running the embedded verifiers, the AIR
//     checks every other clause of the relation: the counters and their ranges,
//     the typing predicate, the accumulation of $bold(c)$ and $s$, and at the
//     root the key derivation and the root check.
// ] <rem:enforces>

A compressor of an argument $Pi_X$ (@sec:tree) proves the relation
$cal(R)_"COMP"^((X))$ of @def:r-comp, and its proofs stand in for those of
$Pi_X$. Composing the two arguments preserves knowledge soundness.

#lemma(title: "Compressors Preserve the Relation")[
  Let $Pi_X$ be knowledge-sound for $cal(R)_X$ with extractor $cal(E)_X$, and
  $Pi_"COMP"$ knowledge-sound for $cal(R)_"COMP"^((X))$ with extractor
  $cal(E)_"COMP"$. The argument whose proofs for $bb(x)$ are the proofs of
  $Pi_"COMP"$ for $bb(x)$ is knowledge-sound for $cal(R)_X$ with the extractor
  $cal(E)_X (bb(x), cal(E)_"COMP" (bb(x), dot))$, and for every adversary $cal(A)$
  there are reductions $cal(D)_1, cal(D)_2$ running in time
  $Time(cal(A)) + poly(lambda)$ with
  $
    Adv("ks", Pi_"COMP" compose Pi_X)(cal(A)) <= Adv("ks", Pi_"COMP")(cal(D)_1) + Adv("ks", Pi_X)(cal(D)_2).
  $
] <lem:compressor>

#proof[
  If the compressor proof is accepted, then except with probability
  $Adv("ks", Pi_"COMP")(cal(D)_1)$, where $cal(D)_1 := cal(A)$, the
  extracted $pi$ satisfies $verifier(vk_X, bb(x), pi) = 1$. The adversary $cal(D)_2$
  runs $cal(A)$ and $cal(E)_"COMP"$ and outputs $(bb(x), pi)$; it wins the
  knowledge-soundness game of $Pi_X$ exactly when $pi$ is accepted and
  $cal(E)_X$ fails. Its running time is that of $cal(A)$ plus that of
  $cal(E)_"COMP"$, which is $Time(cal(A)) + poly(lambda)$ by @def:ks.
]

The lemma composes straight-line extractors and is subject to the first
idealization of @rem:idealized. A compressor adds one term to the error, and
its own parameters, rate and number of queries, enter only that term. ZisK
compresses only AIR proofs, the case of the following remark.

#remark(numbered: true, title: "Compressors of AIR Proofs")[
  @lem:compressor does not apply verbatim to a compressor of an AIR proof,
  since $Pi_"AIR"^((tau))$ is not knowledge-sound on its own. Its proof,
  however, uses the knowledge soundness of $Pi_X$ only on the proof $pi$ that
  the compressor's extractor outputs, which is accepting and occurs in the
  adversary's query list. Extracting the compressed AIR proofs first and then
  applying @lem:binding to the whole collection gives the first statement of
  @thm:arguments with one more term $Adv("ks", Pi_"COMP")$ for each
  compressor argument.
] <rem:air-compressors>

== Concrete Parameters <sec:parameters>

The parameters of every argument of ZisK, its rate $rho$, number of queries
$q$, grinding bits $g_"pow"$, folding factors and constraint degree, are
those of the proving backend @ZISK:WHITEPAPER. In the Johnson regime
(@cor:iop-jbr), every error of @thm:iop-rbr except the query error is a
polynomial in $abs(D)$ divided by $abs(KK) approx 2^(192)$, hence negligible
for the trace heights of ZisK, and the query error of the compiled protocol
is, by @lem:grinding,
$
  epsilon^"qry"_"BCS" approx 2^(-g_"pow") dot (sqrt(rho^+) + eta)^q .
$
@tbl:security lists, for every family of arguments, the limit
$g_"pow" + q dot log_2 (1 \/ sqrt(rho))$ of $-log_2 epsilon^"qry"_"BCS"$
as $eta -> 0$ and $rho^+ -> rho$, and the level reported by `soundcalc`
@SOUNDCALC, which fixes $eta$ and accounts for every round.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (2fr, 0.6fr, 0.7fr, 0.6fr, 1fr, 0.9fr),
      align: (left, center, center, center, center, center),
      table.header(
        [*Arguments*], [*$rho$*], [*$q$*], [*$g_"pow"$*], [*$g_"pow" + q log_2 rho^(-1\/2)$*], [*`soundcalc`*]
      ),
      [AIRs (except below)], [$1\/2$], [$229$--$232$], [$16$], [$130.5$--$132$], [$128$],
      [Rom], [$1\/2$], [$221$], [$20$], [$130.5$], [$128$],
      [Keccakf], [$1\/2$], [$217$], [$23$], [$131.5$], [$128$],
      [Poseidon2], [$1\/4$], [$114$], [$16$], [$130$], [$128$],
      [Compressors], [$1\/4$], [$110$], [$20$], [$130$], [$128$],
      [Leaf and aggregation verifiers], [$1\/8$], [$73$], [$20$], [$129.5$], [$128$],
      [Final Verifier], [$1\/32$], [$43$], [$22$], [$129.5$], [$128$],
    )
  },
  caption: [Security level, in bits, of the query round of every argument of
    ZisK in the Johnson regime: the idealized bound of @lem:grinding and the level reported by
    `soundcalc`.],
  kind: table,
) <tbl:security>

These are errors per query. By @thm:bcs, an adversary making $Q$ queries
gains a factor $Q$, so a level of $128$ bits bounds its success probability
by $Q dot 2^(-128)$.

// Under the unique-decoding regime, which does not rely on
// @lem:mca-jbr beyond half the minimum distance, `soundcalc` reports between
// $63$ bits, for the Final Verifier, and $113$ bits, for the AIRs at rate
// $1\/2$ @ZISK:WHITEPAPER.

// == The SNARK Wrap <sec:snark-wrap>

// The final proof can be wrapped into a pairing-based SNARK over BN254, which
// proves that $verifier_"FINAL"$ accepts it, for cheap verification on chain.
// The wrapper plays the role of a compressor for $Pi_"FINAL"$: if it is
// knowledge-sound for $cal(R)_"COMP"^(("FINAL"))$ with a straight-line
// extractor, @lem:compressor shows that a wrapped proof is knowledge-sound for
// $cal(R)_"FINAL"$, with the knowledge-soundness error of the wrapper as one
// more term. The knowledge soundness of pairing-based SNARKs is usually proved
// in the algebraic group model, with a trusted setup, rather than in the
// random-oracle model with a straight-line extractor; we take it as an
// assumption, and the analysis of this paper stops at $Pi_"FINAL"$.
