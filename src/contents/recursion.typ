#import "../lib.typ": definition
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

ZisK uses proof recursion to combine the independent per-segment proofs produced by trace splitting into a single, globally consistent argument. This section introduces proof recursion in general, identifies the two specific problems it resolves in ZisK, and details the aggregation structure.

== Proof Recursion

A proving system is called _recursive_ when it can verify the validity of another proof as part of its own computation. The key observation is that a verifier is itself a computation ---it reads a proof and performs arithmetic checks--- so the verifier itself can be expressed as polynomial constraints and be proved. A _recursive verifier_ is therefore an arithmetic circuit that takes a proof $pi$ and its public inputs as witness and checks that $pi$ is valid. Wrapping this circuit in a proof yields a _recursive proof_: a succinct argument that attests to the correctness of an underlying proof without re-exposing its content.

The power of this construction comes from its composability. Since a recursive proof is itself a valid proof, it can in turn be fed into another recursive verifier, producing a proof of a proof of a proof. Iterating this idea allows a sequence of computations ---or a collection of independent computations--- to be folded into a single, constant-size argument regardless of the number of steps or the size of the individual proofs. The result is a _proof composition_ that scales arbitrarily: adding more computations does not make the final proof larger or more expensive to verify.

Recursive composition serves two purposes. The first is _proof aggregation_: combining many independent proofs $pi_1, ..., pi_k$ into a single argument that attests to the validity of all of them simultaneously. The second is _proof compression_: converting a proof generated with one proving system (e.g., a proof with large size but fast to generate) into a proof in another system better suited for a particular context (e.g., a compact proof with fast verification).

== The Role of Recursion in ZisK

Recall from @sec:continuations the two open problems left by trace splitting.

The first is _cross-chip bus balancing_. Each segment proof contributes a partial sum $s_i in bb(K)$ to the global bus interaction. Global correctness requires $sum_i s_i = 0$, but no individual proof can verify this: it requires aggregating the partial sums across all segment instances and all chips.

The second, and more subtle, is _challenge derivation_. The LogUp argument (@sec:arithmetization) uses random field elements $alpha$ and $gamma$, derived via the Fiat-Shamir heuristic, to compress bus interactions into a single accumulated value per AIR. For the global balancing equation $sum_i s_i = 0$ to be meaningful, all partial sums must be computed under the _same_ challenges. In a monolithic proof this is automatic: there is one prover transcript and one application of Fiat-Shamir. In the trace-splitting design, each segment is proved independently and would naturally derive its own challenges from its own commitments ---producing values that differ across instances and making the partial sums incommensurable.

Both problems are resolved by the recursive aggregation layer.

== Challenge Derivation

The challenge derivation problem arises because Fiat-Shamir ties each challenge to the transcript of a single prover. When segment provers operate independently, their transcripts diverge and so do their challenges.

The solution is to separate challenge derivation from proof generation: all segment provers first commit to their traces, and the challenge is then derived from the full set of commitments and broadcast to all provers as a _public input_. Each segment proof proves the statement "given the challenge $alpha$, my witness satisfies my constraints and my partial sum is $s_i$" ---the challenge is _assumed_, not derived internally.

A natural first attempt is sequential hashing: Given commitments $"com"_1, ..., "com"_k$, compute: $ alpha = H(dots.c H(H("com"_1, "com"_2), "com"_3) dots.c, "com"_k). $
This fails for two reasons. It is inherently sequential, which negates the parallelism of trace splitting. And it is order-dependent: changing the processing order changes the challenge, so partial batches cannot be computed independently and merged.

ZisK instead uses _LtHash_ @ZISK:LTHASH, a lattice-based multiset hash function whose defining property is homomorphism over multiset union:
$
  "LtHash"(S union T) = "LtHash"(S) + "LtHash"(T),
$
where addition is component-wise over an appropriate vector space. Because the group operation is commutative, the accumulated value does not depend on the order in which commitments are processed: any subset can be accumulated independently and the results summed, enabling full parallelism and hierarchical composition.

The construction is as follows. Each prover $cal(P)_i$ first hashes its commitment $c_i = H("com"_i)$, which is then _embedded_ into a long pseudorandom vector $v_i := v_i (c_i) in ZZ_p^n$ of sufficient length by iterative hashing. The global accumulator is simply the component-wise sum of all these vectors:
$
  "acc" = sum_i v_i in ZZ_p^n,
$
and the common challenge $alpha$ is read off from $"acc"$. Because addition in $ZZ_p^n$ is commutative, the result does not depend on the order of summation: any subset of provers can compute their partial sum independently and all partial sums can be merged later by addition. Security ---the guarantee that no two distinct multisets of commitments produce the same $"acc"$--- reduces to the Short Integer Solution (SIS) @STOC:Ajtai96 lattice problem, which is believed to remain hard even against quantum adversaries.

Correctness of the assumed challenge must be verified ---otherwise a malicious prover could substitute any $alpha$ to make the partial sums balance artificially. Since LtHash is homomorphic, this verification is embedded directly into the aggregation tree: each node carries a _partial accumulator_ over the commitments in its subtree alongside its partial LogUp sum, and a parent node combines the two by addition. At the root, the fully accumulated value is checked against the claimed $alpha$, confirming that it was correctly derived from the entire set of commitments.

== Recursive Structure

Individual AIR proofs are combined in a fixed arity aggregation tree illustrated in @fig:aggregation-tree. Each aggregation node has a fixed amount of children, but the tree is not required to be balanced: it is built opportunistically as proofs complete, so a branch that finishes early can be aggregated immediately while others are still running. The shape of the tree therefore reflects the relative timing of the individual proofs, not a fixed structure decided in advance.

At every level of the tree, each node _verifies_ the proofs produced by its children. In addition to proof verification, each node accumulates two quantities upward: the LogUp partial sums $s_i$ and the LtHash challenge contributions $bold(c)_i$. These accumulations are the mechanism by which the two global checks ---bus balancing and challenge correctness--- are reduced to arithmetic on public outputs at the root.

The challenge $alpha$ is an input to the entire aggregation structure, not something derived inside it. Before proving starts, $alpha$ is derived from all commitments via LtHash and broadcast to every leaf prover. Each leaf proof takes $alpha$ as a _public input_ and uses it to compute its partial LogUp sum $s_i$. The aggregation tree then accumulates both $s$ and the LtHash contributions $bold(c)$ upward, and the root receives $alpha$ as a public input to verify that it matches what the tree actually accumulated.

The tree has three node types.

_Leaf nodes_ are the raw proofs produced by individual AIR segment instances. Each leaf takes $alpha$ as a public input and exposes as public outputs:
- Its _own public outputs_ $bold(o)_i in FF^k$: values the AIR explicitly exposes, such as program outputs that must be visible to the final verifier.
- Its _partial LogUp sum_ $s_i in KK$: the final value of the LogUp accumulator, representing AIR $i$'s net signed contribution to all bus interactions.
- Its _challenge contribution_ $bold(c)_i in ZZ_p^n$: the LtHash vector embedding of its commitment, representing AIR $i$'s additive share of the global challenge accumulator.

_Compressor nodes_ sit directly above the leaves. Each compressor takes a single leaf proof as input and converts it into a format that can be verified efficiently inside the recursive aggregation circuit. The compressor outputs a compressed proof with the same public outputs as its leaf.

_Aggregation nodes_ each receive the compressed proofs of their two children, verify both, and accumulate the LogUp partial sums and the challenge contributions:
$
  s_"parent" = s_L + s_R, quad bold(c)_"parent" = bold(c)_L + bold(c)_R,
$
outputting $(s_"parent", bold(c)_"parent")$ for the next level. This propagates up the tree until a single pair reaches the root.

#figure(
  {
    set text(size: 8pt)
    let sub(body) = text(size: 7pt, body)
    let leaf-fill = rgb("dde8fb")
    let leaf-stroke = rgb("4a6fa5")
    let compressor-fill = rgb("fbe4c2")
    let compressor-stroke = rgb("a86e2c")
    let agg-fill = rgb("fbd5d5")
    let agg-stroke = rgb("a84444")
    let root-fill = rgb("c8e6e0")
    let root-stroke = rgb("2e7d6e")
    let arr-stroke = 0.6pt + luma(80)
    let dash-stroke = (dash: "dashed", paint: luma(130), thickness: 0.5pt)

    let nw = 2.3cm
    let nh = 0.82cm
    let ns(f, s) = (fill: f, stroke: s, width: nw, height: nh + 0.3pt, corner-radius: 3pt)

    diagram(
      spacing: (1.1cm, 1.35cm),

      // Public input alpha, top-right
      node(
        (2.2, 0),
        align(center)[*in:* $alpha$],
        fill: luma(248),
        stroke: 0.5pt + luma(160),
        inset: 5pt,
        corner-radius: 2pt,
      ),

      // Root
      node(
        (0, 0),
        align(
          center,
        )[*Root* #linebreak() #sub[$s_"root" = s_L + s_R$] #linebreak() #sub[$bold(c)_"root" = bold(c)_L + bold(c)_R$] #linebreak() #sub[Checks: $s_"root"=0$, $bold(c)_"root" arrow.r alpha$]],
        fill: root-fill,
        stroke: 0.7pt + root-stroke,
        width: nw + 1cm,
        height: nh + 0.6cm,
        corner-radius: 3pt,
      ),

      // alpha → root
      edge((2.2, 0), (0, 0), "->", stroke: dash-stroke),

      // Level 1: aggregation (left, deeper) + compressor (right, shallower)
      node(
        (-1, 1),
        align(
          center,
        )[*Aggregation* #linebreak() #sub[$s = s_L + s_R$] #linebreak() #sub[$bold(c) = bold(c)_L + bold(c)_R$]],
        fill: agg-fill,
        stroke: agg-stroke,
        width: nw,
        height: nh + 0.3cm,
        corner-radius: 3pt,
      ),
      node((1, 1), align(center)[*Compressor*], ..ns(compressor-fill, 0.5pt + compressor-stroke)),

      // Level 2: two compressors under left agg; leaf under right compressor
      node((-1.7, 2), align(center)[*Compressor*], ..ns(compressor-fill, 0.5pt + compressor-stroke)),
      node((-0.3, 2), align(center)[*Compressor*], ..ns(compressor-fill, 0.5pt + compressor-stroke)),
      node(
        (1, 2),
        align(center)[*ZisK AIR*],
        ..ns(leaf-fill, 0.5pt + leaf-stroke),
      ),

      // Level 3: leaves
      node(
        (-1.7, 3),
        align(center)[*ZisK AIR*],
        ..ns(leaf-fill, 0.5pt + leaf-stroke),
      ),
      node(
        (-0.3, 3),
        align(center)[*ZisK AIR*],
        ..ns(leaf-fill, 0.5pt + leaf-stroke),
      ),

      // alpha → leaves (dashed)
      edge((2.2, 0), (1, 2), "->", stroke: dash-stroke),
      edge((2.2, 0), (-1.7, 3), "->", bend: -20deg, stroke: dash-stroke),
      edge((2.2, 0), (-0.3, 3), "->", stroke: dash-stroke),

      // Proof flow: leaves → compressors → agg → root
      {
        let el(body) = text(size: 5.5pt, fill: luma(50), body)
        // leaf → compressor: raw proof
        edge((-1.7, 3), (-1.7, 2), $pi$, "->", stroke: arr-stroke, label-side: right)
        edge((-0.3, 3), (-0.3, 2), $pi$, "->", stroke: arr-stroke, label-side: right)
        edge((1, 2), (1, 1), $pi$, "->", stroke: arr-stroke, label-side: right)
        // compressor → aggregation: compressed proof + public outputs
        edge((-1.7, 2), (-1, 1), $(pi_L, s_L, bold(c)_L)$, "->", stroke: arr-stroke, label-side: left)
        edge((-0.3, 2), (-1, 1), $(pi_R, s_R, bold(c)_R)$, "->", stroke: arr-stroke, label-side: right)
        // aggregation → root: aggregated proof + accumulated outputs
        edge((-1, 1), (0, 0), $(pi_L, s_L, bold(c)_L)$, "->", stroke: arr-stroke, label-side: left)
        // compressor (shallow branch) → root
        edge((1, 1), (0, 0), $(pi_R, s_R, bold(c)_R)$, "->", stroke: arr-stroke, label-side: right)
      },
    )
  },
  caption: [
    Example aggregation tree (binary, unbalanced). $alpha$ is a public input broadcast to all leaf provers (dashed arrows) and to the root verifier. Solid arrows show proof propagation (bottom-up).
  ],
) <fig:aggregation-tree>

=== Root Verification

At the root of the aggregation tree, two checks are performed simultaneously using the accumulated public outputs.

The first is _bus balancing_: the accumulated LogUp sum must be zero,
$
  s_"root" = sum_(i=1)^k s_i = 0,
$
which is the global bus-balancing condition from @def:bus-balancing ---every message sent on every bus has been received exactly once with matching values.

The second is _challenge correctness_: the accumulated LtHash vector $bold(c)_"root" = sum_i bold(c)_i$ must be consistent with the challenge $alpha$ assumed by all leaf proofs. Concretely, the root verifier checks that $alpha$ equals the field element obtained by embedding $bold(c)_"root"$ into $bb(K)$, confirming that $alpha$ was honestly derived from the full set of commitments and not chosen adversarially.

Both checks reduce to simple arithmetic on values propagated up the tree as public outputs, with no need to inspect any individual AIR trace. This hierarchical structure achieves a clean separation of responsibilities: leaf AIRs prove only local constraint satisfaction; compressor nodes convert proofs to a recursion-friendly format; aggregation nodes accumulate both running totals; and the root enforces global bus balancing and challenge integrity. Because every node can proceed as soon as its children complete, the entire proving pipeline is fully parallelizable ---no single AIR needs to handle the entire computation, eliminating the bottleneck of a monolithic circuit.
