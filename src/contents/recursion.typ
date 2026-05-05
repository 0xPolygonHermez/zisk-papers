#import "../lib.typ": definition
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

ZisK uses proof recursion to combine the independent per-segment proofs produced by trace splitting into a single, globally consistent argument. This section introduces proof recursion in general, identifies the two specific problems it resolves in ZisK, and details the aggregation structure.

== Proof Recursion

A proving system is called _recursive_ when it can verify the validity of another proof as part of its own computation. The key observation is that the verifier $V$ is itself a computation ---it reads a proof, the verification key, and the public statement, and performs arithmetic checks--- so it can be expressed as polynomial constraints and be proved. A _recursive verifier_ is therefore an arithmetic circuit that takes a proof $pi$ as witness and a public statement $x$ as input, and checks that $V("vk", x, pi)$ accepts for some verification key $"vk"$. Wrapping this circuit in a proof yields a _recursive proof_: a succinct argument that attests to the correctness of an underlying proof without re-exposing its content.

The power of this construction comes from its composability. Since a recursive proof is itself a valid proof, it can in turn be fed into another recursive verifier, producing a proof of a proof of a proof. Iterating this idea allows a sequence of computations ---or a collection of independent computations--- to be folded into a single, constant-size argument regardless of the number of steps or the size of the individual proofs. The result is a _proof composition_ that scales arbitrarily: adding more computations does not make the final proof larger or more expensive to verify.

Recursive composition is normally used for three purposes. The first is _proof compression_: reducing the size of a proof by recursively re-proving its verifier within the same proving system. The second is _proof aggregation_: combining many proofs $pi_1, ..., pi_M$ into a single argument that attests to the validity of all of them simultaneously. The third is _cross-system conversion_: translating a proof generated with one proving system (e.g., a proof with large size but fast to generate) into a proof in another system better suited for a particular context (e.g., a compact proof with fast verification).

ZisK leverages recursion for the previous purposes ---trace splitting (@sec:continuations) produces many segment proofs that need to be aggregated; intermediate aggregation proofs are themselves recursively re-proved to shrink their size; and the topmost proof can be converted into a format suitable for the external verifier--- but it also relies on it to resolve two open problems left by trace splitting itself.

The first is _cross-chip bus balancing_. Each segment proof contributes a partial sum $s_i in bb(K)$ to the global bus interaction. Global correctness requires $sum_i s_i = 0$, but no individual proof can verify this: it requires aggregating the partial sums across all segment instances and all chips.

The second, and more subtle, is _challenge derivation_. The LogUp argument (@sec:arithmetization) uses random field elements $alpha$ and $gamma$, derived via the Fiat-Shamir heuristic, to compress bus interactions into a single accumulated value per AIR. For the global balancing equation $sum_i s_i = 0$ to be meaningful, all partial sums must be computed under the _same_ challenges. In a monolithic proof this is automatic: there is one prover transcript and one application of Fiat-Shamir. In the trace-splitting design, each segment is proved independently and would naturally derive its own challenges from its own commitments ---producing values that differ across instances and making the partial sums incommensurable.

== Challenge Derivation <sec:challenge-derivation>

The challenge derivation problem arises because Fiat-Shamir ties each challenge to the transcript of a single prover. When segment provers operate independently, their transcripts diverge and so do their challenges.

The solution is to separate challenge derivation from proof generation: all segment provers first commit to their traces, and the challenge is then derived from the full set of commitments and broadcast to all provers as a _public input_. Each segment proof proves the statement "given the challenge $alpha$, my witness satisfies my constraints and my partial sum is $s_i$" ---the challenge is _assumed_, not derived internally.

A natural first attempt is plain hashing: Given commitments $"com"_1, ..., "com"_M$, compute: $ alpha = H(dots.c H(H("com"_1, "com"_2), "com"_3) dots.c, "com"_M). $
This fails for two reasons. It is inherently sequential, which negates the parallelism of trace splitting; and it is order-dependent: changing the processing order changes the challenge, so partial batches cannot be computed independently and merged.

ZisK instead uses a _multiset hash_ @AC:CDDGS03 ---a function $cal(H)$ from multisets over a message space $cal(M)$ to a commutative group $(cal(G), +)$, satisfying two properties:
- _Multiset Homomorphism_: $cal(H)(S union T) = cal(H)(S) + cal(H)(T)$ for any two multisets $S, T$ over $cal(M)$.
- _Multiset Collision-Resistance_: finding distinct multisets $S != T$ with $cal(H)(S) = cal(H)(T)$ is computationally infeasible.

The standard construction builds $cal(H)$ from an inner _hash-to-group_ function $h : cal(M) -> cal(G)$ as
$
  cal(H)(S) = sum_(x in S) m_S (x) dot h(x),
$
where $m_S (x) in NN$ is the multiplicity of $x$ in $S$. As a consequence, segment provers can independently hash and sum their own commitments, and partial accumulators from disjoint subsets can be merged later by addition. The common challenge is then obtained from the global accumulator $"acc" = cal(H)({"com"_1, dots, "com"_M})$ via a deterministic projection $"DeriveAlpha" : cal(G) -> KK$, which we instantiate as a Poseidon2 hash of the accumulator vector whose output is interpreted as an element of $KK$:
$
  alpha = "DeriveAlpha"("acc") in KK.
$
Multiset collision-resistance ensures that the only way for a malicious prover to alter $alpha$ is to alter the multiset of commitments, which would in turn invalidate at least one segment proof.

ZisK instantiates this scheme with _LtHash_ @ZISK:LTHASH, a lattice-based multiset hash. The group is $cal(G)$ is the vector space $ZZ_p^n$, and the inner hash $h : FF^k -> ZZ_p^n$ is realised by hashing a commitment $"com"$ to a single field element $c = H("com")$ via Poseidon2 @AFRICACRYPT:GraKhoSch23, then iteratively expanding $c$ into a long pseudorandom vector $h("com") in ZZ_p^n$. Multiset collision-resistance for LtHash reduces to the Short Integer Solution (SIS) @STOC:Ajtai96 lattice problem, which is believed to remain hard even against quantum adversaries. ZisK targets $128$-bit security with concrete parameters $n = 372$ and cardinality bound $B = 2^(20)$ (introduced below).

The LtHash group has finite exponent $p$: adding $p$ copies of the same element to a multiset leaves $H$ unchanged, since $p dot h(x) equiv 0 in ZZ_p^n$. To rule out such trivial collisions, the scheme is restricted to multisets of cardinality at most $B << p$. ZisK enforces this bound by tracking the multiset cardinality alongside the accumulator, via the leaf-count counter $kappa$ that the recursion carries and range-checks against $2^B$ at every aggregation node (introduced in the next section). Equivalently, one may think of LtHash as using an augmented per-element hash $h'(x) = (h(x), 1) in ZZ_p^(n+1)$, so that the last coordinate of the multiset hash tracks the total cardinality automatically.

Correctness of the assumed challenge $alpha$ must be verified ---otherwise a malicious prover could substitute any $alpha$ to make the partial sums balance artificially. Since $cal(H)$ is homomorphic over multiset union, this verification is embedded directly into the aggregation tree: each node carries a _partial accumulator_ over the commitments in its subtree, and a parent node combines the two by addition. At the root, the fully accumulated value is checked against the claimed $alpha$, confirming that it was correctly derived from the entire set of commitments.

== What ZisK Proves <sec:zisk-statement>

Before describing the recursive verifiers, we make explicit what ZisK as a whole proves. Given a fixed program $P$, ZisK proves that there exists a valid execution of $P$ on some input producing some output. Some elements of this relation ---typically a subset of the program's inputs and a subset of its outputs--- can be exposed to the verifier as publics; we collect all such public elements into a single vector $bold(p) in FF^k$, the _public statement_. Everything else (the prover's hints, intermediate memory state, and any non-public output) stays inside the prover.

The execution is split into segments and proved piecewise: given ZisK's circuit $cal(C) = {(cal(A)_i, cal(I)_i)}_(i=1)^M$, each segment is an instance of one of the AIRs $(cal(A)_i, cal(I)_i) in cal(C)$, and its trace covers a contiguous range of execution steps. The segments are stitched together by the global bus-balancing condition (@def:bus-balancing) and the global challenge $alpha in KK$, derived from the prover's commitments via Fiat-Shamir as described in @sec:challenge-derivation.

== Recursive Structure

Throughout this section it will be convenient to describe a verifier by the _relation_ it attests to. We write a relation as
$
  cal(R) = { (x\; w) mid(|) phi(x, w) },
$
where $x$ is the _public statement_ and $w$ is the _witness_; the predicate $phi$ specifies the constraints that must hold. A proof for $cal(R)$ on a given $x$ convinces the verifier that there exists $w$ such that $(x\; w) in cal(R)$.

ZisK assembles its proof as the aggregation tree illustrated in @fig:aggregation-tree. The leaves of the tree are the individual AIR segment instances; the internal nodes are _recursive verifiers_ ---arithmetic circuits that take their children's proofs as witness, verifies them, and expose a small number of public outputs that propagate upward. Internal nodes have a fixed arity, but the tree is not required to be balanced: it is built opportunistically as proofs complete, so a branch that finishes early can be verified immediately while others are still running. On top of the aggregation tree sits a single _Final Verifier_, which is the only node that performs the global checks ---bus balancing across all segments, and consistency of the global challenge $alpha$.

Two quantities are accumulated upward at every internal node: the bus partial sum $s$ and the challenge contributions $bold(c)$. These accumulations are the mechanism by which the two global checks are reduced, at the Final Verifier, to simple arithmetic on the public outputs that arrive there.

The challenge $alpha$ is an input to the entire structure, not something derived inside it. Before proving starts, $alpha$ is derived according to @sec:challenge-derivation and broadcast to every leaf prover. Each leaf proof takes $alpha$ as a public input and uses it to compute its partial bus sum $s$. The verifiers then accumulate both $s$ and the challenge contributions $bold(c)$ upward, and the Final Verifier receives $alpha$ as a public input to check that it matches what the tree actually accumulated.

The tree has four kinds of nodes: AIR leaves, leaf verifiers, aggregation verifiers, and the Final Verifier.

=== AIR Leaves

A _leaf_ of the aggregation tree corresponds to a particular segment instance of one of the pairs $(cal(A), cal(I))$ in $cal(C)$. We write $tau in [M]$ for the index of that pair ---the leaf's _circuit type_--- and use the convention that $cal(A)_tau$ and $cal(I)_tau$ refer to it.

As public statement, the proof at a leaf takes the program-level publics $bold(p)$, the challenge $alpha$ and the AIR-level summary $s$. The circuit type $tau$ itself is _not_ part of the leaf's public statement: it is determined by which AIR the leaf instantiates and is lifted into the public statement by the leaf verifier above (described next), so that the upper levels of the tree can read it and decide which AIR's verification key to use.

Given $alpha in KK$, $bold(p) in FF^(k)$, $s in KK$, a proof for a leaf of circuit type $tau$ attests that there exists $bold(T) in FF^(N times W)$, $bold(a) in FF^(V)$ such that:
- The witness $(bold(T), bold(a))$ satisfies the AIR $cal(A)_tau$, and is consistent with the program-level publics $bold(p)$ ---i.e., the cells of the trace and AIR values that the AIR designates as bindings to the program's publics match $bold(p)$.
- The partial bus sum $s$ is correctly computed from the AIR's interactions $cal(I)_tau$ and $(bold(T), bold(a))$ under the challenge $alpha$.

In the language of relations:
$
  cal(R)_"AIR"^((tau)) = lr(
    {
      cases(
        delim: #none,
        ,
        (bold(p), alpha\, s)\; (bold(T), bold(a)),
        ,
      )
      mid(|)
      cases(
        delim: #none,
        gap: #(0pt + 0.4em),
        (bold(T), bold(a)) "satisfies" cal(A)_tau "and is consistent with" bold(p),
        and quad quad quad quad s = "BusCont"_alpha (cal(I)_tau, bold(T), bold(a))
      )
    }
  )
$
where $"BusCont"_alpha (cal(I)_tau, bold(T), bold(a))$ is the AIR contribution to the bus, computed from the set of interactions $cal(I)_tau$ and the witness $(bold(T), bold(a))$ under $alpha$ (as defined in @sec:arguments).


=== Leaf Verifier

A _leaf verifier_ sits directly above an AIR leaf. It takes the AIR proof $pi$ as witness, runs the AIR verifier on it, and re-exposes the AIR proof's public statement, augmented with three new publics that the recursive layer above will rely on: the circuit type $tau in [M]$, a counter $kappa = 1$, and the challenge contribution $bold(c) in ZZ_p^n$. There is one leaf verifier circuit per pair $(cal(A)_i, cal(I)_i) in cal(C)$: a leaf verifier for the AIR of circuit type $tau$ runs the verifier $V_"AIR"^((tau))$, which is hard-wired to the verification key of $cal(A)_tau$, and assigns the constant $tau$ ---fixed by which AIR the leaf verifier is for, not chosen by the prover. The counter $kappa$ will, as it propagates up through aggregation, track how many leaf proofs have been combined under each subtree, enforcing the cardinality bound required by the multiset hash of @sec:challenge-derivation. The challenge contribution $bold(c)$ is the leaf's contribution to the global accumulator: the leaf verifier computes it itself by applying the inner hash-to-group $h$ of @sec:challenge-derivation.

The leaf verifier additionally carries an extra public $"vk"$ ---a verification key--- which it does not use itself. The reason is circular: as we will see, an aggregation verifier may need to verify a proof of _itself_ as one of its children, and a circuit cannot hard-code its own verification key without inducing a circular dependency at setup time. ZisK breaks this loop by treating that key as a public that is _propagated_ through every level of the tree, with the Final Verifier closing the loop by fixing $"vk"$ to a hard-coded constant. The leaf verifier is the bottom of this chain: it has no aggregator below it to verify, so $"vk"$ is just declared so that the aggregation verifier above can read it.

For brevity we bundle the four recursion-tracking publics into a single tuple
$
  sigma = (s, tau, kappa, bold(c)),
$
which we call the _recursive statement_. Every recursive verifier (leaf, aggregation, and Final) carries its own $sigma$ in its public statement, and aggregation verifiers read their children's $sigma$'s as part of the witness. We also adopt the shorthand $V_X (x, pi)$ for $V("vk"_X, x, pi)$, where $"vk"_X$ is the verification key of relation $cal(R)_X$. A proof for the leaf verifier of circuit type $tau$ attests that:
$
  cal(R)_"LEAF"^((tau)) = lr(
    {
      cases(
        delim: #none,
        ,
        (bold(p), alpha, sigma, "vk")\; pi,
        ,
      )
      mid(|)
      cases(
        delim: #none,
        gap: #(0pt + 0.4em),
        V_"AIR"^((tau)) ((bold(p), alpha\, s), pi) = "accept",
        and quad bold(c) = h("com"(bold(T), bold(a))),
        and quad quad quad quad kappa = 1
      )
    }
  )
$
where $V_"AIR"^((tau))$ is the verifier induced by $cal(R)_"AIR"^((tau))$. The bus contribution $s$ is checked by $V_"AIR"^((tau))$, so accepting the AIR proof binds it to the value committed in $pi$, which the leaf verifier then forwards unchanged into its public statement. The challenge contribution $bold(c)$, on the other hand, is computed by the leaf verifier itself, since $h$ only depends on the trace commitment $"com"(bold(T), bold(a))$ that lives inside $pi$, which the leaf verifier has direct access to without help from the AIR verifier. The remaining components are constants associated with this leaf verifier: $tau$ is fixed by the choice of $V_"AIR"^((tau))$, and $kappa = 1$ marks "this subtree contains one leaf". Finally, $"vk"$ is carried as a public but unused at this level.

=== Aggregation Verifier

An _aggregation verifier_ takes the proofs $pi_L, pi_R$ produced by its two children as witness, runs the recursive verifier on each of them, and accumulates the bus partial sums $s_L, s_R$ and the challenge contributions $bold(c)_L, bold(c)_R$ upward. The contribution $bold(c) = bold(c)_L + bold(c)_R$ is exactly the multiset-homomorphism step of the multiset hash $cal(H)$: under the leaf-element interpretation given above, summing the children's $bold(c)$'s computes $cal(H)$ on the union of the two subtrees' multisets. The accumulated $(s, bold(c))$ propagate up the tree until the root.

Each child of an aggregation verifier is itself either a leaf verifier or another aggregation verifier. The aggregation verifier therefore reads each child's circuit type $tau$ and selects the appropriate verifier accordingly: the per-AIR verifier $V_"LEAF"^((tau))$ when $tau in [M]$, or the aggregation verifier $V_"AGG"$ otherwise. We denote this selection by $V_"REC"^((tau))$. The aggregation verifier exposes its own circuit type $tau = M + 1$ in its public statement to mark the resulting proof as "aggregated", so the level above dispatches to $V_"AGG"$ when verifying it.

Dispatching also requires the aggregation verifier to know the verification key of whichever inner verifier it ends up running. The keys $"vk"_("LEAF")^((1)), dots, "vk"_("LEAF")^((M))$ of the per-circuit-type leaf verifiers are fixed at setup time and are hard-coded into the aggregation circuit. The aggregation verifier's _own_ key is exactly the public $"vk"$ introduced above: this is the value that lets the aggregator verify aggregation children. The aggregator additionally binds each of its children to declare the same value of $"vk"$ as itself, so the same value propagates uniformly through the entire tree.

A proof for an aggregation verifier attests that:
- The two child proofs $pi_L$ and $pi_R$ each verify under the verifier selected by their respective circuit types $tau_L, tau_R in [M+1]$, and under their respective public statements.
- The partial bus sum $s$ is the sum of the children's partial sums, $s = s_L + s_R$.
- The challenge contribution $bold(c)$ is the sum of the children's contributions, $bold(c) = bold(c)_L + bold(c)_R$.
- The leaf-count counter $kappa$ is the sum of the children's counters, $kappa = kappa_L + kappa_R$, that satisfy $kappa_L, kappa_R < 2^B$ for the bound $B$ from @sec:challenge-derivation.
- Both children declare the same $"vk"$ as the parent.
- The exposed circuit type is the aggregation marker $tau = M + 1$.

Formally:
$
  cal(R)_"AGG" = lr(
    {
      cases(
        delim: #none,
        ,
        (bold(p), alpha, sigma, "vk")\; ((sigma_L, pi_L), (sigma_R, pi_R)),
        ,
      )
      mid(|)
      cases(
        delim: #none,
        gap: #(0pt + 0.4em),
        V_"REC"^((tau_L))((bold(p), alpha, sigma_L, "vk"), pi_L) = "accept",
        and V_"REC"^((tau_R))((bold(p), alpha, sigma_R, "vk"), pi_R) = "accept",
        and quad quad quad quad tau = M + 1,
        and quad kappa = kappa_L + kappa_R and kappa_L\,kappa_R < 2^B,
        and quad quad quad quad s = s_L + s_R,
        and quad quad quad quad bold(c) = bold(c)_L + bold(c)_R,
      )
    }
  )
$
where $V_"REC"^((tau)) = V_"LEAF"^((tau))$ if $tau in [M]$ and $V_"REC"^((tau)) = V_"AGG"$ if $tau = M + 1$. Each $V_"REC"^((tau))$ is invoked with $"vk"$ in the child's public statement, so by accepting that proof the aggregator implicitly checks that the child declared the same $"vk"$ as itself.

=== Final Verifier

The _Final Verifier_ sits above the aggregation tree. It takes the topmost aggregation proof produced by the tree as its single child, runs the aggregation verifier $V_"AGG"$ on it, and additionally enforces the two global checks. Because the topmost node of the aggregation tree is always an aggregation verifier, the Final expects its child to advertise $tau = M + 1$; this saves the Final from having to dispatch over circuit types as the internal aggregators do. The Final also closes the recursion loop on $"vk"$: it carries $"vk"$ as a parameter ---a hard-coded constant, the actual aggregator's verification key fixed at setup time--- and binds the child's declared $"vk"$ to that constant. After this point $s$, $bold(c)$, $tau$, and $kappa$ have served their purpose and are no longer carried forward: they are absorbed into the global checks below, and only the program-level public statement $bold(p)$ remains visible to an external verifier.

A proof for the Final Verifier attests that:
- The child's circuit type is $tau = M + 1$, i.e., the child is an aggregation proof.
- The child aggregation proof $pi$ verifies under the public statement $(bold(p), alpha, sigma, "vk")$, with the child's declared $"vk"$ matching the Final's hard-coded constant.
- The leaf-count counter $kappa$ is less than $2^B$, confirming that the multiset of commitments aggregated under the child satisfies the cardinality bound required by $cal(H)$ (see @sec:challenge-derivation).
- Bus balancing holds globally: $s = 0$.
- The challenge $alpha$ was honestly derived from the full set of commitments: $alpha = "DeriveAlpha"(bold(c))$, where $"DeriveAlpha"$ is the deterministic projection of the accumulated $bold(c)$ into $bb(K)$ described in @sec:challenge-derivation.

Formally, the Final Verifier attests to the relation:
$
  cal(R)_"FINAL" = lr(
    {
      cases(
        delim: #none,
        ,
        bold(p) \; (alpha, sigma, pi),
        ,
      )
      mid(|)
      cases(
        delim: #none,
        gap: #(0pt + 0.4em),
        V_"AGG" ((bold(p), alpha, sigma, "vk"), pi) = "accept",
        quad quad quad quad quad and kappa < 2^B,
        quad quad quad quad quad and s = 0,
        quad quad and alpha = "DeriveAlpha"(bold(c)),
      )
    }
  )
$

The two equality checks have direct global meaning. The first, $s = 0$, is the global bus-balancing condition from @def:bus-balancing ---every message sent on every bus across every segment has been received exactly once with matching values. The second, $alpha = "DeriveAlpha"(bold(c))$, is _challenge correctness_: by the multiset homomorphism of $cal(H)$, the value of $bold(c)$ at the top of the tree equals $sum_i h("com"(bold(T)_i, bold(a)_i)) = cal(H)(S)$ over the multiset $S$ of segment trace commitments, so this check confirms that $alpha$ was honestly derived from the full set of commitments and not chosen adversarially.

Both checks reduce to simple arithmetic on values propagated up the tree as publics, with no need to inspect any individual AIR trace. This layered structure achieves a clean separation of responsibilities: AIR leaves prove only local constraint satisfaction; leaf verifiers convert proofs to a recursion-friendly format; aggregation verifiers accumulate both running totals; and the Final Verifier enforces global bus balancing and challenge integrity. Because every node can proceed as soon as its children complete, the entire proving pipeline is fully parallelizable ---no single AIR needs to handle the entire computation, eliminating the bottleneck of a monolithic circuit.

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
        (-1.8, 0),
        align(center)[*in:* $alpha$],
        fill: luma(248),
        stroke: 0.5pt + luma(160),
        inset: 5pt,
        corner-radius: 2pt,
      ),


      // Level 0: Final Verifier
      node(
        (0, 0),
        align(
          center,
        )[*Final Verifier* #linebreak() #sub[$V(pi) = "accept"$] #linebreak() #sub[$s = 0$] #linebreak() #sub[$alpha = "DeriveAlpha"(bold(c))$]],
        fill: root-fill,
        stroke: 0.7pt + root-stroke,
        width: nw + 1.2cm,
        height: nh + 0.7cm,
        corner-radius: 3pt,
      ),

      // Level 1: Top Aggregation Verifier (single child of Final)
      node(
        (0, 1),
        align(
          center,
        )[*Aggregation Verifier* #linebreak() #sub[$V(pi_L), V(pi_R) = "accept"$] #linebreak() #sub[$s = s_L + s_R$] #linebreak() #sub[$bold(c) = bold(c)_L + bold(c)_R$]],
        fill: agg-fill,
        stroke: agg-stroke,
        width: nw + 1cm,
        height: nh + 0.7cm,
        corner-radius: 3pt,
      ),

      // Level 2: a deeper aggregation (left) and a leaf verifier (right)
      node(
        (-1, 2),
        align(
          center,
        )[*Aggregation Verifier* #linebreak() #sub[$V(pi_L), V(pi_R) = "accept"$] #linebreak() #sub[$s = s_L + s_R$] #linebreak() #sub[$bold(c) = bold(c)_L + bold(c)_R$]],
        fill: agg-fill,
        stroke: agg-stroke,
        width: nw + 1cm,
        height: nh + 0.7cm,
        corner-radius: 3pt,
      ),
      node(
        (1, 3),
        align(center)[*Leaf Verifier* #linebreak() #sub[$V(pi) = "accept"$]],
        fill: compressor-fill,
        stroke: 0.5pt + compressor-stroke,
        width: nw,
        height: nh + 0.3cm,
        corner-radius: 3pt,
      ),

      // Level 3: all three leaf verifiers (left two under the bottom aggregation; right one feeding directly the top aggregation)
      node(
        (-1.7, 3),
        align(center)[*Leaf Verifier* #linebreak() #sub[$V(pi) = "accept"$]],
        fill: compressor-fill,
        stroke: 0.5pt + compressor-stroke,
        width: nw,
        height: nh + 0.3cm,
        corner-radius: 3pt,
      ),
      node(
        (-0.3, 3),
        align(center)[*Leaf Verifier* #linebreak() #sub[$V(pi) = "accept"$]],
        fill: compressor-fill,
        stroke: 0.5pt + compressor-stroke,
        width: nw,
        height: nh + 0.3cm,
        corner-radius: 3pt,
      ),

      // Level 4: all three ZisK AIRs aligned at the same height
      node(
        (-1.7, 4),
        align(center)[*ZisK AIR*],
        ..ns(leaf-fill, 0.5pt + leaf-stroke),
      ),
      node(
        (-0.3, 4),
        align(center)[*ZisK AIR*],
        ..ns(leaf-fill, 0.5pt + leaf-stroke),
      ),
      node(
        (1, 4),
        align(center)[*ZisK AIR*],
        ..ns(leaf-fill, 0.5pt + leaf-stroke),
      ),

      // alpha → Final and AIR leaves
      edge((-1.8, 0), (0, 0), "->", stroke: dash-stroke),
      edge((-1.8, 0), (1, 4), "->", bend: 15deg, stroke: dash-stroke),
      edge((-1.8, 0), (-1.8, 4), "->", bend: -15deg, stroke: dash-stroke),
      edge((-1.8, 0), (-0.3, 4), "->", stroke: dash-stroke),

      // p → AIR leaves: short labelled arrows entering each AIR from below
      edge((-1.7, 4.5), (-1.7, 4), $(bold(p), alpha)$, "->", label-side: right),
      edge((-0.3, 4.5), (-0.3, 4), $(bold(p), alpha)$, "->", label-side: right),
      edge((1, 4.5), (1, 4), $(bold(p), alpha)$, "->", label-side: right),

      // Proof + recursive statement flow
      {
        // AIR → Leaf Verifier
        edge((-1.7, 4), (-1.7, 3), $(bold(p), alpha, s, pi)$, "->", stroke: arr-stroke, label-side: right)
        edge((-0.3, 4), (-0.3, 3), $(bold(p), alpha, s, pi)$, "->", stroke: arr-stroke, label-side: right)
        edge((1, 4), (1, 3), $(bold(p), alpha, s, pi)$, "->", stroke: arr-stroke, label-side: right)
        // Leaf Verifier → Aggregation
        edge((-1.7, 3), (-1, 2), $(bold(p), alpha, s_L, pi_L, "vk")$, "->", stroke: arr-stroke, label-side: left)
        edge((-0.3, 3), (-1, 2), $(bold(p), alpha, s_R, pi_R, "vk")$, "->", stroke: arr-stroke, label-side: right)
        // Bottom aggregation + right leaf verifier → top aggregation
        edge((-1, 2), (0, 1), $(bold(p), alpha, s_L, pi_L, "vk")$, "->", stroke: arr-stroke, label-side: left)
        edge((1, 3), (0, 1), $(bold(p), alpha, s_R, pi_R, "vk")$, "->", stroke: arr-stroke, label-side: right)
        // Top aggregation → Final
        edge((0, 1), (0, 0), $(bold(p), alpha, s, pi, "vk")$, "->", stroke: arr-stroke, label-side: right)
      },
    )
  },
  caption: [
    Example aggregation tree (binary, unbalanced). Dashed arrows carry the program-level challenge $alpha$ down to the leaves. Solid arrows carry inputs and outputs to each level: each node's outgoing label is its output, and the incoming labels at any node are its inputs.
  ],
) <fig:aggregation-tree>
