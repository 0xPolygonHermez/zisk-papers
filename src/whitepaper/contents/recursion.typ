#import "../../shared/lib.typ": Balanced, BusCont, Commit, DeriveKey, Local, definition, lemma, remark, theorem, verifier, vk
#import "../../shared/aggregation-tree.typ": aggregation-tree

ZisK uses proof recursion to combine the independent per-segment proofs produced by trace splitting into a single, globally consistent argument. This section introduces proof recursion in general, identifies the two specific problems it resolves in ZisK, and details the aggregation structure.

== Proof Recursion

A proving system is called _recursive_ when it can verify the validity of another proof as part of its own computation. The key observation is that the verifier $V$ is itself a computation ---it reads a proof, the verification key, and the public statement, and performs arithmetic checks--- so it can be expressed as polynomial constraints and be proved. A _recursive verifier_ is therefore a computation expressed as constraints ---in ZisK, an AIR--- that takes a proof $pi$ as witness and a public statement $x$ as input, and checks that $verifier(vk, x, pi)$ accepts for some verification key $vk$. Proving it yields a _recursive proof_: a succinct argument that attests to the correctness of an underlying proof without re-exposing its content.

The power of this construction comes from its composability. Since a recursive proof is itself a valid proof, it can in turn be fed into another recursive verifier, producing a proof of a proof of a proof. Iterating this idea allows a sequence of computations ---or a collection of independent computations--- to be folded into a single, constant-size argument regardless of the number of steps or the size of the individual proofs. The result is a _proof composition_ that scales arbitrarily: adding more computations does not make the final proof larger or more expensive to verify.

Recursive composition is normally used for three purposes. The first is _proof compression_: reducing the size of a proof by recursively re-proving its verifier within the same proving system. The second is _proof aggregation_: combining many proofs $pi_1, ..., pi_M$ into a single argument that attests to the validity of all of them simultaneously. The third is _cross-system conversion_: translating a proof generated with one proving system (e.g., a proof with large size but fast to generate) into a proof in another system better suited for a particular context (e.g., a compact proof with fast verification).

ZisK leverages recursion for the previous purposes ---trace splitting (@sec:continuations) produces many segment proofs that need to be aggregated; intermediate aggregation proofs are themselves recursively re-proved to shrink their size; and the topmost proof can be converted into a format suitable for the external verifier--- but it also relies on it to resolve two open problems left by trace splitting itself.

The first is _cross-chip bus balancing_. Each segment proof contributes a partial sum $s_i in bb(K)$ to the global bus interaction. Global correctness requires $sum_i s_i = 0$, but no individual proof can verify this: it requires aggregating the partial sums across all segment instances and all chips.

The second, and more subtle, is _challenge derivation_. The LogUp argument (@sec:arithmetization) uses random field elements $alpha$ and $gamma$, derived via the Fiat-Shamir heuristic, to compress bus interactions into a single accumulated value per AIR. For the global balancing equation $sum_i s_i = 0$ to be meaningful, all partial sums must be computed under the _same_ challenges. In a monolithic proof this is automatic: there is one prover transcript and one application of Fiat-Shamir. In the trace-splitting design, each segment is proved independently and would naturally derive its own challenges from its own commitments ---producing values that differ across instances and making the partial sums incommensurable.

== Challenge Derivation <sec:challenge-derivation>

The challenge derivation problem arises because Fiat-Shamir ties each challenge to the transcript of a single prover. When segment provers operate independently, their transcripts diverge and so do their challenges.

The solution is to separate challenge derivation from proof generation: all segment provers first commit to their traces, and the challenge is then derived from the full set of commitments and broadcast to all provers as a _public input_. Each segment proof proves the statement "given the key $chi = (alpha, gamma)$, my witness satisfies my constraints and my partial sum is $s_i$" ---the key is _assumed_, not derived internally.

A natural first attempt is plain hashing: Given commitments $"com"_1, ..., "com"_M$, compute: $ chi = H(dots.c H(H("com"_1, "com"_2), "com"_3) dots.c, "com"_M). $
This fails for two reasons. It is inherently sequential, which negates the parallelism of trace splitting; and it is order-dependent: changing the processing order changes the challenge, so partial batches cannot be computed independently and merged.

ZisK instead uses a _multiset hash_ @AC:CDDGS03 ---a function $cal(H)$ from multisets over a message space $cal(M)$ to a commutative group $(cal(G), +)$, satisfying two properties:
- _Multiset Homomorphism_: $cal(H)(S union T) = cal(H)(S) + cal(H)(T)$ for any two multisets $S, T$ over $cal(M)$.
- _Multiset Collision-Resistance_: finding distinct multisets $S != T$ with $cal(H)(S) = cal(H)(T)$ is computationally infeasible.

The standard construction builds $cal(H)$ from an inner _hash-to-group_ function $h : cal(M) -> cal(G)$ as
$
  cal(H)(S) = sum_(x in S) m_S (x) dot h(x),
$
where $m_S (x) in NN$ is the multiplicity of $x$ in $S$. As a consequence, segment provers can independently hash and sum their own commitments, and partial accumulators from disjoint subsets can be merged later by addition. The common key is then obtained from the global accumulator $"acc" = cal(H)({"com"_1, dots, "com"_M})$ by a deterministic _key derivation_. It also absorbs the public statement $bold(p)$ (@sec:zisk-statement), so that the key is bound to the statement as well as to the commitments:
$
  chi = (alpha, gamma) = DeriveKey(bold(p), "acc") in KK^2.
$
ZisK instantiates $DeriveKey$ with Poseidon2: a sponge absorbs $bold(p)$ and $"acc"$ and squeezes a _global challenge_ in $KK$, from which a fresh sponge squeezes $alpha$ and $gamma$. Multiset collision-resistance ensures that the only way for a malicious prover to alter $chi$ is to alter the statement or the multiset of commitments, which would in turn invalidate at least one segment proof.

ZisK instantiates this scheme with _LtHash_ @ZISK:LTHASH, a lattice-based multiset hash. The group $cal(G)$ is the vector space $ZZ_p^n$. The element hashed for a segment is its _typed commitment_ $(tau, "com")$: the type $tau$ of its AIR, identified by the root of the AIR's fixed columns, together with $"com"$, the Merkle root of its stage-1 trace commitment (@sec:backend) and its stage-1 AIR values. The inner hash $h$ absorbs $(tau, "com")$ into a Poseidon2 sponge @AFRICACRYPT:GraKhoSch23 and squeezes its $16$-element state, then applies $22$ further Poseidon2 permutations in a chain, concatenating the $23$ states into a pseudorandom vector $h(tau, "com") in ZZ_p^n$ with $n = 23 dot 16 = 368$. Multiset collision-resistance for LtHash reduces to the Short Integer Solution (SIS) @STOC:Ajtai96 lattice problem, which is believed to remain hard even against quantum adversaries.

The LtHash group has finite exponent $p$: adding $p$ copies of the same element to a multiset leaves $cal(H)$ unchanged, since $p dot h(x) equiv 0 in ZZ_p^n$. To rule out such trivial collisions, the scheme is restricted to multisets of cardinality less than $2^B << p$, with $B = 20$. ZisK enforces this bound by tracking the multiset cardinality alongside the accumulator, via the leaf-count counter $kappa$ that the recursion carries and range-checks against $2^B$ at every aggregation node (introduced in the next section). Equivalently, one may think of LtHash as using an augmented per-element hash $h'(x) = (h(x), 1) in ZZ_p^(n+1)$, so that the last coordinate of the multiset hash tracks the total cardinality automatically.

Correctness of the assumed key $chi$ must be verified ---otherwise a malicious prover could substitute any $chi$ to make the partial sums balance artificially. Since $cal(H)$ is homomorphic over multiset union, this verification is embedded directly into the aggregation tree: each node carries a _partial accumulator_ over the commitments in its subtree, and a parent node combines the two by addition. At the root, the fully accumulated value is checked against the claimed $chi$, confirming that it was correctly derived from the statement and the entire set of commitments.

== What ZisK Proves <sec:zisk-statement>

Before describing the recursive verifiers, we make explicit what ZisK as a whole proves. Given a fixed program $P$, ZisK proves that there exists a successful execution of $P$ (@sec:execution_model), on some input and some hint stream, that declares a given list of public outputs: formally, a witness of the execution relation $cal(R)_"exec"$ of @def:r-exec. The data exposed to the verifier form the _external statement_ $bold(p)_"ext" in FF^(68)$:
- the program commitment $"root"_"ROM" in FF^4$, the Merkle root of the Rom chip's cached columns, which hold the program code (@sec:rom-bus);
- the $32$ public outputs $"out"_0, dots, "out"_(31) in [0, 2^(64))$ of @sec:public-outputs, each as two $32$-bit limbs (@sec:word-encoding), for $64$ field elements.
Everything else ---the input, the hints, the intermediate states of the execution--- stays inside the prover. A proof additionally carries $8$ _proof values_ $bold(p)_"pv" in FF^8$: boolean flags, chosen by the prover, that switch on the genesis anchors of the optional AIRs (the ROM data and input data regions and the DMA variants, @sec:continuation-bus). They are not part of the external statement, but every node of the recursion carries them together with it, so we call the pair $bold(p) = (bold(p)_"ext", bold(p)_"pv")$ the _public statement_ of the tree, following the security analysis @ZISK:RECURSION.

These publics are bound to the execution by two mechanisms. The program commitment is the root of a commitment that the Rom AIR's proof opens, so every instruction fetched on the ROM Bus belongs to the program committed by $"root"_"ROM"$ (@sec:rom-bus). The public outputs are bound through _global messages_: messages that no AIR emits, but that the system as a whole adds to the buses as a function of $bold(p)$. We write $cal(G)(bold(p))$ for the multiset of global messages of $bold(p)$. It contains
- the $32$ messages $(mono("pubout"), i, 0, "out"_(i,0), "out"_(i,1), "out"_(i,0), "out"_(i,1))$ received on the Operation Bus for $i in [0, 32)$, where $("out"_(i,0), "out"_(i,1))$ are the limbs of $"out"_i$. The only sender of `pubout` messages is the Main chip, at the `pubout` instructions of the epilogue, so balancing the Operation Bus forces the execution to declare exactly the outputs in $bold(p)_"ext"$;
- the genesis and terminus anchors of the continuation buses (@sec:continuation-bus), the optional ones gated by $bold(p)_"pv"$;
- the initialisation of the registers on the Memory Bus (@sec:registers).

The execution is split into segments and proved piecewise (@def:segmentation): given the family of chips $frak(A) = {(cal(C)_tau, cal(I)_tau)}_(tau in [M])$ (@tbl:chip-inventory), each segment is a witness for one of the AIRs $cal(C)_tau$. The segments are stitched together by global bus balancing ---which includes the continuation buses of @sec:continuation-bus and the global messages $cal(G)(bold(p))$--- under the key $chi$ derived from the statement and the prover's commitments as described in @sec:challenge-derivation.

== Recursive Structure <sec:recursive-structure>

ZisK assembles its proof as the aggregation tree illustrated in @fig:aggregation-tree. The leaves of the tree are the individual AIR segment instances; the internal nodes are _recursive verifiers_ ---AIRs whose constraints verify their children's proofs and expose a small number of public values that propagate upward. Internal nodes have a fixed arity, but the tree is not required to be balanced: it is built opportunistically as proofs complete, so a branch that finishes early can be verified immediately while others are still running. On top of the aggregation tree sits a single _Final Verifier_, which is the only node that performs the global checks ---bus balancing across all segments, and consistency of the key $chi$.

The key $chi$ is an input to the entire structure, not something derived inside it. Before proving starts, $chi$ is derived according to @sec:challenge-derivation and broadcast to every leaf prover. Each leaf proof takes $chi$ as a public input and uses it to compute its bus contribution. The tree then recomputes, as it aggregates, the quantities from which $chi$ was derived, and the Final Verifier checks that the key the leaves used is the one derived from what was actually aggregated.

The tree has four kinds of nodes: AIR leaves, leaf verifiers, aggregation verifiers, and the Final Verifier. For some AIRs a fifth kind, the _compressor_, sits between the AIR leaf and its leaf verifier: the STARK proofs of these AIRs are large, and verifying them directly would make the leaf verifier large as well. A compressor is a recursive verifier that verifies the AIR proof and re-proves the same statement at a lower rate (@sec:backend), so that the leaf verifier verifies the compressor's proof instead. The precise relation that every kind of node attests to is stated, with the analysis of what the relations establish together, in the companion security analysis @ZISK:RECURSION; here we describe what each node checks.

=== Accumulators <sec:accumulators>

Three quantities travel up the tree and are combined at every aggregation node. Each is an _accumulator_: a commutative monoid of values, a contribution of every leaf, and checks that the aggregation nodes and the Final Verifier apply to it (@tbl:accumulators). The value of an aggregation node is the sum of the values of its non-null children, so by associativity and commutativity the value of every node is the sum of the contributions of the leaves below it, whatever the shape of the subtree. This independence of the shape is essential: the key is derived before the tree is built, so the quantities it is checked against must not depend on how the leaves are grouped. A hash-tree accumulation $bold(c) = H(bold(c)_1, bold(c)_2, bold(c)_3)$, for instance, would force the prover to fix the tree before deriving $chi$.

#figure(
  {
    set text(size: 8.5pt, hyphenate: false)
    table(
      stroke: 0.3pt,
      columns: (24%, 14%, 20%, 16%, 26%),
      align: (left, left, left, left, left),
      table.header([*Accumulator*], [*Monoid*], [*Leaf contribution*], [*Child check*], [*Root check*]),
      [leaf counter $kappa$], [$(FF, +)$], [$1$], [$kappa in [1, 2^B)$], [$kappa in [1, 2^B)$],
      [challenge accumulator $bold(c)$], [$(ZZ_p^n, +)$], [$h(tau, "com")$], [---], [$chi = DeriveKey(bold(p), bold(c))$],
      [bus partial sum $s$], [$(KK, +)$], [$BusCont_chi (cal(I)_tau, w)$], [---], [$s + s_"glob" (bold(p), chi) = 0$],
    )
  },
  caption: [The three accumulators of the recursion. $s_"glob" (bold(p), chi)$ is the LogUp sum of the global messages $cal(G)(bold(p))$ under the key $chi$ (@sec:logup-reduction).],
  kind: table,
) <tbl:accumulators>

The values of the three accumulators at a node, together with the node's _type_ $tau$, form its _recursive statement_
$
  sigma = (tau, kappa, bold(c), s),
$
where $tau in [M]$ is the AIR type for a leaf verifier, $tau = M + 1$ marks an aggregation verifier, and $tau = 0$ marks a null child. The counter is the only accumulator checked at every node: it bounds the number of leaves below any node by $2^B - 1$, which is the cardinality restriction required by the multiset hash (@sec:challenge-derivation). The challenge accumulator and the bus partial sum are checked only at the root.

=== Nodes of the Tree

*AIR leaves.* A leaf corresponds to a segment instance of one of the chips of ZisK, of _type_ $tau in [M]$. Its proof establishes that its witness is _locally satisfying_ ---it satisfies the AIR, its fixed columns are those that the AIR prescribes, the AIR values that the AIR binds to the public statement equal the designated coordinates of $bold(p)$, and its cached columns open the cached-column commitment carried in $bold(p)$, which for the Rom AIR is $"root"_"ROM"$--- and exposes the statement $(bold(p), chi, s, "com")$, with $s$ its bus contribution under $chi$ and $"com"$ its trace commitment. Exposing the commitment lets the leaf verifier above hash it into the challenge accumulator. The type is not part of the statement: it is determined by which AIR the leaf instantiates, and the leaf verifier above lifts it into its own statement.

*Compressors.* The STARK proofs of some AIRs are large (@sec:topology), and verifying them directly would make their leaf verifiers large as well. For these types, a _compressor_ sits between the AIR leaf and its leaf verifier: a recursive verifier that verifies the AIR proof with the AIR's key and re-proves the same statement $(bold(p), chi, s, "com")$ at a lower rate (@sec:backend). The compressor changes neither the statement nor its meaning; it only replaces the AIR proof by a smaller one.

*Leaf verifiers.* A leaf verifier sits above an AIR leaf, or above its compressor. There is one leaf verifier per AIR type: the leaf verifier of type $tau$ verifies the AIR proof, or the compressor's proof, with a hard-coded key, and re-exposes its statement in the common format $(bold(p), chi, sigma, vk)$ of the tree, with recursive statement $sigma = (tau, 1, h(tau, "com"), s)$: its type is the constant $tau$ ---fixed by which AIR the leaf verifier is for, not chosen by the prover---, its counter is $1$, and its challenge contribution is the hash of its typed commitment, which it computes itself. The key $vk$ it carries is not used by the leaf verifier: an aggregation verifier may need to verify a proof of _itself_ as one of its children, and an AIR cannot hard-code its own verification key without a circular dependency at setup time. ZisK breaks this loop by treating that key as a public that is _propagated_ through every level of the tree, with the Final Verifier closing the loop by fixing it to a hard-coded constant.

*Aggregation verifiers.* An aggregation verifier has three child slots. A slot holds either the proof of a child ---a leaf verifier or another aggregation verifier--- or a _null child_, a placeholder of type $0$ that is not verified and contributes nothing; at least two slots hold proofs. The aggregation verifier reads each non-null child's type, checks that it is a leaf-verifier type with counter $1$ or the aggregation type $M + 1$ with a counter in $[2, 2^B)$, and verifies the child accordingly: with the hard-coded leaf-verifier key of type $tau$ for $tau in [M]$, or with the propagated key $vk$ for $tau = M + 1$. It verifies every child on a statement that carries its own $(bold(p), chi, vk)$, and declares the type $M + 1$ and the sums of its children's accumulators. The aggregated challenge contribution is exactly the multiset-homomorphism step of $cal(H)$: it is $cal(H)$ of the union of the subtrees' multisets of typed commitments. Since every child is verified on its parent's $(bold(p), chi, vk)$, every node of a valid tree carries the same public statement, key and verification key; and since the counters lie in $[1, 2^B)$, there are at least two non-null children and $3 dot 2^B < p$, every child's counter is strictly smaller than its parent's.

*Final Verifier.* The Final Verifier takes the topmost proof of the tree as its single child, which may not be a null child, and verifies it with the same dispatch as an aggregation verifier. It closes the recursion loop on $vk$: it hard-codes the actual verification key $vk_"AGG"$ of the aggregation verifier and verifies its child on a statement that carries this constant, which binds the child's declared $vk$ to it. It then performs the two global checks. The first, $s + s_"glob" (bold(p), chi) = 0$, where $s_"glob"$ is the bus contribution of the global messages $cal(G)(bold(p))$ (@sec:zisk-statement), which the Final Verifier computes itself, is the global bus-balancing condition under the key $chi$. The second, $chi = DeriveKey(bold(p), bold(c))$, is _key correctness_: by the multiset homomorphism of $cal(H)$, the value of $bold(c)$ at the top of the tree is $cal(H)$ of the multiset of typed commitments of the leaves, so this check confirms that $chi$ was derived from the statement and the full set of commitments. After this point the recursive statement, the key and the proof values are witnesses of the Final Verifier, and only the external statement $bold(p)_"ext"$ remains visible to an external verifier.

Every execution has at least one Main segment and one Mem segment (@sec:chip-inventory), so the tree has at least two leaves and the root of the aggregation tree is an aggregation verifier; the Final Verifier nevertheless dispatches on the type, so it also accepts a single-leaf tree. Both global checks reduce to simple arithmetic on values propagated up the tree, with no need to inspect any individual AIR trace. This layered structure achieves a clean separation of responsibilities: AIR leaves prove only local constraint satisfaction; leaf verifiers convert proofs to a recursion-friendly format; aggregation verifiers accumulate the three running totals; and the Final Verifier enforces global bus balancing and key correctness. Because every node can proceed as soon as its children complete, the entire proving pipeline is fully parallelizable ---no single AIR needs to handle the entire computation, eliminating the bottleneck of a monolithic AIR.

#figure(
  aggregation-tree(root-check: $s + s_"glob" (bold(p), chi) = 0$),
  caption: [
    An aggregation tree with three AIR instances. Each arrow carries the statement and the proof that a node produces, which the node above takes as witness. The AIR proofs of some types are compressed: an optional compressor (dashed, purple) verifies the AIR proof and re-exposes the same statement, and the leaf verifier then verifies the compressor's proof instead; $verifier_"SEG"^((tau))$ denotes the verifier of the AIR proof or of its compressor, $verifier_"REC" [vk]$ the verification of a child according to its type, and $sans("Typed")$ the check of the type and counter of a child. Aggregation verifiers are drawn with two children, whereas they have three slots, the unused ones holding null children.
  ],
) <fig:aggregation-tree>

== Security <sec:recursion-security>

The companion security analysis @ZISK:RECURSION states the relation that every node of the tree attests to and proves what they establish together: the external verifier of the final proof is knowledge-sound for the execution relation $cal(R)_"exec"$ (@def:r-exec), with an explicit error and under explicit assumptions on the primitives. It extracts, from any accepting final proof, a bounded collection of locally satisfying AIR witnesses that, together with the global messages, balance every bus, and decodes that collection into an execution of the committed program, following the bus contracts of @sec:bus-meaning and the access log of @def:access-log.
