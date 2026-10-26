#import "../../lib.typ": Balanced, BusCont, Commit, DeriveKey, Local, definition, lemma, remark, theorem
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

Before describing the recursive verifiers, we make explicit what ZisK as a whole proves. Given a fixed program $P$, ZisK proves that there exists a successful execution of $P$ (@sec:execution_model), on some input and some hint stream, that declares a given list of public outputs. The data exposed to the verifier form the _external statement_ $bold(p)_"ext" in FF^(68)$:
- the program commitment $"root"_"ROM" in FF^4$, the Merkle root of the Rom chip's cached columns, which hold the program code (@sec:rom-bus);
- the $32$ public outputs $"out"_0, dots, "out"_(31) in [0, 2^(64))$ of @sec:public-outputs, each as two $32$-bit limbs (@sec:word-encoding), for $64$ field elements.
Everything else ---the input, the hints, the intermediate states of the execution--- stays inside the prover. A proof additionally carries $8$ _proof values_ $phi in FF^8$: boolean flags, chosen by the prover, that switch on the genesis anchors of the optional AIRs (the ROM data and input data regions and the DMA variants, @sec:continuation-bus). They are not part of the external statement, but every node of the recursion carries them together with it, so we call the pair $bold(p) = (bold(p)_"ext", phi)$ the _public statement_ of the tree, following the security analysis @ZISK:RECURSION.

These publics are bound to the execution by two mechanisms. The program commitment is the root of a commitment that the Rom AIR's proof opens, so every instruction fetched on the ROM Bus belongs to the program committed by $"root"_"ROM"$ (@sec:rom-bus). The public outputs are bound through _global messages_: messages that no AIR emits, but that the system as a whole adds to the buses as a function of $bold(p)$. We write $cal(G)(bold(p))$ for the multiset of global messages of $bold(p)$. It contains
- the $32$ messages $(mono("pubout"), i, 0, "out"_(i,0), "out"_(i,1), "out"_(i,0), "out"_(i,1))$ received on the Operation Bus for $i in [0, 32)$, where $("out"_(i,0), "out"_(i,1))$ are the limbs of $"out"_i$. The only sender of `pubout` messages is the Main chip, at the `pubout` instructions of the epilogue, so balancing the Operation Bus forces the execution to declare exactly the outputs in $bold(p)_"ext"$;
- the genesis and terminus anchors of the continuation buses (@sec:continuation-bus), the optional ones gated by $phi$;
- the initialisation of the registers on the Memory Bus (@sec:registers).

The execution is split into segments and proved piecewise (@def:segmentation): given ZisK's circuit $cal(C) = {(cal(A)_tau, cal(I)_tau)}_(tau=1)^M$ (@tbl:chip-inventory), each segment is a witness for one of the AIRs $cal(A)_tau$. The segments are stitched together by global bus balancing ---which includes the continuation buses of @sec:continuation-bus and the global messages $cal(G)(bold(p))$--- under the key $chi$ derived from the statement and the prover's commitments as described in @sec:challenge-derivation.

== Recursive Structure <sec:recursive-structure>

Throughout this section it will be convenient to describe a verifier by the _relation_ it attests to. We write a relation as
$
  cal(R) = { (x\; w) mid(|) psi(x, w) },
$
where $x$ is the _public statement_ and $w$ is the _witness_; the predicate $psi$ specifies the constraints that must hold. A proof for $cal(R)$ on a given $x$ convinces the verifier that there exists $w$ such that $(x\; w) in cal(R)$. We write $V_X (x, pi) in {0, 1}$ for the verifier of the argument system proving $cal(R)_X$, with key $"vk"_X$, and $V("vk", x, pi)$ when the key is a variable. The relations below follow the companion security analysis @ZISK:RECURSION, which states them for an abstract bus argument and accumulator and proves their soundness (@sec:recursion-security).

ZisK assembles its proof as the aggregation tree illustrated in @fig:aggregation-tree. The leaves of the tree are the individual AIR segment instances; the internal nodes are _recursive verifiers_ ---arithmetic circuits that take their children's proofs as witness, verify them, and expose a small number of public outputs that propagate upward. Internal nodes have a fixed arity, but the tree is not required to be balanced: it is built opportunistically as proofs complete, so a branch that finishes early can be verified immediately while others are still running. On top of the aggregation tree sits a single _Final Verifier_, which is the only node that performs the global checks ---bus balancing across all segments, and consistency of the key $chi$.

The key $chi$ is an input to the entire structure, not something derived inside it. Before proving starts, $chi$ is derived according to @sec:challenge-derivation and broadcast to every leaf prover. Each leaf proof takes $chi$ as a public input and uses it to compute its bus contribution. The tree then recomputes, as it aggregates, the quantities from which $chi$ was derived, and the Final Verifier checks that the key the leaves used is the one derived from what was actually aggregated.

The tree has four kinds of nodes: AIR leaves, leaf verifiers, aggregation verifiers, and the Final Verifier. For some AIRs a fifth kind, the _compressor_, sits between the AIR leaf and its leaf verifier: the STARK proofs of these AIRs are large, and verifying them directly would make the leaf verifier circuit large as well. A compressor is a recursive verifier that verifies the AIR proof and re-proves the same statement at a lower rate (@sec:backend), so that the leaf verifier verifies the compressor's proof instead. Since it changes neither the statement nor its meaning, we fold the compressor into the leaf verifier in the relations below; it appears separately only in the topology of @sec:topology.

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

The values of the three accumulators at a node, together with the node's _circuit type_ $tau$, form its _recursive statement_
$
  sigma = (tau, kappa, bold(c), s),
$
where $tau in [M]$ is the AIR type for a leaf verifier, $tau = M + 1$ marks an aggregation verifier, and $tau = 0$ marks a null child. The counter is the only accumulator checked at every node: it bounds the number of leaves below any node by $2^B - 1$, which is the cardinality restriction required by the multiset hash (@sec:challenge-derivation). The challenge accumulator and the bus partial sum are checked only at the root.

=== AIR Leaves

A _leaf_ of the aggregation tree corresponds to a particular segment instance of one of the pairs $(cal(A)_tau, cal(I)_tau)$ in $cal(C)$, where $tau in [M]$ is the leaf's circuit type. Its witness is $w = (bold(T), bold(a))$, and its proof establishes that the witness is _locally satisfying_, written $Local_tau (bold(p), w)$:
+ $w$ satisfies the AIR $cal(A)_tau$;
+ the fixed columns of $bold(T)$ are those prescribed by the AIR (@sec:arithmetization);
+ the AIR values that the AIR binds to the public statement equal the designated coordinates of $bold(p)$;
+ the cached columns of $bold(T)$ open the cached-column commitment carried in $bold(p)$; for the Rom AIR, this is $"root"_"ROM"$.

The leaf's statement exposes the public statement $bold(p)$, the key $chi$, the bus contribution $s$ and the trace commitment $"com"$. The relation is in _commit-and-prove_ form: the commitment is part of the statement, so that the leaf verifier above can hash it into the challenge accumulator. The circuit type $tau$ is not part of the statement: it is determined by which AIR the leaf instantiates, and the leaf verifier above lifts it into its own statement.
$
  cal(R)_"AIR"^((tau)) = lr(
    {
      cases(
        delim: #none,
        ,
        (bold(p), chi\, s\, "com")\; (bold(T), bold(a)),
        ,
      )
      mid(|)
      cases(
        delim: #none,
        gap: #(0pt + 0.4em),
        Local_tau (bold(p), (bold(T), bold(a))),
        and quad s = BusCont_chi (cal(I)_tau, (bold(T), bold(a))),
        and quad Commit(bold(T), bold(a)) = "com"
      )
    }
  )
$

=== Leaf Verifier

A _leaf verifier_ sits directly above an AIR leaf. It takes the AIR proof $pi_"AIR"$ as witness, runs the AIR verifier on it, and re-exposes the AIR proof's statement in the common format $(bold(p), chi, sigma, "vk")$ of the tree. There is one leaf verifier circuit per AIR type: the leaf verifier of type $tau$ runs the verifier $V_"AIR"^((tau))$, which is hard-wired to the verification key of $cal(A)_tau$, and sets the circuit type of its recursive statement to the constant $tau$ ---fixed by which AIR the leaf verifier is for, not chosen by the prover. Its counter is $1$, and its challenge contribution is the hash $h(tau, "com")$ of its typed commitment, which the leaf verifier computes itself.

The leaf verifier additionally carries an extra public $"vk"$ ---a verification key--- which it does not use itself. The reason is circular: as we will see, an aggregation verifier may need to verify a proof of _itself_ as one of its children, and a circuit cannot hard-code its own verification key without inducing a circular dependency at setup time. ZisK breaks this loop by treating that key as a public that is _propagated_ through every level of the tree, with the Final Verifier closing the loop by fixing $"vk"$ to a hard-coded constant. The leaf verifier is the bottom of this chain: it has no aggregator below it to verify, so $"vk"$ is just declared so that the aggregation verifier above can read it.
$
  cal(R)_"LEAF"^((tau)) = lr(
    {
      cases(
        delim: #none,
        ,
        (bold(p), chi\, sigma\, "vk")\; ("com", pi_"AIR"),
        ,
      )
      mid(|)
      cases(
        delim: #none,
        gap: #(0pt + 0.4em),
        sigma = (tau, 1, bold(c), s),
        and quad V_"AIR"^((tau)) ((bold(p), chi, s, "com"), pi_"AIR") = 1,
        and quad bold(c) = h(tau, "com")
      )
    }
  )
$
The bus contribution $s$ is certified by the AIR proof and forwarded unchanged; the other components of $sigma$ are constants of the circuit or are computed from the commitment.

=== Aggregation Verifier

An _aggregation verifier_ has three child slots. A slot holds either the proof of a child ---a leaf verifier or another aggregation verifier--- or a _null child_, a placeholder of circuit type $0$ that is not verified and contributes nothing; at least two slots hold proofs. The aggregation verifier reads each non-null child's circuit type and verifies the child accordingly: with the leaf-verifier key $"vk"_"LEAF"^((tau))$ for $tau in [M]$, which is hard-coded in the aggregation circuit, or with the propagated key $"vk"$ for $tau = M + 1$, which is the aggregation verifier's own key and arrives as a public.

#definition(title: "Recursive Dispatch")[
  For a circuit type $tau$ and a key $"vk"$, the _dispatched verifier_ is
  $
    V_"REC"^((tau)) ["vk"](x, pi) := cases(
      V_"LEAF"^((tau))(x, pi) & "if" tau in [M]\,,
      V("vk", x, pi) & "if" tau = M + 1\,,
    )
  $
  and $V_"REC"^((tau)) ["vk"]$ rejects everything if $tau in.not [M + 1]$; in particular, a null child never passes it. The _typing predicate_ on a circuit type and a counter is
  $
    sans("Typed")(tau, kappa) := (tau in [M] and kappa = 1) or (tau = M + 1 and 2 <= kappa < 2^B).
  $
] <def:dispatch>

With $x_X := (bold(p), chi, sigma_X, "vk")$ the statement of the child in slot $X in [3]$, $sigma_X = (tau_X, kappa_X, bold(c)_X, s_X)$ its recursive statement, and $N := {X in [3] : tau_X != 0}$ the set of non-null slots, a proof for the aggregation verifier attests to
$
  cal(R)_"AGG" = lr(
    {
      cases(
        delim: #none,
        ,
        (bold(p), chi\, sigma\, "vk")\; ((sigma_X, pi_X))_(X in [3]),
        ,
      )
      mid(|)
      cases(
        delim: #none,
        gap: #(0pt + 0.4em),
        sigma = (M + 1, kappa, bold(c), s) "and" abs(N) >= 2,
        and quad sans("Typed")(tau_X, kappa_X) "and" V_"REC"^((tau_X)) ["vk"](x_X, pi_X) = 1 "for" X in N,
        and quad kappa = sum_(X in N) kappa_X "and" bold(c) = sum_(X in N) bold(c)_X "and" s = sum_(X in N) s_X
      )
    }
  )
$
The aggregated challenge contribution $bold(c)$ is exactly the multiset-homomorphism step of $cal(H)$: it is $cal(H)$ of the union of the subtrees' multisets of typed commitments. Two invariants of this relation drive the soundness argument. First, the _propagation invariant_: every non-null child is verified on a statement that carries the parent's own $(bold(p), chi, "vk")$, so every node of a valid tree carries the same public statement, key and verification key. Second, the _counter invariant_: the typing predicate places the counter of every non-null child in $[1, 2^B)$, there are at least two of them, and the counters are summed over the integers since $3 dot 2^B < p$, so every child's counter is strictly smaller than its parent's.

=== Final Verifier

The _Final Verifier_ sits above the aggregation tree. It takes the topmost proof of the tree as its single child, verifies it with the same dispatch as an aggregation verifier, and enforces the global checks. It also closes the recursion loop on $"vk"$: it hard-codes the actual verification key $"vk"_"AGG"$ of the aggregation verifier and verifies its child on a statement that carries this constant, which binds the child's declared $"vk"$ to it. After this point the recursive statement, the key and the proof values have served their purpose: they are witnesses of the Final Verifier, and only the external statement $bold(p)_"ext"$ remains visible to an external verifier. With $bold(p) := (bold(p)_"ext", phi)$,
$
  cal(R)_"FINAL" = lr(
    {
      cases(
        delim: #none,
        ,
        bold(p)_"ext" \; (phi, chi, sigma, pi),
        ,
      )
      mid(|)
      cases(
        delim: #none,
        gap: #(0pt + 0.4em),
        sigma = (tau, kappa, bold(c), s) "and" sans("Typed")(tau, kappa),
        and quad V_"REC"^((tau)) ["vk"_"AGG"]((bold(p), chi, sigma, "vk"_"AGG"), pi) = 1,
        and quad s + s_"glob" (bold(p), chi) = 0,
        and quad chi = DeriveKey(bold(p), bold(c))
      )
    }
  )
$
where $s_"glob" (bold(p), chi)$ is the bus contribution of the global messages $cal(G)(bold(p))$ (@sec:zisk-statement), which depends only on the statement and the key, so the Final Verifier computes it itself. The typing predicate excludes a null child at the root, which would otherwise leave $bold(c)$ and $s$ unconstrained.

#remark[
  Every execution has at least one Main segment and one Mem segment (@sec:chip-inventory), so the tree has at least two leaves and the root of the aggregation tree is an aggregation verifier. The Final Verifier nevertheless dispatches on the circuit type, so the relation also covers a single-leaf tree.
]

The two equality checks have direct global meaning. The first, $s + s_"glob" = 0$, is the global bus-balancing condition (@def:bus-balancing) under the key $chi$: every message sent on every bus across every segment and every global message is received with matching values. The second, $chi = DeriveKey(bold(p), bold(c))$, is _key correctness_: by the multiset homomorphism of $cal(H)$, the value of $bold(c)$ at the top of the tree equals $sum_ell h(tau_ell, "com"_ell) = cal(H)(S)$ over the multiset $S$ of typed commitments of the leaves, so this check confirms that $chi$ was honestly derived from the statement and the full set of commitments and not chosen adversarially.

Both checks reduce to simple arithmetic on values propagated up the tree as publics, with no need to inspect any individual AIR trace. This layered structure achieves a clean separation of responsibilities: AIR leaves prove only local constraint satisfaction; leaf verifiers convert proofs to a recursion-friendly format; aggregation verifiers accumulate the three running totals; and the Final Verifier enforces global bus balancing and key correctness. Because every node can proceed as soon as its children complete, the entire proving pipeline is fully parallelizable ---no single AIR needs to handle the entire computation, eliminating the bottleneck of a monolithic circuit.

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

    let nw = 2.3cm
    let nh = 0.82cm
    let ns(f, s) = (fill: f, stroke: s, width: nw, height: nh + 0.3pt, corner-radius: 3pt)

    diagram(
      spacing: (1.1cm, 1.35cm),


      // Level 0: Final Verifier
      node(
        (0, 0),
        align(
          center,
        )[*Final Verifier* #linebreak() #sub[$V(pi) = 1$] #linebreak() #sub[$s + s_"glob" = 0$] #linebreak() #sub[$chi = DeriveKey(bold(p), bold(c))$]],
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
        )[*Aggregation Verifier* #linebreak() #sub[$V(pi_L), V(pi_R) = 1$] #linebreak() #sub[$kappa = kappa_L + kappa_R$, $s = s_L + s_R$] #linebreak() #sub[$bold(c) = bold(c)_L + bold(c)_R$]],
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
        )[*Aggregation Verifier* #linebreak() #sub[$V(pi_L), V(pi_R) = 1$] #linebreak() #sub[$kappa = kappa_L + kappa_R$, $s = s_L + s_R$] #linebreak() #sub[$bold(c) = bold(c)_L + bold(c)_R$]],
        fill: agg-fill,
        stroke: agg-stroke,
        width: nw + 1cm,
        height: nh + 0.7cm,
        corner-radius: 3pt,
      ),
      node(
        (1, 3),
        align(center)[*Leaf Verifier* #linebreak() #sub[$V(pi) = 1$]],
        fill: compressor-fill,
        stroke: 0.5pt + compressor-stroke,
        width: nw,
        height: nh + 0.3cm,
        corner-radius: 3pt,
      ),

      // Level 3: all three leaf verifiers (left two under the bottom aggregation; right one feeding directly the top aggregation)
      node(
        (-1.7, 3),
        align(center)[*Leaf Verifier* #linebreak() #sub[$V(pi) = 1$]],
        fill: compressor-fill,
        stroke: 0.5pt + compressor-stroke,
        width: nw,
        height: nh + 0.3cm,
        corner-radius: 3pt,
      ),
      node(
        (-0.3, 3),
        align(center)[*Leaf Verifier* #linebreak() #sub[$V(pi) = 1$]],
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


      // p → AIR leaves: short labelled arrows entering each AIR from below
      edge((-1.7, 4.5), (-1.7, 4), $(bold(p), chi)$, "->", label-side: right),
      edge((-0.3, 4.5), (-0.3, 4), $(bold(p), chi)$, "->", label-side: right),
      edge((1, 4.5), (1, 4), $(bold(p), chi)$, "->", label-side: right),

      // Proof + recursive statement flow
      {
        // AIR → Leaf Verifier
        edge((-1.7, 4), (-1.7, 3), $(bold(p), chi, s, "com"), pi_"AIR"$, "->", stroke: arr-stroke, label-side: right)
        edge((-0.3, 4), (-0.3, 3), $(bold(p), chi, s, "com"), pi_"AIR"$, "->", stroke: arr-stroke, label-side: right)
        edge((1, 4), (1, 3), $(bold(p), chi, s, "com"), pi_"AIR"$, "->", stroke: arr-stroke, label-side: right)
        // Leaf Verifier → Aggregation
        edge((-1.7, 3), (-1, 2), $(bold(p), chi, sigma_L, "vk"), pi_L$, "->", stroke: arr-stroke, label-side: left)
        edge((-0.3, 3), (-1, 2), $(bold(p), chi, sigma_R, "vk"), pi_R$, "->", stroke: arr-stroke, label-side: right)
        // Bottom aggregation + right leaf verifier → top aggregation
        edge((-1, 2), (0, 1), $(bold(p), chi, sigma_L, "vk"), pi_L$, "->", stroke: arr-stroke, label-side: left)
        edge((1, 3), (0, 1), $(bold(p), chi, sigma_R, "vk"), pi_R$, "->", stroke: arr-stroke, label-side: right)
        // Top aggregation → Final
        edge((0, 1), (0, 0), $(bold(p), chi, sigma, "vk"), pi$, "->", stroke: arr-stroke, label-side: right)
      },
    )
  },
  caption: [
    Example aggregation tree (unbalanced; drawn with two children per aggregation node for readability, whereas ZisK aggregation nodes have three, unused slots being null children). Solid arrows carry inputs and outputs to each level: each node's outgoing label is its output, and the incoming labels at any node are its inputs.
  ],
) <fig:aggregation-tree>

== Security of the Recursion <sec:recursion-security>

The relations of @sec:recursive-structure say what each node checks. The companion analysis @ZISK:RECURSION proves what they establish together: from any accepting Final proof one can extract a bounded collection of locally satisfying AIR witnesses that, together with the global messages, balance every bus. We state the target relation and the result here; the exact model, the proofs and the ledger of assumptions are in @ZISK:RECURSION.

A _typed witness collection_ is a finite list $L = ((tau_1, w_1), dots, (tau_(abs(L)), w_(abs(L))))$ of AIR witnesses, each with its circuit type, in no particular order. The _message multiset_ of a witness $w$ of type $tau$ assigns to every bus message $(b, v)$ the total signed multiplicity with which $w$ emits it,
$
  "Msg"_tau (w)(b, v) := sum_((b', m, bold(e)) in cal(I)_tau, b' = b) sum_(r=1)^(N_tau) m(r) dot bold(1)[bold(e)(r) = v] in FF,
$
and the collection is _balanced for_ $bold(p)$, written $Balanced_bold(p) (L)$, if $sum_i "Msg"_(tau_i)(w_i) + cal(G)(bold(p)) = 0$: every message, counting the global messages of @sec:zisk-statement, is sent and received with the same total multiplicity. This is the bus-balancing condition of @def:bus-balancing, extended with the global messages.

#definition(title: "Bounded global satisfiability")[
  With $bold(p) := (bold(p)_"ext", phi)$, the _target relation_ of ZisK's recursion is
  $
    (bold(p)_"ext"; (phi, L)) in cal(R)_"ZisK"
    <=>
    cases(
      1 <= abs(L) < 2^B\,,
      Local_(tau_i)(bold(p), w_i) "for every" i in [abs(L)]\,,
      Balanced_bold(p) (L).
    )
  $
] <def:r-zisk>

The relation has the same statement as the Final relation, the external statement $bold(p)_"ext"$, and its three conjuncts are exactly what the recursion adds to the individual AIR proofs: a bound on the number of segments, one common public statement, and global bus balancing. The bus argument enters through the following bound for the LogUp sum of @sec:logup-reduction, which for a multiset $D$ of messages under the key $chi = (alpha, gamma)$ we write $cal(F)_chi (D) := sum_((b, v)) D(b, v) \/ (alpha + hat(e)_gamma (b, v))$, with $hat(e)_gamma$ the compression of @def:compressed-interaction-value.

#lemma(title: [LogUp soundness @ZISK:RECURSION])[
  Let $D != 0$ be an $FF$-weighted multiset of at most $Lambda$ messages of length at most $ell$. For $chi = (alpha, gamma)$ uniform in $KK^2$,
  $
    Pr_chi [cal(F)_chi (D) = 0] <= frac(ell dot binom(Lambda, 2) + Lambda - 1, abs(KK)).
  $
] <lem:logup>

The first term bounds the probability that two distinct messages collide under the compression, and the second the number of roots in $alpha$ of the resulting nonzero rational identity. Since a fixed but unbalanced collection would pass the root check $s + s_"glob" = 0$ only if $cal(F)_chi$ vanished on its nonzero signed multiplicity, the lemma is what turns the root check into balance, provided the key is independent of the collection. This independence is what the derivation of $chi$ from the typed commitments (@sec:challenge-derivation) provides.

#theorem(title: [Correct-witness extractability @ZISK:RECURSION])[
  Model Poseidon2, and with it $h$, $DeriveKey$ and the trace commitment, as a random oracle, and assume that straight-line knowledge extraction composes across the layers of the tree and that the multiset hash $cal(H)$ is preimage aware on multisets of fewer than $2^B$ elements. Then there is an extractor that, from any accepting Final proof for $bold(p)_"ext"$, outputs $(phi, L)$ with $(bold(p)_"ext"; (phi, L)) in cal(R)_"ZisK"$, except with probability at most
  $
    & epsilon_"ks" (Pi_"FINAL") + (kappa_"max" - 1) dot epsilon_"ks" (Pi_"AGG") + kappa_"max" dot max_tau epsilon_"ks" (Pi_"LEAF"^((tau))) + kappa_"max" dot max_tau epsilon_"ks" (Pi_"AIR"^((tau))) \
    & + (Q + 1) dot frac(ell dot binom(Lambda_"max", 2) + Lambda_"max" - 1, abs(KK)) + epsilon_"pa" (cal(H)) + epsilon_"ext" (Commit),
  $
  where $kappa_"max" = 2^B - 1$, $epsilon_"ks" (Pi)$ is the knowledge-soundness error of the argument system $Pi$ for the relation of each node, $Q$ bounds the adversary's oracle queries, $Lambda_"max"$ bounds the number of bus terms of a collection of fewer than $2^B$ witnesses together with the global messages, and $epsilon_"pa"$ and $epsilon_"ext"$ are the preimage-awareness and extractability errors of the multiset hash and the trace commitment.
] <thm:cwe>

The extractor descends the tree: it extracts the Final Verifier's witness, unrolls the aggregation verifiers ---at most $kappa - 1$ of them for a root counter $kappa$, by the counter invariant and the requirement of two non-null children---, extracts the AIR proof below every leaf verifier and, from it, the AIR witness. Each layer costs the knowledge-soundness error of its argument system once per node, which gives the first line of the bound. The second line is the bus argument: the derived key must be independent of the extracted collection for @lem:logup to apply, and this is where the random oracle answers at most $Q + 1$ fresh queries, and where the multiset hash and the trace commitment must let the extractor recover, at the time $chi$ is derived, the collection that the adversary will later open.

Two of the hypotheses are idealizations, and @ZISK:RECURSION discusses both. Straight-line extraction composes across a recursion only for arguments that remain knowledge-sound relative to the same oracle, which is not known to hold for succinct arguments in general; and preimage awareness of LtHash does not follow from a standard assumption, only its collision resistance does, from the hardness of SIS. Without the second idealization the bus argument can be proved by rewinding at the cost of a square-root loss. With $B = 20$, $kappa_"max"$ is about $10^6$, so the bound should be read as a statement about the structure of the reduction rather than as a concrete security level; the concrete $128$-bit figures of @sec:backend-params are those of the individual STARK proofs.

The theorem concerns AIR witnesses, not executions. That a balanced collection of locally satisfying witnesses encodes one successful execution of the committed program ---the memory argument, the stitching of segments by the continuation buses, and the semantics of every chip--- is the semantic layer built on top of it. Two further points are outside the theorem: balance is established with multiplicities in $FF$, and lifting it to equality of multisets over the integers requires bounds on every multiplicity column; and each compressor node adds one more knowledge-soundness term, of the same form as that of the leaf verifiers.
