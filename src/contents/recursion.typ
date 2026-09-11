#import "../lib.typ": definition, remark, assumption, lemma
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

ZisK instantiates this scheme with _LtHash_ @ZISK:LTHASH, a lattice-based multiset hash. The group is $cal(G)$ is the vector space $ZZ_p^n$, and the inner hash $h : FF^k -> ZZ_p^n$ is realised by hashing a commitment $"com"$ to a single field element $c = H("com")$ via Poseidon2 @AFRICACRYPT:GraKhoSch23, then iteratively expanding $c$ into a long pseudorandom vector $h("com") in ZZ_p^n$. Multiset collision-resistance for LtHash reduces to the Short Integer Solution (SIS) @STOC:Ajtai96 lattice problem, which is believed to remain hard even against quantum adversaries. ZisK targets $128$-bit security with concrete parameters $n = 372$ and cardinality bound $B = 2^(20)$ (introduced below). A formal statement of the binding property assumed of $cal(H)$, with these parameters, is given in @sec:challenge-derivation-formal.

The LtHash group has finite exponent $p$: adding $p$ copies of the same element to a multiset leaves $H$ unchanged, since $p dot h(x) equiv 0 in ZZ_p^n$. To rule out such trivial collisions, the scheme is restricted to multisets of cardinality at most $B << p$. ZisK enforces this bound by tracking the multiset cardinality alongside the accumulator, via the leaf-count counter $kappa$ that the recursion carries and range-checks against $B$ at every aggregation node (introduced in the next section). Throughout, $B$ denotes the bound itself (so the check reads $kappa < B = 2^(20)$), never an exponent. Equivalently, one may think of LtHash as using an augmented per-element hash $h'(x) = (h(x), 1) in ZZ_p^(n+1)$, so that the last coordinate of the multiset hash tracks the total cardinality automatically.

Correctness of the assumed challenge $alpha$ must be verified ---otherwise a malicious prover could substitute any $alpha$ to make the partial sums balance artificially. Since $cal(H)$ is homomorphic over multiset union, this verification is embedded directly into the aggregation tree: each node carries a _partial accumulator_ over the commitments in its subtree, and a parent node combines the two by addition. At the root, the fully accumulated value is checked against the claimed $alpha$, confirming that it was correctly derived from the entire set of commitments.

=== Formal Specification of the Challenge Derivation <sec:challenge-derivation-formal>

The preceding discussion interleaves the specification with its motivation. We now separate the two and state the challenge derivation as a self-contained primitive with an explicit security requirement, so that the soundness sketch of @sec:security can consume it as a named assumption rather than as prose.

#definition(title: "Multiset Hash and Multiset Binding")[
  Let $cal(M)$ be a message space, $(cal(G), +)$ a finite abelian group, and $B in NN$ a _cardinality bound_. A _multiset hash_ is a function $cal(H)$ from finite multisets over $cal(M)$ to $cal(G)$ that is _homomorphic_: $cal(H)(S union T) = cal(H)(S) + cal(H)(T)$ for all multisets $S, T$, where $union$ is multiset union (multiplicities add). The multiset hash is _$(B, epsilon_"ms")$-binding_ if for every probabilistic polynomial-time adversary $cal(A)$,
  $
    Pr[ (S, T) arrow.l cal(A)(1^lambda) : S != T and |S| <= B and |T| <= B and cal(H)(S) = cal(H)(T) ] <= epsilon_"ms" (lambda),
  $
  where $|S|$ denotes the cardinality of $S$ counted with multiplicity.
] <def:multiset-binding>

#definition(title: "ZisK Challenge Derivation")[
  Let $h : cal(M) -> ZZ_p^n$ be the inner hash-to-group function of @sec:challenge-derivation, and let $cal(H)(S) := sum_(x in S) m_S (x) dot h(x)$ be the induced multiset hash with values in $cal(G) = ZZ_p^n$. Let $"DeriveAlpha" : FF^* times ZZ_p^n -> KK$ be the deterministic projection realised by Poseidon2. Given the public statement $bold(p)$ and a multiset $S$ of trace commitments, the _ZisK challenge_ is
  $
    alpha(bold(p), S) := "DeriveAlpha"(bold(p), cal(H)(S)) := "Poseidon2"("Trans"(bold(p)) || cal(H)(S)), quad gamma := H_gamma (alpha),
  $
  where $"Trans"(bold(p))$ is the canonical transcript encoding of the public statement (the program commitment, the public outputs, and the proof-level selector values of @sec:public-ledger) and $H_gamma : KK -> KK$ is the fixed hash deriving the compression challenge from $alpha$ (@sec:logup-reduction). Including $bold(p)$ in the derivation binds the challenge to the statement as well as to the commitments. The concrete parameters are $p = 2^64 - 2^32 + 1$, $n = 372$, and $B = 2^(20)$.
] <def:zisk-challenge>

The two properties that the recursion relies on are, respectively, the homomorphism (which is what allows $bold(c)$ to be accumulated by addition at every internal node) and the following assumption.

#assumption(title: "LtHash Binding")[
  The multiset hash $cal(H)$ of @def:zisk-challenge is $(B, epsilon_"ms")$-binding in the sense of @def:multiset-binding, with $epsilon_"ms" (lambda) <= 2^(-128)$ for the stated parameters, under the hardness of the Short Integer Solution problem for the corresponding lattice parameters @ZISK:LTHASH.
] <asm:lthash>

The role of the cardinality bound is the one described earlier: without it, any multiset containing $p$ copies of an element collides with the same multiset with those copies removed, since $cal(G)$ has exponent $p$. The recursion enforces $|S| <= B$ by construction ---$kappa$ counts the leaves under each node and the checks $kappa < B$ in $cal(R)_"AGG"$ and $cal(R)_"FINAL"$ ensure that the multiset whose hash is compared against $alpha$ at the root has at most $B$ elements--- so @asm:lthash applies to it.

Finally, the challenge $alpha$ is a Fiat-Shamir challenge: it is a deterministic function of the prover's first-round messages (the trace commitments). The standard way to argue about it is to model $"DeriveAlpha"(bold(p), cal(H)(dot))$ as a random oracle on pairs (statement, multiset of commitments), which is legitimate if $cal(H)$ is binding and $"DeriveAlpha"$ is modelled as a random oracle: a binding $cal(H)$ means distinct multisets of size at most $B$ map to distinct accumulators except with probability $epsilon_"ms"$, after which a random-oracle $"DeriveAlpha"$ yields independent uniform challenges for distinct (statement, multiset) pairs. This is the form in which @sec:security uses it.

== What ZisK Proves <sec:zisk-statement>

Before describing the recursive verifiers, we make explicit what ZisK as a whole proves. Given a fixed program $P$, ZisK proves that there exists a valid execution of $P$ on some input producing some output. Some elements of this relation ---typically a subset of the program's inputs and a subset of its outputs--- can be exposed to the verifier as publics; we collect all such public elements into a single vector $bold(p) in FF^k$, the _public statement_. Everything else (the prover's hints, intermediate memory state, and any non-public output) stays inside the prover.

The execution is split into segments and proved piecewise: given ZisK's circuit $cal(C) = {(cal(A)_i, cal(I)_i)}_(i=1)^M$, each segment is an instance of one of the AIRs $(cal(A)_i, cal(I)_i) in cal(C)$ (@def:segment). The segments are stitched together by the global bus-balancing condition (@def:bus-balancing) and the global challenge $alpha in KK$, derived from the prover's commitments via Fiat-Shamir as described in @sec:challenge-derivation.

The relations in the rest of this section describe what each recursive verifier checks; they are statements about proof acceptance and bus arithmetic. The formal statement about program semantics ---the relation $cal(R)_"exec"$ whose witness is an execution of $P$, the ledger of the public statement $bold(p)$, and the knowledge-soundness theorem that connects an accepting final proof to a witness of $cal(R)_"exec"$--- is given separately in @sec:statement, and the reduction from the relations below to $cal(R)_"exec"$ is sketched in @sec:security.

== Recursive Structure

Throughout this section it will be convenient to describe a verifier by the _relation_ it attests to. We write a relation as
$
  cal(R) = { (x\; w) mid(|) phi(x, w) },
$
where $x$ is the _public statement_ and $w$ is the _witness_; the predicate $phi$ specifies the constraints that must hold. A proof for $cal(R)$ on a given $x$ convinces the verifier that there exists $w$ such that $(x\; w) in cal(R)$.

ZisK assembles its proof as the aggregation tree illustrated in @fig:aggregation-tree. The leaves of the tree are the individual AIR segment instances; the internal nodes are _recursive verifiers_ ---arithmetic circuits that take their children's proofs as witness, verifies them, and expose a small number of public outputs that propagate upward. Internal nodes have a fixed arity, but the tree is not required to be balanced: it is built opportunistically as proofs complete, so a branch that finishes early can be verified immediately while others are still running. On top of the aggregation tree sits a single _Final Verifier_, which is the only node that performs the global checks ---bus balancing across all segments, and consistency of the global challenge $alpha$.

Two quantities are accumulated upward at every internal node: the bus partial sum $s$ and the challenge contributions $bold(c)$. These accumulations are the mechanism by which the two global checks are reduced, at the Final Verifier, to simple arithmetic on the public outputs that arrive there.

The challenge $alpha$ is an input to the entire structure, not something derived inside it. Before proving starts, $alpha$ is derived according to @sec:challenge-derivation and broadcast to every leaf prover. Each leaf proof takes $alpha$ as a public input and uses it to compute its partial bus sum $s$. The verifiers then accumulate both $s$ and the challenge contributions $bold(c)$ upward, and the Final Verifier receives $alpha$ as a public input to check that it matches what the tree actually accumulated.

The tree has four kinds of nodes: AIR leaves, leaf verifiers, aggregation verifiers, and the Final Verifier. For the six AIR types whose STARK proofs are largest (@sec:security-level), a _compressor_ node sits between the AIR leaf and its leaf verifier: it is a recursive verifier for the relation "the AIR proof verifies with this public statement", re-proved at a higher rate so that the leaf verifier circuit stays small. Since a compressor changes neither the statement nor the witness semantics, we fold it into the leaf verifier in the relations below and list it separately only in the topology (@sec:topology).

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

The challenge contribution is computed from the _trace commitment_ carried inside the AIR proof. We write $"com"(pi)$ for the commitment component of an AIR proof $pi$: the backend of @sec:backend produces, as the first message of every proof, a Merkle root binding the committed trace columns of $(bold(T), bold(a))$, and $"com"(pi)$ denotes exactly that root together with the identifier of the AIR the proof is for (@sec:trace-commitment gives the precise contents). The function $"com"(dot)$ is a fixed, public parsing of the proof string; it involves no secret and no choice by the prover beyond the proof itself, so it is a legitimate helper function inside a relation whose witness is $pi$.

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
        and quad quad quad bold(c) = h("com"(pi)),
        and quad quad quad quad kappa = 1
      )
    }
  )
$
where $V_"AIR"^((tau))$ is the verifier induced by $cal(R)_"AIR"^((tau))$. The bus contribution $s$ is checked by $V_"AIR"^((tau))$, so accepting the AIR proof binds it to the value committed in $pi$, which the leaf verifier then forwards unchanged into its public statement. The challenge contribution $bold(c)$, on the other hand, is computed by the leaf verifier itself, since $h$ only depends on the trace commitment $"com"(pi)$, which is a field of $pi$ that the leaf verifier parses directly. The remaining components are constants associated with this leaf verifier: $tau$ is fixed by the choice of $V_"AIR"^((tau))$, and $kappa = 1$ marks "this subtree contains one leaf". Finally, $"vk"$ is carried as a public but unused at this level. Every symbol in the displayed relation is thus bound: $bold(p), alpha, sigma, "vk"$ by the public statement, $pi$ by the witness, $tau$ and the constant $1$ by the choice of leaf-verifier circuit, and $V_"AIR"^((tau)), h, "com"$ are fixed public functions.

=== Aggregation Verifier

An _aggregation verifier_ has a fixed arity $k$ ---$k = 3$ in ZisK v0.16.1--- and takes the proofs $pi_1, dots, pi_k$ produced by its children as witness, runs the recursive verifier on each of them, and accumulates the bus partial sums $s_i$ and the challenge contributions $bold(c)_i$ upward. When fewer than $k$ proofs are available, the remaining child slots are _null_: a null child is marked by the reserved circuit type $tau = 0$, is not verified, and contributes $s = 0$, $bold(c) = bold(0)$, $kappa = 0$. The contribution $bold(c) = sum_i bold(c)_i$ is exactly the multiset-homomorphism step of the multiset hash $cal(H)$: under the leaf-element interpretation given above, summing the children's $bold(c)$'s computes $cal(H)$ on the union of the subtrees' multisets. The accumulated $(s, bold(c))$ propagate up the tree until the root.

Each non-null child of an aggregation verifier is itself either a leaf verifier or another aggregation verifier. The aggregation verifier therefore reads each child's circuit type $tau$ and selects the appropriate verifier accordingly: the per-AIR verifier $V_"LEAF"^((tau))$ when $tau in [M]$, the aggregation verifier $V_"AGG"$ when $tau = M + 1$, and no verifier at all when $tau = 0$. We denote this selection by $V_"REC"^((tau))$, with the convention that $V_"REC"^((0))$ accepts exactly the null statement $sigma = (0, 0, 0, bold(0))$. The aggregation verifier exposes its own circuit type $tau = M + 1$ in its public statement to mark the resulting proof as "aggregated", so the level above dispatches to $V_"AGG"$ when verifying it. The circuit type is thus _dispatch information determined by the child's provenance_: a leaf verifier of type $tau$ hard-codes $tau$ into its public statement, an aggregation verifier hard-codes $M + 1$, and neither is a free choice of the prover. The parent enforces the consequence: whatever $tau$ a child declares, the parent runs the verifier with the verification key _for that $tau$_, so a proof produced for one circuit type cannot be passed off as another.

Dispatching also requires the aggregation verifier to know the verification key of whichever inner verifier it ends up running. The keys $"vk"_("LEAF")^((1)), dots, "vk"_("LEAF")^((M))$ of the per-circuit-type leaf verifiers are fixed at setup time and are hard-coded into the aggregation circuit. The aggregation verifier's _own_ key is exactly the public $"vk"$ introduced above: this is the value that lets the aggregator verify aggregation children. The aggregator additionally binds each of its children to declare the same value of $"vk"$ as itself, so the same value propagates uniformly through the entire tree.

A proof for an aggregation verifier attests that:
- Each child proof $pi_i$ verifies under the verifier selected by its circuit type $tau_i in {0} union [M+1]$ and under its public statement.
- The partial bus sum $s$ is the sum of the children's partial sums, $s = sum_i s_i$.
- The challenge contribution $bold(c)$ is the sum of the children's contributions, $bold(c) = sum_i bold(c)_i$.
- The leaf-count counter $kappa$ is the sum of the children's counters, $kappa = sum_i kappa_i$, and both every child counter and every running partial sum of the addition are range-checked against $B = 2^(20)$ (@sec:challenge-derivation); the checks are performed in the circuit by a $20$-bit decomposition. Checking the sum after every addition is what makes the bound hold at the root, where $kappa$ equals the total number of leaves in the tree.
- Both children declare the same $"vk"$ as the parent.
- The exposed circuit type is the aggregation marker $tau = M + 1$.

Formally:
$
  cal(R)_"AGG" = lr(
    {
      cases(
        delim: #none,
        ,
        (bold(p), alpha, sigma, "vk")\; ((sigma_i, pi_i))_(i in [k]),
        ,
      )
      mid(|)
      cases(
        delim: #none,
        gap: #(0pt + 0.4em),
        forall i in [k] : V_"REC"^((tau_i))((bold(p), alpha, sigma_i, "vk"), pi_i) = "accept",
        and quad quad quad quad tau = M + 1,
        and quad kappa = sum_i kappa_i and forall i : kappa_i < B and sum_(i' <= i) kappa_(i') < B,
        and quad quad quad quad s = sum_i s_i,
        and quad quad quad quad bold(c) = sum_i bold(c)_i,
      )
    }
  )
$
where $V_"REC"^((tau)) = V_"LEAF"^((tau))$ if $tau in [M]$, $V_"REC"^((tau)) = V_"AGG"$ if $tau = M + 1$, and $V_"REC"^((0))$ accepts only the null statement. Each $V_"REC"^((tau))$ is invoked with $"vk"$ in the child's public statement, so by accepting that proof the aggregator implicitly checks that the child declared the same $"vk"$ as itself. The verification keys used by $V_"LEAF"^((1)), dots, V_"LEAF"^((M))$ are constants of the aggregation circuit; the key used by $V_"AGG"$ is the public $"vk"$ (@sec:vk-ledger).

#remark(title: "Worked example of dispatch")[
  Consider a Main leaf and a Keccakf leaf feeding one aggregation node, with the third slot null. The Main leaf verifier is the circuit of type $tau = 1$; it verifies the Main AIR proof with the hard-coded key $"vk"_"AIR"^((1))$, hashes the proof's trace commitment into $bold(c)_1$, and outputs $sigma_1 = (s_1, 1, 1, bold(c)_1)$. The Keccakf leaf verifier (type $tau = 15$, say) does the same with $"vk"_"AIR"^((15))$ and outputs $sigma_2 = (s_2, 15, 1, bold(c)_2)$. The aggregation node reads $tau_1 = 1$ and $tau_2 = 15$ from the children's statements, verifies $pi_1$ with the constant $"vk"_"LEAF"^((1))$ and $pi_2$ with the constant $"vk"_"LEAF"^((15))$, checks that both children carry the same $"vk"$ as its own public, treats the third child as null, and outputs $sigma = (s_1 + s_2, M + 1, 2, bold(c)_1 + bold(c)_2)$. A prover cannot present the Keccakf proof as a Main proof: the leaf verifier that produced $sigma_2$ hard-codes $tau = 15$, and if the prover instead ran the type-$1$ leaf verifier on the Keccakf proof, $V_"AIR"^((1))$ would reject it, since the two AIRs have different verification keys.
]

=== Final Verifier

The _Final Verifier_ sits above the aggregation tree. It takes the topmost aggregation proof produced by the tree as its single child, runs the aggregation verifier $V_"AGG"$ on it, and additionally enforces the two global checks. Because the topmost node of the aggregation tree is always an aggregation verifier, the Final expects its child to advertise $tau = M + 1$; this saves the Final from having to dispatch over circuit types as the internal aggregators do. The Final also closes the recursion loop on $"vk"$: it carries a _fixed parameter_ $"vk"^*$ ---a hard-coded constant, the actual aggregation verifier's verification key fixed at setup time--- and binds the child's declared $"vk"$ to that constant. Since $"vk"^*$ is neither part of the public statement nor of the witness, we write it as a parameter of the relation, $cal(R)_"FINAL"["vk"^*]$; the external verifier knows $"vk"^*$ as part of the ZisK verification context (@sec:vk-ledger). After this point $s$, $bold(c)$, $tau$, and $kappa$ have served their purpose and are no longer carried forward: they are absorbed into the global checks below, and only the program-level public statement $bold(p)$ remains visible to an external verifier.

A proof for the Final Verifier attests that:
- The child's circuit type is $tau = M + 1$, i.e., the child is an aggregation proof.
- The child aggregation proof $pi$ verifies under the public statement $(bold(p), alpha, sigma, "vk"^*)$; since the child's $"vk"$ is a public of the child, running $V_"AGG"$ with $"vk"^*$ in that position is what binds the child's declared key to the Final's hard-coded constant.
- The leaf-count counter $kappa$ is less than $B$, confirming that the multiset of commitments aggregated under the child satisfies the cardinality bound required by $cal(H)$ (see @sec:challenge-derivation).
- Bus balancing holds globally: $s = 0$.
- The challenge $alpha$ was honestly derived from the public statement and the full set of commitments: $alpha = "DeriveAlpha"(bold(p), bold(c))$, the deterministic projection of @def:zisk-challenge applied to the accumulated $bold(c)$.

Formally, the Final Verifier attests to the relation:
$
  cal(R)_"FINAL"["vk"^*] = lr(
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
        V_"AGG" ((bold(p), alpha, sigma, "vk"^*), pi) = "accept",
        quad quad quad quad quad and kappa < B,
        quad quad quad quad quad and s = 0,
        quad and alpha = "DeriveAlpha"(bold(p), bold(c)),
      )
    }
  )
$

#remark[
  In the degenerate case of an execution that fits in a single segment, the aggregation tree is empty: there is nothing to aggregate. The Final Verifier then takes the leaf verifier's proof directly as its child, dispatching to $V_"LEAF"^((tau))$ in exactly the same way as an aggregation verifier would. The relation $cal(R)_"FINAL"$ above generalises to this case by replacing $V_"AGG"$ with $V_"LEAF"^((tau))$ and accepting any $tau in [M]$; everything else stays the same.
]

The two equality checks have direct global meaning. The first, $s = 0$, is the global bus-balancing condition from @def:bus-balancing ---every message sent on every bus across every segment has been received exactly once with matching values. The second, $alpha = "DeriveAlpha"(bold(p), bold(c))$, is _challenge correctness_: by the multiset homomorphism of $cal(H)$, the value of $bold(c)$ at the top of the tree equals $sum_i h("com"(pi_i)) = cal(H)(S)$ over the multiset $S$ of segment trace commitments, so this check confirms that $alpha$ was honestly derived from the statement and the full set of commitments and not chosen adversarially. Both checks are _commit-then-justify_ patterns: every leaf uses $alpha$ before the multiset it is derived from has been assembled, and every aggregator uses $"vk"$ before the Final fixes it. Their soundness rests on the two root checks being enforced on the very values that propagated up the tree, which is argued in @sec:security.

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
        )[*Final Verifier* #linebreak() #sub[$V(pi) = "accept"$] #linebreak() #sub[$s = 0$] #linebreak() #sub[$alpha = "DeriveAlpha"(bold(p), bold(c))$]],
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
    Example aggregation tree (drawn with two children per node for readability; ZisK's aggregation verifier has arity $3$, unused slots being null children). The tree is unbalanced. Dashed arrows carry the program-level challenge $alpha$ down to the leaves. Solid arrows carry inputs and outputs to each level: each node's outgoing label is its output, and the incoming labels at any node are its inputs.
  ],
) <fig:aggregation-tree>
