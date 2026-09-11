#import "../lib.typ": definition, remark, assumption

The arithmetization framework of @sec:arithmetization is backend-independent by design, and the preceding sections have used the backend only through the abstract interface $V("vk", x, pi)$. For the soundness analysis, however, the backend cannot remain abstract: the binding of trace commitments, the soundness error of each proof, and the parameters that an external reviewer needs in order to evaluate the system (for instance, in the EF `soundcalc` tool @SOUNDCALC) all depend on it. This section fixes the backend that ZisK v0.16.1 actually uses and states its parameters. Nothing in the previous sections depends on these choices, so the reader interested only in the architecture may skip ahead.

== The STARK Backend <sec:stark-backend>

Every relation in this paper ---the AIR leaves $cal(R)_"AIR"^((tau))$ as well as the recursive relations $cal(R)_"LEAF"^((tau))$, $cal(R)_"AGG"$ and $cal(R)_"FINAL"$--- is proved with the same proving system: a univariate STARK following the DEEP-ALI paradigm @EPRINT:BBHR18 @EPRINT:StaWah23, with FRI @ICALP:BBHR18 as low-degree test and Merkle trees as vector commitments, made non-interactive with the BCS transform @TCC:BenChiSpo16. Concretely, for an AIR of width $W$, depth $D$ and trace height $N$ over the domain $L_0 = ⟨omega⟩ subset FF^times$ of size $N$:

+ *Trace commitment.* The witness columns of $bold(T)$ are interpolated to polynomials of degree $< N$, evaluated on a coset of a larger domain $L$ of size $N / rho$ (the _rate_ $rho = 2^(-k)$ is the inverse of the blowup factor), and committed by a Merkle tree whose leaves are the rows of the evaluation matrix. The tree hash is Poseidon2 over $FF$ with a $256$-bit digest (four field elements) @AFRICACRYPT:GraKhoSch23. The root of this tree is the _stage-1 commitment_; it is the object $"com"(pi)$ of @sec:recursion (see @sec:trace-commitment). Fixed columns are committed once at setup and their root is part of the verification key; cached columns (@sec:arithmetization) are committed once per program and their root is bound as described in @sec:vk-ledger.

+ *Auxiliary commitment.* After the verifier's challenges $alpha, gamma in KK$ are available, the prover commits (in a second Merkle tree) to the LogUp columns of @sec:logup-reduction: for each interaction the column of inverses $1 \/ (alpha + hat(e)(r))$ and the partial-sum column $S$. In ZisK, $alpha$ and $gamma$ are not sampled from the transcript of the individual proof but are the global challenge of @sec:challenge-derivation, supplied as a public input; this is a deviation from the plain STARK and is analysed in @sec:deviations.

+ *Constraint aggregation (ALI).* The verifier samples a challenge and the prover commits to the quotient polynomial of the random linear combination of all constraint polynomials, divided by the vanishing polynomial of $L_0$. The maximum constraint degree $d$ (three for the ZisK AIRs, up to eight for the recursion circuits) determines the number of quotient chunks.

+ *DEEP query and FRI.* The verifier samples an out-of-domain point $z in KK$; the prover sends the evaluations of all committed polynomials at $z$ (and at the shifted points $omega^k z$ for $k <= D$), and the two sides run FRI on the random linear combination of the DEEP quotients to certify that the committed evaluations are close to low-degree polynomials. FRI uses folding factors as listed in @tbl:backend-params, an early-stop degree, a number of query rounds $q$, and proof-of-work _grinding_ of $g$ bits before the query phase.

The extension field $KK = FF_(p^3)$ is used for every verifier challenge and every out-of-domain evaluation, so that the soundness error of each random-challenge step is of order $N / |KK| approx N dot 2^(-192)$.

#figure(
  table(
    stroke: 0.3pt,
    columns: (1.7fr, 0.55fr, 0.55fr, 0.7fr, 1.1fr, 1.4fr),
    align: (left, center, center, center, center, center),
    table.header([*Circuit family*], [*$log_2 N$*], [*rate $rho$*], [*queries $q$*], [*grinding $g$*], [*folding*]),
    [ZisK AIRs (Main, Mem, Rom, Binary, ...)], [$20$--$22$], [$1\/2$], [$229$--$232$], [$16$ ($20$ Rom, $23$ Keccakf)], [$[8, dots, 8]$ or $[8, dots, 8, 4]$],
    [Poseidon2 AIR], [$17$], [$1\/4$], [$114$], [$16$], [$[8,8,8,8,4]$],
    [Compressors], [$18$--$20$], [$1\/4$], [$110$], [$20$], [$[8,8,8,8,8]$ or $[8,8,8,8,8,4]$],
    [Aggregation verifier (`Recursive2`)], [$17$], [$1\/8$], [$73$], [$20$], [$[8,8,8,8,8]$],
    [Final verifier (`Final`)], [$16$], [$1\/32$], [$43$], [$22$], [$[16,16,16,16]$],
    [Final, compressed (`Final_Compressed`)], [$15$], [$1\/16$], [$54$], [$22$], [$[8,8,8]$],
  ),
  caption: [Backend parameters of ZisK v0.16.1 by circuit family, as registered in `soundcalc` @SOUNDCALC. All circuits use the Goldilocks field with cubic extension, Poseidon2 Merkle trees with $256$-bit digests, DEEP-ALI with powers-based batching, and univariate LogUp for every bus. Per-circuit values are listed in @tbl:soundcalc-mapping.],
  kind: table,
) <tbl:backend-params>

== Security Level and Soundness Regime <sec:security-level>

With the parameters of @tbl:backend-params, `soundcalc` reports for every circuit of ZisK v0.16.1 a soundness level of $128$ bits under the _Johnson-bound regime_ (JBR: list-decoding up to the Johnson radius, a proven regime for Reed--Solomon codes) and between $111$ and $113$ bits for the standard AIRs under the more conservative _unique-decoding regime_ (UDR), with the recursion circuits at $63$--$80$ bits in UDR owing to their lower rates @SOUNDCALC. ZisK therefore claims $128$-bit security _in the Johnson-bound regime_ and does not rely on capacity conjectures for FRI. In the soundness ledger of @sec:security we write $epsilon_"be"(N, rho, q, g)$ for the knowledge-soundness error of a single backend proof with these parameters; its concrete value is the per-circuit `soundcalc` figure.

#remark(title: "Proof sizes and the compressor layer")[
  The plain STARK proof of a large AIR is several megabytes (up to $21$ MiB for Keccakf). Verifying such a proof directly inside a leaf verifier would make the leaf verifier circuit itself large. ZisK therefore inserts, for the six largest AIR families, an intermediate _compressor_ circuit that verifies the STARK proof at rate $1\/2$ and re-proves it at rate $1\/4$ with far fewer queries; the leaf verifier then verifies the compressor proof instead. The compressor is a recursive verifier whose relation is "the AIR proof verifies and has the given public statement", so it is transparent to the relations of @sec:recursion; we include it in the topology of @sec:topology.
]

== Trace Commitments and the Function $"com"(pi)$ <sec:trace-commitment>

A proof $pi$ produced by the backend for an AIR of circuit type $tau$ is a sequence of Merkle roots (one per commitment stage), the out-of-domain evaluations, the FRI folding roots and final polynomial, the Merkle authentication paths for the queried rows, and the grinding nonce. The _trace commitment_ of $pi$ is
$
  "com"(pi) := ("root"_1 (pi), tau),
$
the stage-1 Merkle root together with the identifier of the AIR. Including $tau$ makes commitments of different AIR types distinct messages of the multiset hashed in @sec:challenge-derivation, so that two segment instances of different types cannot contribute the same element to the multiset; the leaf verifier for type $tau$ has $tau$ hard-coded, so this is not a prover choice. The AIR values $bold(a)$ and the public statement are not part of $"com"(pi)$: they are inputs to the verifier and enter the per-proof transcript directly.

Two properties of the trace commitment are used by the soundness sketch. The first is _binding_: the Merkle root of the stage-1 tree binds the prover to the evaluations of the committed columns on $L$, and by the low-degree test to a unique low-degree witness $bold(T)$ (except with the backend soundness error). The second is that the commitment is produced _before_ the global challenge $alpha$ is derived, so that the multiset $S$ of trace commitments hashed in @def:zisk-challenge is fixed before $alpha$ becomes available to any prover. Both properties are stated formally in @sec:security.

== Verification-Key and Cached-Column Ledger <sec:vk-ledger>

The recursion of @sec:recursion mentions several verification keys with different roles; the review of the W1 draft rightly asked for these to be separated. @tbl:vk-ledger lists them.

#figure(
  table(
    stroke: 0.3pt,
    columns: (0.9fr, 0.9fr, 3.2fr),
    align: (left, left, left),
    table.header([*Key*], [*Fixed at*], [*Role and how it is bound*]),
    [$"vk"_"AIR"^((tau))$, $tau in [M]$], [setup (per program for AIRs with cached columns)], [Verification key of the backend STARK for AIR $cal(A)_tau$: constraint description, fixed-column root, and stark parameters. Hard-coded into the leaf verifier circuit of type $tau$ (or into the compressor of type $tau$ where one exists). Selected by $tau$.],
    [$"vk"_"LEAF"^((tau))$, $tau in [M]$], [setup], [Verification key of the leaf verifier circuit of type $tau$. Hard-coded into the aggregation verifier circuit, which selects it by reading $tau$ from the child's recursive statement.],
    [$"vk"$ (propagated)], [setup, but not hard-coded in the aggregator], [The aggregation verifier's own verification key. It cannot be hard-coded into itself, so it is carried as a public through every node; each aggregator uses the value it received to verify aggregation children and passes the same value up.],
    [$"vk"^*$], [setup], [The actual aggregation verifier key, hard-coded into the Final Verifier, which binds the propagated $"vk"$ to it. This is the fixed parameter of $cal(R)_"FINAL"["vk"^*]$.],
    [$"vk"_"FINAL"$], [setup], [Verification key of the Final Verifier; held by the external verifier, together with $"vk"^*$, as the _verification context_ of ZisK for the given program.],
    [$"root"_"ROM"$], [per program], [Commitment to the program: the Merkle root of the cached columns of the ROM AIR, which hold the instruction table $P$ (@sec:program). It is bound into $"vk"_"AIR"^(("ROM"))$ and thereby into the whole key chain above, so $"vk"_"FINAL"$ identifies the program.],
    [$"root"_"cache"^((tau))$], [setup], [Roots of the fixed columns of table AIRs (arithmetic, binary, range, MemAlign, Keccak and SHA-256 tables). They are program-independent, computed deterministically from the table definition, and part of $"vk"_"AIR"^((tau))$.],
  ),
  caption: [Verification-key ledger. "Setup" means computed once for the ZisK release; "per program" means recomputed when the guest program changes. Every key is either hard-coded in a circuit above it or bound by the Final Verifier, so the external verifier's context $("vk"_"FINAL", "vk"^*)$ transitively fixes every key in the tree.],
  kind: table,
) <tbl:vk-ledger>

The distinction between $tau$ and $"vk"$ is thus the following. The circuit type $tau$ is _dispatch information_: it tells an aggregator which hard-coded child verifier to run, $V_"LEAF"^((tau))$ for $tau in [M]$ or $V_"AGG"$ for $tau = M+1$. The propagated $"vk"$ is _one specific key_, the aggregation verifier's own, which is the only key in the system that cannot be hard-coded where it is needed. In particular the propagated $"vk"$ is never the key selected by $tau$; when $tau in [M]$ the selected key is $"vk"_"LEAF"^((tau))$, which lives in the aggregator's constants.

For the cached and fixed columns the lifecycle is as follows. Fixed columns are defined by the AIR (they are part of its description) and their evaluations are committed at setup; their correctness is a property of the AIR definition, not of any proof. Cached columns are computed by the prover from the program binary once and committed; their root is bound into the program-specific verification key, and the setup procedure recomputes them deterministically from the binary so that the verifier can check the root against the program it intends to verify. Soundness of lookups against a cached table (e.g. the frequent-operation caches of @sec:freq-op-caches) therefore rests on two facts: that the root in the verification context is the root of the honestly computed table (a setup-time check), and that the STARK binds the prover to that root (backend binding). Both are entries of the proof-obligation ledger in @sec:proof-obligations.
