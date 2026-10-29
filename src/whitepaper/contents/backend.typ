#import "../../lib.typ": remark, verifier, vk

The arithmetization framework of @sec:arithmetization is backend-independent by design, and the preceding sections have used the backend only through the abstract interface $verifier(vk, x, pi)$. This section fixes the backend that ZisK actually uses ---the commitment scheme, the low-degree test, the transcript and all their parameters--- and maps every AIR of the recursion tree to the name under which it is registered in the Ethereum Foundation's `soundcalc` tool @SOUNDCALC, so that the soundness of each proof can be evaluated independently. The parameters below are those of the official ZisK setup.

== The STARK Backend <sec:stark>

Every AIR of ZisK ---the chips of @tbl:chip-inventory as well as the recursive verifiers of @sec:recursion --- is proved with the same proving system: a univariate STARK @EPRINT:BBHR18 following the DEEP-ALI paradigm, with FRI @ICALP:BBHR18 as low-degree test and Merkle trees as vector commitments, made non-interactive with the BCS transform @TCC:BenChiSpo16. All arithmetic is over the Goldilocks field $FF$, and every verifier challenge and out-of-domain evaluation lies in the cubic extension $KK$ of @sec:introduction. The exact protocol, as an interactive oracle proof and in its compiled form, and the analysis of its soundness are those of the security analysis @ZISK:RECURSION; here we summarise it. For an AIR of trace height $N$, a proof proceeds in five stages.

+ *Trace commitment.* The witness columns are interpolated over a multiplicative subgroup of $FF^times$ of size $N$, evaluated over a coset of a larger subgroup of size $N \/ rho$, where $rho$ is the _rate_ (the inverse of the _blowup factor_), and committed with a Merkle tree whose leaves are the rows of the evaluation matrix. The root of this tree is the _stage-1 commitment_ of the proof, which enters the challenge derivation of @sec:challenge-derivation. Fixed columns are committed once at setup, and the root of their tree is part of the AIR's verification key; the cached columns of the Rom AIR are committed once per program, and the root of their tree is the program commitment $"root"_"ROM"$ (@sec:rom-bus).
+ *Bus commitment.* With the key $chi = (alpha, gamma) in KK^2$ of the bus argument, the prover commits, in a second Merkle tree, to the LogUp columns of @sec:logup-reduction: one fraction column for each group of interactions, the groups being chosen at setup to keep the degree of the constraints bounded, and the running-sum column. In ZisK this key is not sampled from the proof's own transcript but derived from the global challenge of @sec:challenge-derivation, which every segment proof receives as a public input; the transcript of each AIR proof is seeded with it.
+ *Quotient.* The verifier samples a challenge, and the prover commits to the quotient of the random linear combination of all constraint polynomials (by powers of the challenge) by the vanishing polynomial of the trace domain. Intermediate columns keep the degree of each constraint below the bound allowed by the rate.
+ *DEEP evaluations.* The verifier samples an out-of-domain point $xi in KK$, and the prover sends the evaluations of all committed polynomials at $xi$ and at the shifted points required by the constraints.
+ *FRI.* The verifier samples two challenges with which the prover combines all committed polynomials into a single DEEP quotient, whose proximity to a low-degree polynomial is proved with FRI. FRI folds the evaluation domain by a factor of $8$ per round (a final round may fold by $4$), committing each folded layer with a Merkle tree, until the domain has $2^5$ or $2^6$ points, at which stage the remaining polynomial is sent in the clear. Before the query phase the prover must find a _grinding_ nonce: a value whose Poseidon2 hash together with the last challenge has $g$ leading zero bits, for a grinding parameter $g$. Finally, $q$ query positions are derived from the transcript, and the prover opens every committed tree at them.

*Merkle trees and transcript.* All Merkle trees and the Fiat–Shamir transcript use Poseidon2 @AFRICACRYPT:GraKhoSch23 over Goldilocks. Merkle trees have arity $4$ (Poseidon2 of width $16$), each row of a committed matrix is hashed into a leaf, and digests are $4$ field elements, i.e. about $256$ bits. To shorten proofs, Merkle authentication paths stop at a level close to the root ---one with $4$ or $16$ nodes for most AIRs--- and the proof carries that whole level. The transcript is a Poseidon2 sponge of width $16$. For the AIR proofs it is seeded with the global challenge, which already depends on the public statement and on every stage-1 commitment (@sec:challenge-derivation); for the recursive verifiers it is seeded with the verification key, the public inputs and the stage-1 commitment. It then absorbs every later commitment, the second-stage AIR values, the airgroup values and the evaluations before the corresponding challenges are squeezed.

== Parameters and Security Level <sec:backend-params>

Rates, query counts and grinding are chosen per AIR so that every proof reaches $128$ bits of security in the _Johnson-bound regime_ (JBR) for Reed–Solomon proximity, i.e. assuming FRI soundness up to the Johnson radius, which is a proven regime and does not rely on proximity-gap conjectures. Given the rate $rho$ and the grinding $g$, the number of queries is the smallest $q$ for which the query phase alone reaches $128$ bits. @tbl:backend-params lists the resulting parameters by family of AIRs.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (1.8fr, 0.55fr, 0.5fr, 0.65fr, 0.6fr, 1.1fr, 0.6fr),
      align: (left, center, center, center, center, center, center),
      table.header([*AIR*], [*$log_2 N$*], [*$rho$*], [*$q$*], [*$g$*], [*FRI folding*], [*$d$*]),
      [ZisK AIRs (except below)], [$18$--$22$], [$1\/2$], [$229$--$232$], [$16$], [$8$ ($4$ last)], [$3$],
      [Rom], [$22$], [$1\/2$], [$221$], [$20$], [$8$], [$2$],
      [Keccakf], [$17$], [$1\/2$], [$217$], [$23$], [$8$], [$3$],
      [Poseidon2], [$17$], [$1\/4$], [$114$], [$16$], [$8$ ($4$ last)], [$4$],
      [Compressors], [$18$--$20$], [$1\/4$], [$110$], [$20$], [$8$ ($4$ last)], [$5$],
      [Leaf and aggregation verifiers], [$17$], [$1\/8$], [$73$], [$20$], [$8$], [$8$],
      [Final Verifier], [$16$], [$1\/32$], [$43$], [$22$], [$16$], [$8$],
    )
  },
  caption: [Backend parameters of ZisK: trace height $N$ (per AIR in @tbl:chip-inventory), rate $rho$, number of FRI queries $q$, grinding bits $g$, FRI folding factor, and maximum constraint degree $d$. All AIRs use Goldilocks with its cubic extension, Poseidon2 Merkle trees of arity $4$ with $256$-bit digests, and LogUp for every bus.],
  kind: table,
) <tbl:backend-params>

With these parameters, `soundcalc` @SOUNDCALC reports $128$ bits of security in the Johnson-bound regime for every AIR of ZisK. Under the more conservative _unique-decoding regime_ (UDR), which only assumes FRI soundness up to half the minimum distance, it reports between $111$ and $113$ bits for the AIRs at rate $1\/2$, $93$ bits for Poseidon2, $94$ bits for the compressors, $80$ bits for the leaf and aggregation verifiers and $63$ bits for the Final Verifier. ZisK therefore claims $128$-bit security in the Johnson-bound regime.

#remark(title: "Proof Size and Compressors")[
  The high rate and large query count of the AIR proofs make them fast to produce but large, especially for the AIRs with the widest traces. The compressor nodes of @sec:recursion verify such a proof and re-prove its statement at rate $1\/4$ with $110$ queries, which is what keeps the leaf verifier within $2^(17)$ rows.
]

== Topology of All Proof-System Calls <sec:topology>

@tbl:topology lists every AIR for which a STARK proof is produced in a ZisK proof, its role in the aggregation tree of @sec:recursion, the relation it proves in the security analysis @ZISK:RECURSION, and the number of instances an execution produces. An execution with $L$ leaves has between $ceil((L - 1) \/ 2)$ and $L - 1$ aggregation verifiers, since each has two or three non-null children; with a single leaf it has none, and the Final Verifier verifies the leaf verifier directly. All auxiliary arguments ---memory, lookups, permutations, range checks and continuations--- are realised as bus interactions inside the AIR leaves (@sec:bus-system), not as separate proof-system invocations.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (0.9fr, 1.6fr, 0.8fr, 1.2fr),
      align: (left, left, left, left),
      table.header([*Node*], [*AIR*], [*Relation*], [*Instances*]),
      [AIR leaf],
      [each of the $35$ AIRs of @tbl:chip-inventory],
      [$cal(R)_"AIR"^((tau))$],
      [one per segment of the AIR (@def:segmentation)],

      [compressor],
      [Keccakf, Sha256f, Blake2br, ArithEq, ArithEq384, DmaPrePost],
      [compressor relation of $Pi_"AIR"^((tau))$],
      [one per leaf of these AIRs],

      [leaf verifier],
      [one per AIR],
      [$cal(R)_"LEAF"^((tau))$],
      [one per leaf],

      [aggregation verifier], [one], [$cal(R)_"AGG"$], [between $ceil((L - 1) \/ 2)$ and $L - 1$],
      [Final Verifier], [one], [$cal(R)_"FINAL"$], [$1$],
    )
  },
  caption: [Topology of all proof-system calls in ZisK, for an execution with $L$ leaves. The relations are those of the security analysis @ZISK:RECURSION.],
  kind: table,
) <tbl:topology>

Every AIR of @tbl:topology is registered in `soundcalc` @SOUNDCALC: each AIR under its own name (e.g. `Main`, `Mem`, `Keccakf`), each compressor as `<AIR>-compressor` (e.g. `Keccakf-compressor`), the aggregation verifier as `Recursive2`, and the Final Verifier as `Final`.

The leaf verifiers of all AIRs share the STARK parameters and constraint system of the aggregation verifier and differ from it only in their fixed columns, which hard-code the key of the AIR they verify; the `soundcalc` entry `Recursive2` therefore covers both kinds of node. Finally, the Final Verifier's proof can be wrapped into a pairing-based SNARK over BN254 for cheap on-chain verification; this wrapping step is outside the scope of this document and of `soundcalc`.
