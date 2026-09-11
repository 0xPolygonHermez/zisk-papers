#import "../lib.typ": definition, remark, assumption, lemma, theorem, proposition

This section collects the material that a W3 soundness proof of @thm:target will be built from: the topology of every proof-system call, a vanilla baseline against which ZisK's design choices are recorded as deviations, the explicit assumption about the transpiler, the lemma chain from an accepting final proof down to a witness of $cal(R)_"exec"$, and the ledger of proof obligations that remain. Following the EF W2 guidance @EF:ZKVMREQ, nothing here is a complete proof; every step is stated precisely enough that what remains to be proved is visible.

== Topology of All Proof-System Calls <sec:topology>

@tbl:soundcalc-mapping lists every circuit for which a STARK proof is produced, its role in the aggregation tree of @sec:recursion, the relation it proves, how many instances of it an execution produces, and the name under which it is registered in the EF `soundcalc` tool @SOUNDCALC. All circuits are proved with the backend of @sec:backend; their parameters are in @tbl:backend-params.

#figure(
  {
    set text(size: 8pt)
    table(
      stroke: 0.3pt,
      columns: (0.8fr, 1.5fr, 0.9fr, 0.75fr, 1.75fr),
      align: (left, left, left, center, left),
      table.header([*Node kind*], [*Circuit*], [*Relation*], [*Instances*], [*`soundcalc` name*]),
      [AIR leaf], [Main], [$cal(R)_"AIR"^(("Main"))$], [$ceil(T \/ 2^(22))$], [`Main`],
      [AIR leaf], [Rom], [$cal(R)_"AIR"^(("Rom"))$], [1], [`Rom`],
      [AIR leaf], [Mem, RomData, InputData], [$cal(R)_"AIR"^((tau))$], [per region workload], [`Mem`, `RomData`, `InputData`],
      [AIR leaf], [MemAlign, MemAlignByte, MemAlignReadByte, MemAlignWriteByte], [$cal(R)_"AIR"^((tau))$], [workload], [same names],
      [AIR leaf], [Arith, Binary, BinaryAdd, BinaryExtension], [$cal(R)_"AIR"^((tau))$], [workload], [same names],
      [AIR leaf], [Add256, ArithEq, ArithEq384, Keccakf, Sha256f, Poseidon2, Blake2br], [$cal(R)_"AIR"^((tau))$], [workload], [same names],
      [AIR leaf], [the 12 DMA AIRs], [$cal(R)_"AIR"^((tau))$], [workload], [`Dma`, `DmaMemCpy`, `DmaInputCpy`, `Dma64Aligned`, `Dma64AlignedInputCpy`, `Dma64AlignedMemSet`, `Dma64AlignedMem`, `Dma64AlignedMemCpy`, `DmaUnaligned`, `DmaPrePost`, `DmaPrePostMemCpy`, `DmaPrePostInputCpy`],
      [AIR leaf (table)], [SpecifiedRanges, VirtualTable0, VirtualTable1], [$cal(R)_"AIR"^((tau))$], [1 each], [`SpecifiedRanges`, `VirtualTable0`, `VirtualTable1`],
      [compressor], [one per large AIR type], ["$V_"AIR"^((tau))$ accepts"], [one per such leaf], [`DmaPrePost-compressor`, `ArithEq-compressor`, `ArithEq384-compressor`, `Keccakf-compressor`, `Sha256f-compressor`, `Blake2br-compressor`],
      [leaf verifier], [one per AIR type (35)], [$cal(R)_"LEAF"^((tau))$], [one per leaf], [not registered separately (see remark)],
      [aggregation verifier], [Recursive2], [$cal(R)_"AGG"$], [$approx$ (leaves $- 1$) / 2], [`Recursive2`],
      [Final Verifier], [Final], [$cal(R)_"FINAL"["vk"^*]$], [1], [`Final`],
      [Final, compressed], [Final_Compressed], ["$V_"FINAL"$ accepts"], [0 or 1], [`Final_Compressed`],
    )
  },
  caption: [Topology of all proof-system calls in ZisK v0.16.1 and mapping to `soundcalc` circuit names. The 35 AIR leaves are the circuit $cal(C)$ of @tbl:chip-inventory. An execution that fits in a single leaf uses the degenerate tree of @sec:recursion (the Final verifies the leaf verifier directly). The optional compressed Final is a one-to-one re-proof of the Final at a smaller size; the optional wrap into a pairing-based SNARK for on-chain verification is outside the scope of this document.],
  kind: table,
) <tbl:soundcalc-mapping>

#remark(title: "Leaf verifiers in soundcalc")[
  The `soundcalc` export produced from the ZisK proving key registers the AIRs, the compressors, the aggregation verifier and the two Final circuits, but not the per-type leaf verifier circuits. Their parameters are those of the aggregation verifier family (rate $1\/8$, $73$ queries, $20$ grinding bits), so the security level reported for `Recursive2` applies to them; making them explicit entries is a pending item of the `soundcalc` integration.
]

Every auxiliary argument ---memory, lookup, permutation, range check, continuation--- is realised _inside_ the AIR leaves as bus interactions and not as a separate proof-system invocation. Their public interface between proof instances is therefore uniform: every leaf exposes exactly its bus contribution $s in KK$ and its trace commitment (through $bold(c)$), and the global relation that ties the instances together is $cal(R)_"BUS"^(alpha)$ of @def:global-bus-relation, checked as $s = 0$ at the Final. The semantic relation each bus enforces is given in @sec:bus-system and @sec:continuation-bus.

== Vanilla Baseline and Deviation Ledger <sec:deviations>

We adopt the baseline-and-deviation strategy of the W2 requirements @EF:ZKVMREQ. The _vanilla construction_ we compare against is the following: a single monolithic AIR whose trace is the whole execution, proved by a plain DEEP-ALI STARK with FRI; memory checked by a sorted-permutation argument inside that AIR with Merkle-committed memory at segment boundaries; all lookups and permutations realised by LogUp with independent verifier challenges $alpha, gamma$ sampled per proof; fixed segmentation of the execution into whole-VM-state checkpoints proved separately and stitched by equality of boundary states; and binary aggregation of proofs by a recursive verifier that hard-codes every verification key. This is essentially the reference vanilla zkVM of the EF sprint and its security argument (correct-trace extractability by descending the recursion tree) is the one we intend to adapt. @tbl:deviations lists every proof-system-level difference between the vanilla construction and ZisK, with the layer it affects and the argument by which soundness is preserved.

#figure(
  {
    set text(size: 8pt)
    table(
      stroke: 0.3pt,
      columns: (1.5fr, 0.6fr, 2.7fr, 0.6fr),
      align: (left, left, left, left),
      table.header([*Deviation*], [*Layer*], [*Why soundness is preserved (sketch)*], [*Interacts with*]),
      [D1. Per-chip trace splitting instead of whole-VM segmentation (@sec:segment-objects)], [segmentation], [No whole-state equality is available; instead the Main's boundary state is a typed payload on a continuation bus and the memory is checked _globally_ by one sorted trace spanning all segments. Soundness reduces to @lem:stitching for the Main and to @lem:memory-argument for memory.], [D2, D4],
      [D2. LogUp bus balancing across independently proved AIRs, checked only at the root (@def:global-bus-relation)], [PIOP / recursion], [Each leaf's partial sum is a public output bound by its own STARK; the root check $s = 0$ is the LogUp identity for the union of all interactions. Soundness is the LogUp bound at a random $alpha$; the challenge must be common to all leaves, which is D3.], [D3, D6],
      [D3. Global challenge from an LtHash multiset hash of all trace commitments, supplied to leaves as a public input and justified at the root (@def:zisk-challenge)], [transcript / recursion], [Commit-then-justify: leaves use $alpha$ before it is justified, but every leaf's commitment enters the multiset whose hash the Final recomputes. Changing any commitment changes $cal(H)(S)$ except with $epsilon_"ms"$, hence $alpha$, hence invalidates the leaf. Requires @asm:lthash and the random-oracle modelling of $"DeriveAlpha"$.], [D2, D8],
      [D4. Compression challenge $gamma$ derived from $alpha$ instead of sampled independently], [PIOP], [$gamma = H_gamma (alpha)$ with $H_gamma$ a random oracle is a fresh random value given $alpha$; the LogUp collision bound applies with $(alpha, gamma)$ modelled as a random pair determined by the transcript.], [D2],
      [D5. Circuit-type dispatch $tau$ and propagated $"vk"$ (@sec:vk-ledger)], [recursion], [$tau$ is hard-coded by the circuit that produced the proof and selects a hard-coded key in the parent; $"vk"$ propagates unchanged and is fixed at the root. An accepting aggregation with a wrong $"vk"$ at any node would require an accepting Final with a child declaring $"vk" != "vk"^*$, which the Final rejects.], [D3],
      [D6. Registers handled by a linked-step argument in Main instead of the sorted memory (@sec:registers)], [AIR / bus], [Timestamp-linked chain with exact multiset matching on the Memory Bus is a standard alternative memory-checking argument; per-register chain is opened once globally and reloaded at every segment boundary. Register refinement obligation in @sec:proof-obligations.], [D1],
      [D7. MemAlign decomposition of sub-word accesses into aligned ones (@sec:memalign-refinement)], [AIR / bus], [Fixed micro-program table; write-back stamped in the following slot preserves order. @lem:memalign-refinement.], [D6],
      [D8. Precompiles access memory directly, ordered by the dispatching step (@sec:operation-bus)], [AIR / bus], [The Main places its step $t$ on the Operation Bus; the precompile stamps its accesses with slots $2, 3$ of $t$, so the memory argument orders them exactly where the ISA semantics places the precompile's effect.], [D1, D6],
      [D9. Table buses with fixed tables, frequent-operation caches and packed virtual tables (@sec:table-buses)], [AIR / setup], [Lookup soundness plus binding of the fixed-column roots in the verification keys. Cache correctness is a setup-time property (@sec:vk-ledger).], [---],
      [D10. Two-limb encoding of 64-bit words over Goldilocks (@sec:word-encoding)], [AIR], [Injective encoding on range-constrained limbs; overflow handled by explicit carries. Obligation: every consumed limb is range-constrained.], [D6, D7],
      [D11. Trace splitting claimed equivalent to a jagged commitment], [PIOP], [Not a soundness claim: it is a statement about prover cost. No soundness argument depends on it.], [---],
      [D12. Fixed arity-3 aggregation with null children, unbalanced tree, per-node $kappa$ range checks], [recursion], [Null children contribute the neutral element to every accumulator and are not verified; the $kappa$ checks bound the multiset size for @asm:lthash.], [D3],
      [D13. Compressor nodes for large AIRs (@sec:topology)], [recursion], [A one-to-one recursive verifier with the same statement; adds one knowledge-soundness term per compressed leaf and nothing else.], [---],
      [D14. Custom (cached) commitment for the ROM with its root as a public (@tbl:vk-ledger)], [setup / statement], [The ROM AIR verifies its openings against $"root"_"ROM"$ taken from $bold(p)$; binding of the Merkle commitment makes the fetched instructions those of $P$ with $"Commit"_"ROM"(P) = "root"_"ROM"$.], [---],
    )
  },
  caption: [Deviation ledger: proof-system-level differences between the vanilla construction and ZisK v0.16.1.],
  kind: table,
) <tbl:deviations>

== Transpiler Correctness Assumption <sec:transpiler-assumption>

ZisK executes programs in its own ISA, obtained from a RISC-V binary $P_"RV"$ by a deterministic transpiler $"Transpile"$ (@sec:isa). Everything proved in this document concerns the ZisK program $P = "Transpile"(P_"RV")$, which is what $"root"_"ROM"$ commits to. A claim about the RISC-V binary requires the following separate assumption, which is part of ZisK's trusted computing base and not discharged by any proof.

#assumption(title: "Transpiler Correctness")[
  For every RISC-V binary $P_"RV"$ in the supported subset, every input $"in"$ and every hint sequence $h$: if the ZisK execution of $"Transpile"(P_"RV")$ on $("in", h)$ is successful and declares outputs $"out"$, then the RISC-V execution of $P_"RV"$ on $"in"$ with the same hint responses terminates successfully and produces the same public outputs $"out"$.
] <asm:transpiler>

Under @asm:transpiler, @thm:target yields the statement about the original program: an accepting proof for $x = ("Commit"_"ROM"("Transpile"(P_"RV")), "out")$ implies that $P_"RV"$ has a successful execution producing $"out"$ on some input and hints. The verifier must independently know that $"root"_"ROM"$ is the commitment of the transpiled binary it cares about; in deployments this is established once, at setup, by recomputing $"Commit"_"ROM"$ from the binary.

== Soundness Sketch: From an Accepting Final Proof to an Execution <sec:soundness-sketch>

We sketch the extractor $cal(E)_"fin"$ of @thm:target and the lemma each step needs. Throughout, "accepting" means the relevant verifier outputs accept, and every step is conditioned on the failure events of the previous steps not occurring; the bound of @thm:target is the union bound over all failure events.

*Step 1 (Final layer).* Run the straight-line knowledge extractor of the Final's STARK on $(bold(p), pi)$ to obtain a witness $(alpha, sigma, pi_"AGG")$ of $cal(R)_"FINAL"["vk"^*]$: an aggregation proof accepted by $V_"AGG"$ under $(bold(p), alpha, sigma, "vk"^*)$ with $s = 0$, $kappa < B$, $alpha = "DeriveAlpha"(bold(p), bold(c))$. _Fails with_ $epsilon_"be"("Final")$.

*Step 2 (Recursive descent).* Apply the extractors of $V_"AGG"$ and $V_"LEAF"^((tau))$ recursively: an accepting aggregation proof yields $k$ accepting child proofs with statements $sigma_i$ summing to $sigma$ and all carrying $"vk"^*$; an accepting leaf-verifier proof of type $tau$ yields an accepting AIR proof $pi_tau$ with $s_tau$ and $bold(c)_tau = h("com"(pi_tau))$. Because every child's $"vk"$ equals the parent's and the root's is $"vk"^*$, every aggregation proof in the tree was verified with the genuine aggregation key (deviation D5); because $kappa$ is range-checked at every node and every node's $kappa$ is the sum of its children's, the tree has $kappa < B$ leaves. _Fails with_ $sum_v epsilon_"be"(v)$ over internal nodes. This step is the analogue of the "combine tree unrolling" lemma of the vanilla analysis; well-foundedness follows from $kappa$ strictly increasing towards the root.

#lemma(title: "Recursive descent")[
  From an accepting Final proof, the extractor obtains a multiset of at most $B$ accepting AIR proofs ${(tau_ell, bold(p), alpha, s_ell, pi_ell)}_ell$ such that $sum_ell s_ell = 0$ and $alpha = "DeriveAlpha"(bold(p), sum_ell h("com"(pi_ell)))$, except with probability $sum_v epsilon_"be"(v)$.
] <lem:descent>

*Step 3 (AIR extraction).* For each leaf, run the STARK extractor to obtain a witness $(bold(T)_ell, bold(a)_ell)$ satisfying $cal(A)_(tau_ell)$, consistent with $bold(p)$, with $"BusCont"_alpha (cal(I)_(tau_ell), bold(T)_ell, bold(a)_ell) = s_ell$, and whose stage-1 commitment is $"com"(pi_ell)$. _Fails with_ $sum_ell epsilon_"be"(tau_ell) + epsilon_"bind"$.

*Step 4 (Challenge soundness).* The multiset $S = {"com"(pi_ell)}$ of extracted commitments was fixed before $alpha$ was available to any prover: each $"com"(pi_ell)$ is the first message of its proof, and $alpha$ is a function of $bold(p)$ and $cal(H)(S)$. By @asm:lthash, no other multiset of size at most $B$ has the same hash except with $epsilon_"ms"$; modelling $"DeriveAlpha"$ as a random oracle, $alpha$ is therefore uniformly random and independent of the extracted witnesses. This is the formal content of the commit-then-justify argument for $alpha$. _Fails with_ $epsilon_"ms" + epsilon_"FS"$.

*Step 5 (Bus soundness).* The extracted witnesses form a witness for the circuit $cal(C)$ (possibly with several instances of each AIR) whose bus contributions sum to zero at a uniformly random $alpha$ (Step 4). By the LogUp soundness bound of @sec:arithmetization, every bus is balanced in the sense of @def:bus-balancing except with $epsilon_"LogUp" <= (N_"tot" + ell N_"tot"^2) / |KK|$. Hence the per-bus semantic relations hold: @def:rom-bus-relation (every Main row fetches $P["pc"]$), @def:operation-bus-relation (every delegated operation is correct), the table-bus membership relations, and the continuation relations.

*Step 6 (Stitching and memory).* By @lem:stitching applied to the Main's continuation bus, the Main instances form one sequence $G_1, dots, G_m$ starting at $("pc"_"BOOT", 0)$ and ending at $("pc"_"END", 0)$, with matching $("pc", c)$ at every boundary; concatenating their traces gives a sequence of rows $r = 0, dots, T - 1$ with globally consistent step counter, program counter and $c$. By @lem:memory-argument and its refinements, the multiset of memory operations requested by all rows (Main, MemAlign, precompiles) is consistent with the initial memory $"mem"_0$; define $"mem"_t$ as the memory obtained by applying, in memory-step order, all operations with memory step less than $1 + 4t$. This is the deterministic _memory reconstruction rule_ of the extractor. The read-only data region's contents are the first-access values, and the input-data region's contents define $"in"$.

*Step 7 (AIR-to-step).* Set $S_t := ("pc"_t, c_t, "mem"_t)$ from the Main rows and the reconstructed memory, $iota_t := P["pc"_t]$ (Step 5, ROM relation) and $h_t$ := the values read from the free-input port at step $t$. The Main's constraints, together with the operation-bus relation (correct $(c, "flag")$ and correct precompile memory effects) and the memory relation (operand reads return $"mem"_t$'s values and the store updates $"mem"_(t+1)$), imply $"Step"_P (S_t, iota_t, h_t, S_(t+1))$ for every $t$. This is a property of the Main AIR's constraint system alone and is the central W3 obligation.

#lemma(title: "AIR-to-step")[
  Let a Main row $r$ satisfy the Main AIR, let its ROM Bus message be a row of $P$, let its Operation Bus message (if any) be valid in the sense of @def:operation-bus-relation, and let its Memory Bus messages be consistent with $"mem"_t$ in the sense of Step 6. Then the state read off row $r + 1$ equals $"Step"_P$ applied to the state read off row $r$ with the row's hints.
] <lem:air-to-step>

*Step 8 (Boundary and outputs).* The genesis and terminus anchors give $S_0 = ("pc"_"BOOT", 0, "mem"_0)$ and $"pc"_T = "pc"_"END"$, $c_T = 0$. The global `pubout` terms on the Operation Bus, balanced in Step 5, give exactly one `pubout` per index $i$ in the Main trace with value $"out"_i$ from $bold(p)$, establishing $"Bind"_"out"$. The ROM relation with $"root"_"ROM"$ from $bold(p)$ establishes $"ProgramBind"$. Hence $(x; w_"exec") in cal(R)_"exec"$ with $w_"exec"$ the extracted execution.

The union of the failure probabilities of Steps 1--7 is the bound of @thm:target. Steps 1--3 are instances of backend knowledge soundness; Step 4 is the LtHash and Fiat-Shamir assumptions; Steps 5--8 are properties of ZisK's constraint system and buses and constitute the ZisK-specific W3 proof obligations.

== Proof-Obligation Ledger <sec:proof-obligations>

@tbl:obligations lists every lemma or assumption consumed by the sketch above, with its status.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (0.35fr, 3.6fr, 1.1fr),
      align: (left, left, left),
      table.header([*Id*], [*Obligation*], [*Status*]),
      [O1], [Knowledge soundness of the backend STARK for each circuit of @tbl:soundcalc-mapping with the parameters of @tbl:backend-params, in the random-oracle model for Poseidon2; straight-line extraction and its composition across the recursion (idealised, @sec:extractability).], [standard / assumed; parameters audited by `soundcalc`],
      [O2], [Binding of the stage-1 trace commitment and of the fixed and cached column commitments (Merkle trees over Poseidon2).], [standard, from collision resistance],
      [O3], [LtHash $(B, epsilon_"ms")$-binding with $n = 372$, $B = 2^(20)$ (@asm:lthash); consistency of the convention $kappa < B$ everywhere.], [assumed (SIS); convention fixed in this revision],
      [O4], [Fiat-Shamir: $"DeriveAlpha"(bold(p), cal(H)(S))$ modelled as a random oracle on (statement, multiset); the per-proof STARK challenges likewise.], [assumed (random oracle)],
      [O5], [LogUp soundness: if the union of all extracted witnesses does not balance a bus in the sense of @def:bus-balancing, then $sum_i s_i = 0$ holds with probability at most $(N_"tot" + ell N_"tot"^2)/|KK|$ over $(alpha, gamma)$; with $gamma = H_gamma (alpha)$ (D4).], [standard, adapted to D4; W3],
      [O6], [Well-formedness of every bus message: the interaction polynomials of each AIR emit exactly the schemas of @sec:bus-system, with binary selectors, and no AIR emits a message on a bus it is not listed on.], [inspection of the PIL sources; W3],
      [O7], [Memory argument (@lem:memory-argument): the constraints of @def:sorted-access-trace imply consistency of the requested operations with the initial memory; including the bounded-increment argument and the bridging rows.], [new (sorted-permutation memory over LogUp); W3],
      [O8], [Register refinement: the linked-step argument of @sec:registers with the per-segment reload implies that every register read returns the last written value, registers start at zero, and the $2^(24)$ window is never exceeded.], [new; W3],
      [O9], [MemAlign refinement (@lem:memalign-refinement) and byte-level MemAlign variants.], [new; W3],
      [O10], [Binding of the read-only data region's initial contents and of any RAM initialisation to the program committed by $"root"_"ROM"$ (remark in @sec:memory-relation): identify the chip that requests the initialising writes at v0.16.1 and show it is bound to $"root"_"ROM"$.], [open at v0.16.1; resolved by the ROM AIR's init messages in later versions],
      [O11], [Stitching (@lem:stitching) for the Main and for each Memory region; the `last`-flag argument that excludes cycles.], [new; W3],
      [O12], [AIR-to-step (@lem:air-to-step): the Main AIR's constraints implement operand resolution, store, and control flow exactly as in @sec:execution_model, including the `set_pc`/`flag` exclusion and the 32-bit address formation.], [new; W3 (constraint audit)],
      [O13], [Per-executor correctness: each executor and precompile AIR accepts an Operation Bus message only if it is valid per @appendix:opcodes and its memory effect; frequent-operation tables contain only valid triples.], [W3 (per-chip constraint audit)],
      [O14], [Range constraints: every limb column consumed by a relation is range-constrained as stated in @sec:word-encoding, and the increment/timestamp bounds of @def:sorted-access-trace cannot wrap modulo $p$.], [W3 (constraint audit)],
      [O15], [Cached-column lifecycle: the roots of the frequent-operation caches and fixed tables in the verification keys are those of the honestly computed tables (@sec:vk-ledger).], [setup-time check; documented],
      [O16], [Transpiler correctness (@asm:transpiler).], [trusted computing base],
      [O17], [Completeness: the honest prover's pipeline produces accepting proofs for every successful execution with $T < 2^(36)$ and at most $B$ leaves.], [not addressed here; W3],
    )
  },
  caption: [Proof-obligation ledger. "Standard" obligations are instances of published results for the named primitive; "new" ones are specific to ZisK's design and constitute the W3 work; "open" marks the single item whose status at v0.16.1 this revision could not settle from the specification alone.],
  kind: table,
) <tbl:obligations>
