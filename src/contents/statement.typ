#import "../lib.typ": definition, remark, assumption, lemma, theorem

The relations of @sec:recursion say what each recursive verifier checks: that certain proofs verify and that certain sums vanish. They do not, on their face, say anything about programs. This section states what ZisK proves _about program execution_: a typed public statement, a semantic execution relation whose witness is an execution in the sense of @sec:execution_model, and the knowledge-soundness property that connects an accepting final proof to such a witness. The sketch of why the relations of @sec:recursion imply this property is the subject of @sec:security.

== Public Statement Ledger <sec:public-ledger>

The external verifier receives the Final Verifier's proof together with a vector $bold(p) in FF^(68)$ and a fixed _verification context_. @tbl:public-ledger says what every entry is and which role it plays.

#figure(
  table(
    stroke: 0.3pt,
    columns: (1.1fr, 0.5fr, 0.9fr, 3fr),
    align: (left, center, left, left),
    table.header([*Entry*], [*Width*], [*Role*], [*How it is bound*]),
    [$"root"_"ROM"$], [4], [program binding], [Merkle root of the cached ROM columns encoding $P$ (@tbl:vk-ledger). Consumed by the ROM AIR's verifier as the root of its custom commitment, so every instruction fetched on the ROM Bus is a row of the table committed under this root.],
    [$"out"_0, dots, "out"_(31)$ as $64$ limbs], [64], [public outputs], [Received on the Operation Bus as the $32$ messages $(mono("pubout"), i, "out"_i, "out"_i, 0, 0, 0)$ by a degree-zero global term (@sec:operation-bus); balancing forces the Main to have executed exactly one `pubout` per index with matching value.],
    [$"vk"_"FINAL"$, $"vk"^*$], [context], [verification keys], [Held by the external verifier; fix the whole key chain of @tbl:vk-ledger and thereby the circuit $cal(C)$ and the backend parameters.],
    [$alpha$], [3], [recursive only], [The global challenge. It is a public of every internal node but is _consumed_ by $cal(R)_"FINAL"$ ($alpha = "DeriveAlpha"(bold(p), bold(c))$) and does not appear in the external statement.],
    [$sigma = (s, tau, kappa, bold(c))$], [$1 + 1 + 1 + 372$], [recursive only], [Recursive statement; consumed by the Final's global checks and not exposed externally.],
    [$"vk"$ (propagated)], [4], [recursive only], [Bound to $"vk"^*$ by the Final; not exposed externally.],
    [proof-level selectors], [9], [witness-only], [Booleans indicating which optional AIRs (input data, ROM data, DMA variants) are instantiated; constrained boolean, included in the challenge transcript, and used only to gate the genesis anchors of unused regions. They carry no semantic information about the execution.],
  ),
  caption: [Ledger of the public statement. The externally meaningful part is $x := ("root"_"ROM", "out")$, and $bold(p)$ is its field encoding; the remaining rows exist only inside the recursion. Neither the input stream nor the hints appear anywhere: they are existentially quantified in @def:exec-relation.],
  kind: table,
) <tbl:public-ledger>

We write $x = ("root"_"ROM", "out") in FF^4 times [0, 2^(64))^(32)$ for the typed final statement and identify it with $bold(p)$ through the encoding of @tbl:public-ledger.

== The Execution Relation <sec:exec-relation>

Let $"Commit"_"ROM"(P)$ denote the deterministic procedure that lays out a program $P$ as the cached columns of the ROM AIR (one row per instruction with the fields of @subsec:instruction_format, padded with zero rows to $2^(22)$) and returns their Merkle root under the backend's commitment (@sec:trace-commitment). We use the objects of @sec:execution_model: guest states $S_t = ("pc"_t, c_t, "mem"_t)$, instructions $iota_t$, hint sequences $h_t$, the step predicate $"Step"_P$, the initial memory $"mem"_0 (P, "in")$, and the outputs $"out"_i (S_0, dots, S_T)$.

#definition(title: "ZisK Execution Relation")[
  The _execution relation_ $cal(R)_"exec"$ consists of the pairs $(x; w_"exec")$ with $x = ("root"_"ROM", "out")$ and
  $
    w_"exec" = (P, T, "in", (S_t)_(t=0)^T, (iota_t)_(t=0)^(T-1), (h_t)_(t=0)^(T-1))
  $
  such that
  + (_ProgramBind_) $"root"_"ROM" = "Commit"_"ROM"(P)$;
  + (_Init_) $S_0 = ("pc"_"BOOT", 0, "mem"_0 (P, "in"))$, with $"in"$ a word-aligned byte string of length less than $2^(30)$;
  + (_Fetch and Step_) for all $t < T$: $iota_t = P["pc"_t]$ and $"Step"_P (S_t, iota_t, h_t, S_(t+1))$ (@def:step);
  + (_Term_) $"pc"_T = "pc"_"END"$ and $c_T = 0$, and $T < 2^(36)$;
  + (_Bind_) $"out"_i = "out"_i (S_0, dots, S_T)$ for all $i in [0, 32)$, i.e. the $i$-th public output declared by the execution equals the $i$-th word of the statement.
] <def:exec-relation>

In words: an accepting final proof for $x$ is meant to convince the verifier that _there exist_ an input and a hint sequence under which the program committed to by $"root"_"ROM"$ runs successfully from the boot state and declares exactly the outputs $"out"$. The input and the hints are witnesses, not statement: ZisK proves nothing about them beyond what the program itself checks and exposes through its outputs. The relation is about the committed ZisK program $P$; its connection to a RISC-V binary is the separate assumption of @sec:transpiler-assumption.

The two binding predicates of the reviewers' template are instantiated as follows. $"Bind"_"in"$ is vacuous ---no public input is bound--- except for the program, which is bound through $"root"_"ROM"$. $"Bind"_"out"$ is the equality of the statement's words with the values carried by the $32$ `pubout` instructions of the execution; since those instructions read the output-data region of $"mem"_T$ word by word, $"Bind"_"out"$ equivalently says that $"out"_i = "mem"_T [$ `0xA001_0000` $+ 8 i]_8$ for the memory at the time the boot code reads it.

== Execution Extractability <sec:extractability>

Let $Pi_"fin" = ("Prove"_"fin", V_"fin")$ be the final non-interactive argument exposed to the external verifier: $V_"fin"(x, pi)$ runs the Final Verifier's STARK verifier $V("vk"_"FINAL", bold(p), pi)$ with $bold(p)$ the encoding of $x$. We use the standard knowledge-soundness notion with a straight-line extractor, following the reference formulation of the EF sprint documents @EF:ZKVMREQ.

#definition(title: "Execution Extractability")[
  $Pi_"fin"$ is _execution-extractable_ for $cal(R)_"exec"$ with error $epsilon_"fin"$ if there is a probabilistic polynomial-time extractor $cal(E)_"fin"$ such that for every probabilistic polynomial-time adversary $cal(A)$,
  $
    Pr[ (x, pi) arrow.l cal(A)(1^lambda) : V_"fin"(x, pi) = "accept" and (x; cal(E)_"fin"(x, pi)) in.not cal(R)_"exec" ] <= epsilon_"fin"(lambda).
  $
  The extractor is given $(x, pi)$ and the same oracle access as the verifier; its running time is that of $cal(A)$ plus a polynomial in $lambda$ and in the size of the extracted execution.
] <def:execution-extractability>

#remark(title: "Extraction model")[
  ZisK's proofs are hash-based, and all challenges (the per-proof STARK challenges and the global challenge $alpha$) are derived by Fiat-Shamir from Poseidon2. The natural model is therefore the random-oracle model for Poseidon2, in which STARK/FRI arguments admit straight-line extractors. Composing such extractors across the recursion requires each inner argument to remain knowledge-sound relative to the same oracle, which is known not to hold for succinct arguments in general @EPRINT:BarChiGua24. Like the reference vanilla analysis, we idealise over this obstruction: the soundness sketch of @sec:security assumes straight-line extraction composes across the tree, and the resulting bounds should be read as statements about the reduction structure rather than as concrete security levels for the recursion. The concrete $128$-bit figure of @sec:security-level is the soundness of each individual STARK, which is what `soundcalc` measures.
]

#theorem(title: "What ZisK Proves (target statement)")[
  Under the assumptions listed in @sec:proof-obligations ---knowledge soundness of the backend STARK for every circuit in @tbl:soundcalc-mapping, binding of the trace commitments, LtHash binding (@asm:lthash), and the random-oracle modelling of Poseidon2--- the ZisK final argument $Pi_"fin"$ is execution-extractable for $cal(R)_"exec"$, with
  $
    epsilon_"fin" <= sum_("nodes" v) epsilon_"be"(v) + epsilon_"ms" + epsilon_"FS" + epsilon_"LogUp" + epsilon_"bind",
  $
  where the sum ranges over the nodes of the aggregation tree (each contributing the knowledge-soundness error of its STARK), $epsilon_"ms"$ is the LtHash binding error, $epsilon_"FS"$ the probability that a random-oracle challenge collides or is guessed, $epsilon_"LogUp"$ the bus soundness error of @def:global-bus-relation at a random $alpha$, and $epsilon_"bind"$ the Merkle binding error over all commitments opened by the extractor.
] <thm:target>

The theorem is the W2 _target_: its statement is precise, its proof is the W3 deliverable. @sec:security gives the lemma chain and the ledger of every term used above, indicating for each whether it is discharged in this document, inherited from a standard result, or left as an explicit W3 obligation.

== Definition Ledger <sec:definition-ledger>

The following table lists every soundness-flavoured term used in @thm:target and in @sec:security, and where its meaning is fixed.

#figure(
  table(
    stroke: 0.3pt,
    columns: (1.6fr, 1.1fr, 2.3fr),
    align: (left, left, left),
    table.header([*Term*], [*Status*], [*Where*]),
    [execution relation $cal(R)_"exec"$], [defined here], [@def:exec-relation],
    [step predicate, fetch, initial and terminal states], [defined here], [@def:step and @sec:execution_model],
    [execution extractability], [defined here], [@def:execution-extractability],
    [backend knowledge soundness $epsilon_"be"$], [assumed (backend)], [@sec:stark-backend, values from `soundcalc` @SOUNDCALC],
    [trace-commitment binding], [assumed (backend)], [@sec:trace-commitment: Merkle binding under collision-resistant Poseidon2],
    [LtHash multiset binding $epsilon_"ms"$], [defined here, assumed], [@def:multiset-binding, @asm:lthash],
    [Fiat-Shamir / transcript binding $epsilon_"FS"$], [assumed (random oracle)], [@def:zisk-challenge and the remark on the extraction model],
    [bus balancing (semantic)], [defined here], [@def:bus-balancing],
    [global bus relation $cal(R)_"BUS"^(alpha)$ and LogUp soundness $epsilon_"LogUp"$], [defined here, proof obligation], [@def:global-bus-relation and @sec:proof-obligations],
    [per-bus relations (operation, ROM, memory, table)], [defined here], [@sec:bus-system],
    [memory argument, register and MemAlign refinements], [defined here, proof obligation], [@def:sorted-access-trace, @lem:memory-argument, @lem:memalign-refinement],
    [segment, continuation relation, stitching], [defined here, proof obligation], [@def:segment, @def:continuation-relation, @lem:stitching],
    [recursive relations $cal(R)_"AIR", cal(R)_"LEAF", cal(R)_"AGG", cal(R)_"FINAL"$], [defined here], [@sec:recursion],
    [transpiler correctness], [assumed (trusted computing base)], [@sec:transpiler-assumption],
  ),
  caption: [Definition ledger for the terms used in the soundness statement.],
  kind: table,
) <tbl:definition-ledger>
