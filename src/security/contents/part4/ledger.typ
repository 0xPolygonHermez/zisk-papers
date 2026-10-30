#import "../../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, fwd, game, lemma, mult,
  negl, poly, proof, proposition, remark, theorem, todo, vk,
)

Every term of @thm:final, and every hypothesis it rests on, is defined and
proved in this paper, stated in it and left to prove, inherited from a
standard result, or an explicit assumption. @tbl:ledger records the status of
each.

#figure(
  {
    set text(size: 8.5pt)
    table(
      stroke: 0.3pt,
      columns: (28%, 20%, 52%),
      align: (left, left, left),
      table.header([*Term or hypothesis*], [*Status*], [*Where*]),
      [$epsilon^*$, $epsilon^*_(Pi_X)$],
      [proved],
      [Round-by-round errors of @thm:iop-rbr and @cor:iop-jbr, with grinding (@lem:grinding); concrete levels in @tbl:security.],

      [$epsilon_"MT" (Q)$],
      [standard, in the random-oracle model],
      [Merkle trees over a random oracle (@def:merkle, @thm:bcs).],

      [Joint extraction of the AIR witnesses], [proved], [@lem:binding and the first statement of @thm:arguments.],
      [$Q dot Lambda_"pole" \/ abs(KK)$],
      [proved],
      [The poles of the bus columns (@rem:poles), charged in @lem:binding.],

      [$epsilon_(cal(F))(Lambda_"max")$], [proved], [LogUp (@lem:logup) and the bus argument (@prop:bus-soundness).],
      [Enforcement of the recursive relations], [assumption on the implementation], [@def:enforces.],

      [Straight-line composition], [idealization], [@rem:idealized, first item.],
      [$Adv("pa", cal(H))$],
      [idealization],
      [@def:cr and @rem:idealized, second item; LtHash is only known to be collision resistant, and the rigorous alternative is @rem:forking.],

      [$Adv("bind", Com_"cach")$],
      [standard, in the random-oracle model],
      [Binding of a Merkle tree over a random oracle (@def:commitment).],

      [$Lambda_"max" < p$], [parameter condition], [@lem:few-interactions; it holds for ZisK.],
      [Part III],
      [stated, partly proved],
      [@thm:theorem-iii and the lemmas of @sec:per-bus to @sec:memory; the proofs that read the constraints of the AIRs, and that of @thm:theorem-iii, are left as todos.],

      [Chip obligations],
      [obligation],
      [@tbl:obligations: the chips not proved sound in Part III, and the contents of the fixed tables and of the frequent-operation caches.],

      [Valid program], [assumption on $P^*$], [@sec:valid-programs; every program produced by the transpiler is valid.],
      [Transpiler correctness],
      [assumption],
      [@def:transpiler; it relates the committed ZisK program to the RISC-V binary.],
    )
  },
  caption: [Ledger of the terms and hypotheses of @thm:final.],
  kind: table,
) <tbl:ledger>

The analysis is about soundness, of the protocol as deployed in ZisK
v0.16.1. The following items are conditions on the implementation that the
theorem assumes, or are outside it.

- *Requirements on the recursive verifiers.* The relations of
  @sec:relations-def require the recursive verifiers to enforce the typing
  predicate on every non-null child and on the root, to require at least two
  non-null children at every aggregation node, to hash an identifier of the
  type together with the commitment into the challenge contribution, to
  expose the trace commitment as a public input of the AIR argument, and to
  feed the public statement, which carries the cached-column commitment, into
  the key derivation (@sec:instantiation).
- *Completeness.* That the honest pipeline produces an accepting final proof
  for every successful execution of length at most $2^(36)$ is not stated
  formally. The relations of @sec:relations-def admit the honest proofs, and
  the converse direction of @def:enforces is what a proof of completeness
  would need from the recursive verifiers.
- *Zero knowledge.* ZisK's proofs are not analyzed for zero knowledge, and
  nothing in this paper depends on it.
- *Wrappers.* A final proof can be wrapped into a pairing-based SNARK for
  verification on chain. The wrapper is outside the analysis; a wrapped proof
  inherits @thm:final only if the wrapper is knowledge-sound, with a
  straight-line extractor, for the relation of accepting final proofs.
- *Idealizations.* @thm:final rests on the two idealizations of
  @rem:idealized; the bound should be read as a statement about the structure
  of the reduction rather than as a concrete security level (@rem:concrete).
- *Part III.* The decoding of a balanced collection into an execution is
  stated, with the lemmas it rests on, and only partly proved here: the
  proofs that read the constraints of the AIRs, and the final induction, are
  left to a machine-checked formalization, together with the obligations on
  the chips that are not proved sound (@tbl:obligations).
- *Versions.* The analysis follows the constraints of ZisK v0.16.1. Later
  versions change parts of the design that the analysis depends on, such as
  how the read-only data is initialized, and the statements of Part III must be
  checked again for each version.
