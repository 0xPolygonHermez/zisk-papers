#import "../lib.typ": definition

This section describes how the AIR constraints and bus-balancing conditions from Section 4 are turned into a cryptographic argument of correctness. <sec:ps>

== Constraint Language: PIL2

ZisK's constraint system is expressed in _PIL2_ (Polynomial Identity Language 2), a domain-specific language for AIR-based constraint systems. PIL2 source files are compiled by the PIL2 compiler into a binary `.pilout` artifact (`pil/zisk.pilout`), which the proof system consumes directly.

PIL2 provides:
- `col fixed` — preprocessed (public) columns, computed at setup time.
- `col witness` — private witness columns, computed per execution.
- `airval` — scalar public values attached to an AIR instance (see Section 4.1.2).
- `proofval` — proof-level public values (e.g., `enable_input_data`) that control which optional AIR instances are active in a given proof.
- `lookup_assumes` / `lookup_proves` — bus interaction declarations that compile to LogUp constraints.

The complete ZisK constraint system is assembled in `pil/zisk.pil` under the `airgroup Zisk` declaration.

== Field and Extension

ZisK uses the Goldilocks prime field $bb(F) = bb(F)_p$ with $p = 2^(64) - 2^(32) + 1$ as the base field. This choice offers 64-bit arithmetic that maps efficiently to modern CPUs while remaining large enough for soundness.

For the polynomial commitment and verification steps, the proof system works over the degree-3 extension field $bb(K) = bb(F)[X] \/ (X^3 - X - 1)$. The extension field provides the additional algebraic degrees of freedom needed for the LogUp challenges and soundness amplification.

== STARK Proof Generation

Each AIR instance in the `airgroup Zisk` is proved independently with a STARK. The STARK protocol proceeds as follows:

+ *Witness computation*: The prover evaluates all `col witness` columns over the trace domain of $N$ rows, producing the trace matrix $bold(T) in bb(F)^(N times w)$.

+ *Polynomial commitment*: Witness columns are interpolated into degree-$(N-1)$ polynomials and committed using a polynomial commitment scheme. ZisK uses the `proofman` library (from the `pil2-proofman` project referenced in `Cargo.toml` via the `gha_pil2_proofman_js_branch` metadata field).

+ *Challenge sampling*: The verifier (or the Fiat--Shamir hash) provides random challenges $alpha, gamma in bb(K)$ for the LogUp argument.

+ *LogUp accumulation*: The prover computes the partial-sum polynomial $S$ (Section 4.4) and commits to it. The final value $c_i = S(N-1)$ becomes a public output of the proof.

+ *Low-degree test*: The prover demonstrates that all constraint and accumulation polynomials have degree at most $N-1$ using a FRI-based proximity test over the Goldilocks field.

+ *Query phase*: The verifier checks constraint evaluations at randomly sampled positions to complete the STARK verification.

== Proof Generation Pipeline

The end-to-end proving pipeline is orchestrated by `executor/src/executor.rs` and `core/src/lib.rs`:

+ *Emulation*: The ZisK emulator (`emulator/`) executes the program to determine which secondary state machines (binary, arithmetic, precompiles) are needed and in what quantities.

+ *Witness planning*: The executor plans AIR instance sizes and allocates memory for trace generation (`executor/src/sm_static_bundle.rs`).

+ *Trace generation*: Each AIR's trace is filled in parallel by dedicated witness generators (`executor/src/witness_generator.rs`, `executor/src/witness_orchestrator.rs`). The operation bus routes intermediate values between the main trace and sub-AIR generators.

+ *Individual proofs*: Each AIR instance is proved independently. This is the most compute-intensive step and the main target for parallelism and distributed proving.

+ *Aggregation*: Completed proofs are fed into the aggregation tree (Section 5) level by level. Each aggregation circuit verifies two child proofs and adds their partial sums.

+ *Root proof*: The root aggregation circuit checks $sum_i c_i = 0$ and produces the final proof.

== Virtual Tables and Frequent-Operation Caching

Two optimizations reduce the size of lookup-table AIRs:

- *Virtual tables* (`set_group_virtual_tables` in `pil/zisk.pil`, lines 76--78): Large lookup tables (e.g., `BinaryTable`, `ArithTable`, `KeccakfTable`) are represented as _virtual_ AIRs. Their trace is not stored in RAM in the conventional sense; instead, the PIL2 runtime materializes only the rows that are actually looked up, using compressed binary format.

- *Frequent-operations tables* (`FrequentOps` AIR, `state-machines/arith/src/arith_frops_fixed.bin` etc.): A small set of the most frequently occurring operation inputs/outputs is precomputed and stored as a fixed binary file. Lookups that hit this cache are resolved without generating a full AIR row, substantially reducing the number of constraint evaluations for common operations.

== Distributed Proving

For very large programs, ZisK supports distributing proof generation across multiple worker machines (`distributed/`). The coordinator assigns segments to workers; each worker independently generates traces and STARK proofs for its assigned segments. When all workers complete, the coordinator aggregates the proofs using the same tree structure described in Section 5. Communication uses gRPC (`distributed/crates/grpc-api/`), and the coordinator exposes webhook notifications on job completion.
