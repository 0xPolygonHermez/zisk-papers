#import "../lib.typ": definition

Recent advances in zero-knowledge (ZK) proving systems @EPRINT:GabWilCio19, @ICALP:BBHR18, @EPRINT:DiaPos23b, @EPRINT:HabLevPap24  have opened the door to a new class of cryptographic applications: systems that can verify the correct execution of an arbitrary computation without revealing its private inputs, in time and space sublinear in the original computation. These properties underpin a rapidly expanding class of applications in blockchain scalability—such as validity rollups, verifiable coprocessors, and trustless cross-chain bridges—as well as an increasingly broad range of off-chain computation protocols.

== Background and Motivation

Early ZK systems required developers to express computations directly as arithmetic circuits using frameworks such as Circom @CIRCOM or Halo2 @HALO2. This low-level approach offers the greatest flexibility ---developers can hand-tune constraint counts and choose their proof backend--- but comes at a significant cost: every new computation requires custom circuit design, security review, and ongoing maintenance. The productivity model is fundamentally different from standard software development, limiting who can build ZK-enabled applications.

_Zero-knowledge virtual machines_ (zkVMs) address this by interposing a fixed, general-purpose circuit between the developer and the proving system. The circuit verifies the correct execution of programs targeting a standard instruction set architecture (ISA), so developers can write programs in familiar languages like Rust or C and obtain proofs automatically, without writing a single constraint. The challenge for zkVM designers is then to make this general-purpose circuit as efficient as possible.

Existing zkVMs navigate a fundamental trade-off between developer experience and proving efficiency. Systems built around _ZK-native ISAs_ (e.g., Cairo @EPRINT:GolPapRia21 or Valida @VALIDA) define instruction sets whose semantics align naturally with finite-field arithmetic, enabling compact constraint representations but requiring developers to adopt a new programming model. Systems targeting _standard ISAs_ such as RISC-V @RISCV (e.g., RISC Zero @RISCZERO, SP1 @SP1 or Nexus @NEXUS) preserve familiar toolchains and allow any RISC-V binary to run, but must constrain a general-purpose register machine whose operations ---integer division, bitwise logic, memory addressing--- are expensive to encode as polynomial constraints.

== ZisK

This paper introduces ZisK, a zkVM designed to make zero-knowledge proofs of general-purpose computation practical at production scale. ZisK targets the RISC-V ISA, preserving compatibility with mature toolchains such as LLVM and Rust so that programs can be proved without changes to existing development workflows. This positions ZisK in the standard-ISA camp, but with a deliberate architecture that treats proving performance as a first-class concern: rather than accepting the overhead of a general-purpose CPU circuit, ZisK uses a modular design where expensive operations are handled by dedicated, independently optimized constraint systems.

A central motivation for ZisK is _extensibility_. Application domains such as blockchain execution environments rely on a specific, known set of expensive primitives ---elliptic-curve operations, hash functions, bulk memory transfers. A zkVM designed for these domains should be able to support those primitives natively, with proofs that are tight to the operation's intrinsic complexity. ZisK is structured so that such optimized components can be added as self-contained modules without modifying the rest of the system, making it practical to tailor the prover to a specific application's workload. Building on STARKs @EPRINT:BBHR18 further ensures that this is achieved without a trusted setup and with post-quantum security.

== Paper Overview

@sec:isa defines the ZisK ISA: execution environment, machine state, and instruction format. @sec:arithmetization presents the arithmetization framework: AIRs, bus interactions, and LogUp-based circuit satisfiability. @sec:design describes the chip architecture and bus system. @sec:continuations explains trace splitting and how continuation buses chain segment boundaries. @sec:recursion covers the recursive aggregation tree, the recursive challenge derivation, and root-level bus balancing.

== Notation

For the remainder of the paper, we fix $bb(F)$ to be a finite field of prime order $p$. In particular, we use the Goldilocks prime field $p = 2^64 - 2^32 + 1$, though this choice is not fundamental to the overall design and any appropriate prime would suffice. When needed, we identify field elements with integers in the range $[0, p)$.

We also fix a finite extension field $bb(K)$ of $bb(F)$, primarily for the security of the underlying proving system; concretely, ZisK targets $128$-bit security. In particular, we use the third Goldilocks extension $frac(bb(F)[X], (X^3 - X - 1), style: "horizontal")$, whose order $|bb(K)| = p^3 approx 2^(192)$ gives enough room to drive the proving system's soundness error well below $2^(-128)$, while still allowing efficient arithmetic. Again, this choice is not fundamental to the design.

We denote by $bb(F)[X]$ the ring of univariate polynomials over $bb(F)$ and by $bb(F)[X_1, ..., X_n]$ the ring of $n$-variate polynomials over $bb(F)$. When needed, we write $bb(F)^(<N)[X]$ to refer to the subset of polynomials of degree strictly less than $N$. We use $bb(F)^(n times m)$ to denote the set of $n$-by-$m$ matrices over $bb(F)$. The same notation applies to $bb(K)$.

We use the notation $[a, b]$ to denote the set of integers from $a$ to $b$, inclusive; and $[a, b)$ to denote the set of integers from $a$ to $b$, inclusive of $a$ and exclusive of $b$. When $a = 1$, we write $[b]$ instead of $[1, b]$.
