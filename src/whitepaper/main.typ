#import "../shared/style.typ": appendix, paper, references

#show: paper.with(
  title: "ZisK Whitepaper",
  authors: ((name: "ZisK Core Team"),),
  // Fixed on purpose: the build script pins SOURCE_DATE_EPOCH for
  // reproducible PDFs, so `datetime.today()` would not give the real date.
  date: [October 30, 2026],
  abstract: [
    We present ZisK, a STARK-based zero-knowledge virtual machine (zkVM) that executes programs compiled from standard instruction set architectures and produces succinct, transparent proofs of their correct execution. ZisK targets the RISC-V ISA, allowing developers to use existing Rust and C toolchains without modification. Moreover, ZisK's modular architecture enables the addition of optimized constraint systems for expensive operations such as elliptic-curve arithmetic and bulk memory access, making it practical to prove complex computations at scale.

    This paper provides a precise specification of the ZisK design: its instruction set architecture, the arithmetization framework, the circuit architecture and chip design, the continuation mechanism, the recursive aggregation system, and the proving backend with its parameters.
  ],
)

= Introduction <sec:introduction>

#include "contents/introduction.typ"

= Instruction Set Architecture <sec:isa>

#include "contents/isa.typ"

= Arithmetization Framework <sec:arithmetization>

#include "contents/arithmetization.typ"

= ZisK Design <sec:design>

#include "contents/design.typ"

= Continuations <sec:continuations>

#include "contents/continuations.typ"

= Recursion <sec:recursion>

#include "contents/recursion.typ"

= Proving Backend <sec:backend>

#include "contents/backend.typ"

#pagebreak()

#heading(outlined: false, numbering: none)[Acknowledgments]

This paper draws on the designs presented in the OpenVM @OPENVM and Nexus @NEXUS whitepapers, which served as important sources of inspiration. We also acknowledge RISC Zero @RISCZERO as a pioneering zkVM and SP1 @SP1 for advancing the practical deployment of RISC-V-based proving systems.

We extend our gratitude to the Polygon zkEVM and Plonky3 @PLONKY3 teams for their foundational work in zero-knowledge proving systems, as well as to the RISC-V community @RISCV for providing a robust architecture that enables the zkVM model.

#set heading(outlined: true)

#references()

#show: appendix

= Arguments <appendix:arguments>

#include "appendix/arguments.typ"

#pagebreak()

= Instruction Set <appendix:opcodes>

#include "appendix/instruction-set.typ"
