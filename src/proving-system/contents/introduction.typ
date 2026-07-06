#import "../../lib.typ": definition, remark

A proving system separates cleanly into a _frontend_, which turns a computation into a system of polynomial constraints, and a _backend_, which turns a witness for those constraints into a succinct cryptographic proof. The ZisK whitepaper (its Arithmetization Framework section) specifies the frontend in full: the AIR framework, interactions, buses, and the LogUp reduction of bus balancing. It treats the backend abstractly ---a one-time setup produces a proving key $sans("pk")$ and a verification key $sans("vk")$, and verification of a proof $pi$ against a public statement $x$ is a deterministic procedure $V(sans("vk"), x, pi) in {sans("accept"), sans("reject")}$--- without committing to how $pi$ is produced.

This document fills that gap with a concrete backend: a #smallcaps[multilinear STARK]. Where a classical STARK @EPRINT:BBHR18 views each trace column as a univariate polynomial over a multiplicative subgroup and enforces constraints by low-degree testing a quotient, the multilinear approach views each column as a function on the Boolean hypercube, enforces constraints by a _sumcheck_ @JACM:LFKN92, and commits columns with the #smallcaps[Basefold] polynomial commitment scheme @EPRINT:ZCF23. The two layers remain decoupled: the same frontend AIRs are proved unchanged; only the backend differs.

== What a Basic Proof Is

The ZisK circuit $cal(C) = {(cal(A)_i, cal(I)_i)}_(i=1)^M$ is proved piecewise. Each _instance_ is a concrete witness for one of the AIRs $(cal(A)_tau, cal(I)_tau) in cal(C)$, and a _basic proof_ is the backend's proof for a single instance. In the language of the whitepaper's recursion layer, a basic proof is exactly a proof for the AIR-leaf relation $cal(R)_"AIR"^((tau))$: given a challenge $alpha in KK$, the program publics $bold(p)$, and a claimed bus contribution $s$, it attests that there is a witness $(bold(T), bold(a))$ that

+ satisfies the AIR $cal(A)_tau$ and is consistent with $bold(p)$, and
+ produces the partial bus sum $s$ under $alpha$.

Basic proofs are the leaves of the aggregation tree; combining them into a single circuit-level statement ---checking global bus balancing $sum_i s_i = 0$ under a common challenge--- is the job of recursion (the whitepaper's Recursion section) and is out of scope here. What this document specifies is precisely how one basic proof is generated and verified.

== Preliminaries and Notation

We work over the Goldilocks prime field $FF$ with $p = 2^(64) - 2^(32) + 1$, and its degree-three extension $KK = FF[X] slash (X^3 - X - 1)$, used for all soundness-critical randomness. We reuse the whitepaper's AIR notation without change: an AIR $cal(A) = {C_i}_(i in I)$ of width $W$, depth $D$, and $V$ values; a witness $(bold(T), bold(a))$ with trace matrix $bold(T) in FF^(N times W)$ and AIR values $bold(a) in FF^(V)$; columns $T_j : [N] arrow FF$; the shifted variable $X_j^((k))$ instantiated at row $r$ by $T_j(r + k)$ (indices modulo $N$); the value variable $Y_j$ instantiated by $a_j$. Throughout we take the trace height to be a power of two, $N = 2^n$, and we identify a row index $r in [N]$ with its little-endian bit decomposition
$
  bold(r) = (r_0, r_1, dots, r_(n-1)) in {0,1}^n, quad r = sum_(i=0)^(n-1) r_i 2^i.
$
Vectors are set in bold; $bold(p) in FF^(k)$ is the public statement.
