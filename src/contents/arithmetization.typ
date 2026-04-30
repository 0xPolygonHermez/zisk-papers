#import "../lib.typ": definition

A proving system is naturally divided into two layers. The _frontend_ takes a program and produces a structured mathematical representation --- typically a system of polynomial constraints --- that captures exactly what it means for the computation to be correct. The _backend_ then takes that representation and produces a cryptographic proof of its satisfiability. The two layers are decoupled by design: a single frontend can target different backends, and improvements to either do not require redesigning the other.

ZisK's _arithmetization framework_ is its frontend. The choice of arithmetization is consequential: it determines how circuits are structured, what operations are native, and how efficiently the backend can prove them. ZisK's arithmetization is designed to be modular and flexible, capturing a wide range of computations while optimizing for the patterns that arise most frequently in zkVM execution.

The frontend is based on a generalization of the _algebraic intermediate representation (AIR)_ framework @EPRINT:BBHR18, which specifies polynomial constraints over a witness matrix; coupled with arguments such as LogUp @EPRINT:Habock22b, which extends AIR with logarithmic derivative-based lookups. A single AIR captures the behavior of one logical unit (e.g., the CPU, the ALU, or the memory). Since realistic computations involve multiple interacting units, we group AIRs together and define _interactions_ between them ---messages exchanged through shared communication channels called _buses_. This modular design has several advantages:
- *Separation of concerns*: Each AIR can be designed, implemented, and tested independently.
- *Composability*: AIRs can be reused across different computations or combined in different configurations.
- *Scalability*: Different AIRs can have different sizes, allowing resources to be allocated based on actual usage.
- *Backend independence*: The arithmetization can be paired with any compatible proving system.

The remainder of this section formalizes these concepts.

== AIRs

We generalize the standard AIR definition @EPRINT:BBHR18 by augmenting it with _AIR values_: a fixed vector of field elements attached to the instance rather than indexed by row. This extension is non-standard but necessary to express global constants ---such as public inputs or aggregation roots--- as first-class citizens of the constraint system rather than as workarounds encoded in the trace.

#definition(title: "AIR and Witness")[
  An _algebraic intermediate representation_ (AIR) of width $W$, depth $D$, and $V$ values is a set of _polynomials_:
  $
    cal(A) = { C_i }_(i in I) subset FF[X_1^((0)), ..., X_W^((0)), ..., X_1^((D)), ..., X_W^((D)), Y_1, ..., Y_V]
  $
  where $I$ is a finite index set. Polynomials $C_i$ are typically known as _constraint polynomials_ or simply _constraints_.

  A _witness_ for $cal(A)$ is a pair $(bold(T), bold(a))$ where $bold(T) in FF^(N times W)$ (with $N$ a power of two) is the _trace matrix_ and $bold(a) in FF^V$ are the _AIR values_. The $j$-th column of $bold(T)$, viewed as a mapping $T_j : [N] arrow FF$, instantiates the family of shifted variables $X_j^((0)), ..., X_j^((k))$: at row $r$, the variable $X_j^((k))$ takes the value $T_(j)(r + k)$. The variable $Y_j$ is instantiated by $a_j$, the same value at every row. The witness _satisfies_ $cal(A)$ if for every constraint $C in cal(A)$ and every row $r in [N]$:
  $
    C(T_1(r), ..., T_(W)(r), ..., T_1(r+D), ..., T_(W)(r+D), a_1, ..., a_V) = 0
  $
  where row indices are taken modulo $N$.
]

Not all columns in a trace have the same lifecycle. Some are fully determined by the program before any execution begins; others depend on the specific inputs provided; and others are intermediate values the prover computes but need not reveal. Distinguishing these cases allows the proving system to avoid redundant work ---a column that is the same across all executions of a program need only be committed once--- and to be precise about what the verifier is entitled to see. Trace columns are therefore partitioned into three categories according to when they are determined and who can access them:

- *Fixed*: Determined at setup time, independent of any particular execution. Fixed columns are shared with the verifier as part of the AIR's description; when an AIR has fixed columns, the trace height $N$ is also fixed at setup. Typical uses include lookup tables and instruction encodings.

- *Cached*: Computed by the prover and committed once, then reused across multiple executions of the same program. Cached columns capture data that depends on the program but not on its inputs ---such as the ROM instruction trace--- avoiding redundant recomputation.

- *Witness*: Computed fresh for each execution and not revealed to the verifier. These columns carry the execution-specific state: operation values, memory accesses, and all intermediate values produced during a run.

== Interactions

A single AIR is self-contained: its constraint polynomials relate columns within the same trace and cannot reference columns of another AIR. Yet realistic computations are inherently cross-cutting ---the CPU must read values that the memory has written, and a hash precompile must receive inputs from and return outputs to the main execution trace. To express these relationships without merging all AIRs into one monolithic constraint system, we introduce _interactions_: row-level messages that one AIR sends and another receives, mediated by a shared channel called a _bus_. An interaction specifies which values are communicated at each row and with what multiplicity; consistency across AIRs is then enforced by requiring that every bus is _balanced_ ---the total signed flow of messages sums to zero.

#definition(title: "Interaction")[
  Let $cal(A)$ be an AIR of width $W$, depth $D$, $V$ values. An _interaction_ of length $ell$ for $cal(A)$ is a tuple $(b, m, bold(e))$ where:
  - $b in FF$ is a _bus identifier_.
  - $m in FF[X_1^((0)), ..., X_W^((0)), ..., X_1^((D)), ..., X_W^((D)), Y_1, ..., Y_V]$ is the _multiplicity_ polynomial.
  - $bold(e) in FF[X_1^((0)), ..., X_W^((0)), ..., X_1^((D)), ..., X_W^((D)), Y_1, ..., Y_V]^ell$ are the _message_ polynomials.

  Given a witness $(bold(T), bold(a))$ for the host AIR, the _evaluation_ of the interaction at row $r$ is obtained by substituting $X_j^((k)) arrow.l T_j(r+k)$ and $Y_j arrow.l a_j$. We write $m(r)$ and $bold(e)(r)$ for the resulting scalar and vector in $FF^ell$, leaving the witness implicit when clear from context.
]

Each AIR can be augmented with a set of interactions. At each row, the interaction emits the message $bold(e)(r)$ with signed multiplicity $m(r)$: a positive multiplicity means the AIR _sends_ the message, a negative multiplicity means it _receives_ it.

Interactions define the communication structure, but they do not by themselves specify what semantic relationship is being enforced. That is the role of _arguments_.

== Arguments

_Arguments_ are the semantic tools used to specify what consistency must hold across bus interactions: a permutation argument asserts that two multisets are equal or a lookup argument asserts containment in a table. Each argument type is realized as a pair of interactions on a shared bus ---one AIR sending with positive multiplicity, another receiving with negative multiplicity--- so that bus balancing becomes equivalent to the desired relationship holding. A detailed description of the specific arguments used in ZisK is provided in @appendix:arguments.

Bus balancing is therefore the unified consistency condition underlying all arguments. However, checking it naively ---summing over every row of every AIR--- requires the verifier to process the full witness, defeating succinctness. We use _LogUp_ @EPRINT:Habock22b to reduce bus balancing to a small set of polynomial constraints that the backend can verify efficiently. The reduction proceeds in two steps: first, compress each multi-element message into a single field element; then, express the balancing sum as a polynomial identity checkable at a random location.

=== LogUp Reduction

The key insight of LogUp is that multiset equality can be recast as a rational identity over a random challenge. Two multisets $S$ and $R$ (with multiplicities) are equal if and only if, for a _challenge_ $alpha$:
$
  sum_(s in S) frac(1, alpha + s) = sum_(r in R) frac(1, alpha + r)
$
Here, by _challenge_ we refer to a random field element sent by the verifier after the prover has committed to its witness; because the prover cannot predict it before committing, the challenge breaks any attempt to craft a witness that satisfies the identity by accident. In the non-interactive setting, challenges are derived deterministically from the prover's commitments via a collision-resistant hash (Fiat-Shamir transform @C:FiaSha86), preserving the same guarantee without interaction.

To apply this idea to bus balancing, we first need to compress each multi-element message $bold(e)(r)$ into a single field element.

#definition(title: "Compressed Interaction Value")[
  Given an interaction $(b, m, bold(e))$ of length $ell$ and a challenge $gamma in KK$, the _compressed value_ at row $r$ is:
  $
    hat(e)(r) = b + sum_(j=1)^(ell) gamma^j dot e_j (r)
  $
  The bus identifier $b$ is included to prevent cancellation across different buses.
] <def:compressed-interaction-value>

After compression, LogUp defines an auxiliary column to account for the sum. For each AIR $cal(A)_i$ with trace of length $N_i$ and set of interactions $cal(I)_i$, the contributions of all its interactions to the bus are accumulated row by row into a _partial sum_ $S_i$, defined by the recurrence:
$
  S_i (r) = cases(
    display(sum_((b, m, bold(e)) in cal(I)_i) frac(m(1), alpha + hat(e)(1)))\, & " if" r = 1,
    display(S_i (r-1) + sum_((b, m, bold(e)) in cal(I)_i) frac(m(r), alpha + hat(e)(r)))\, & " if" r > 1,
  )
$
The final value $s_i = S_i (N_i)$ is the AIR's total signed contribution to the bus. Global bus balancing then reduces to a single scalar constraint:
$
  sum_(i=1)^k s_i = 0
$
This constraint is enforced at the aggregation level: individual AIR proofs expose $s_i$ as a public output, and the aggregation step verifies that they sum to zero (see @sec:recursion).

== Circuits <sec:circuits-and-balancing>

Similar to @OPENVM, we define a _circuit_ as a collection of AIRs that, together with interactions, represents a complete computation.

#definition(title: "Circuit")[
  A _circuit_ is a collection of pairs $cal(C) := {(cal(A)_i, cal(I)_i)}_(i=1)^k$, where each $cal(A)_i$ is an AIR with its own parameters $(W_i, D_i, V_i)$ and each $cal(I)_i$ is a set of interactions for $cal(A)_i$.

  A _witness_ for $cal(C)$ is a collection of witnesses ${(bold(T)_i, bold(a)_i)}_(i=1)^k$ for each AIR $cal(A)_i$, with $bold(T)_i in FF^(N_i times W_i)$ and $bold(a)_i in FF^(V_i)$, where the trace heights $N_i$ may differ across AIRs.
]

The fact that each AIR carries its _own_ trace height $N_i$ is a deliberate design choice and one of the main reasons for organising a computation as a circuit rather than as a single monolithic AIR. Different AIRs typically encode different units of work with different natural sizes ---one AIR may scale with the length of the program being proved, another with the number of times a particular operation is invoked, and another with the size of a fixed lookup table--- and there is no reason for these sizes to coincide. Forcing all AIRs to share a common height would either pad the cheap ones with empty rows or truncate the expensive ones below their needs, both of which translate directly into wasted prover work. Allowing per-AIR heights instead lets each AIR be sized to its true workload, so the prover only pays for what each unit actually does. This independence is also what later makes per-AIR mechanisms such as continuations (@sec:continuations) possible without affecting the rest of the circuit.

A _bus_ is a communication channel that connects all interactions sharing the same bus identifier $b$. Through the bus, different AIRs exchange data by sending and receiving interactions. The set of all bus identifiers in a circuit $cal(C)$ is denoted $cal(B) = {b : exists i, (b, m, bold(e)) in cal(I)_i}$.

The key consistency condition is _bus balancing_: the total flow of values across each bus must sum to zero when weighted by multiplicities.

#definition(title: "Bus Balancing")[
  Given a circuit $cal(C) = {(cal(A)_i, cal(I)_i)}_(i=1)^k$ with associated witnesses ${(bold(T)_i, bold(a)_i)}_(i=1)^k$, a bus $b in cal(B)$ is _balanced_ if:
  $
    sum_(i=1)^k sum_((b, m, bold(e)) in cal(I)_i) sum_(r=1)^(N_i) m(r) dot hat(e)(r) = 0,
  $
  where $hat(e)(r)$ is the compressed interaction value for the interaction at row $r$ from @def:compressed-interaction-value.
] <def:bus-balancing>

Bus balancing ensures coherent communication: every message sent must be received with matching content, and no message can be invented or dropped. Together, local constraint satisfaction and global bus balancing give the full notion of circuit satisfiability: a circuit is satisfied when every AIR accepts its witness and every bus is balanced.

#definition(title: "Circuit Satisfiability")[
  A circuit $cal(C) = {(cal(A)_i, cal(I)_i)}_(i=1)^k$ is _satisfied_ by witnesses ${(bold(T)_i, bold(a)_i)}$ if:
  + Each witness $(bold(T)_i, bold(a)_i)$ satisfies its corresponding AIR $cal(A)_i$.
  + Every bus $b in cal(B)$ is balanced.
]
