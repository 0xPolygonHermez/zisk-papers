#import "../../shared/lib.typ": BusCont, definition, verifier, vk

A proving system is naturally divided into two layers. The _frontend_ takes a program and produces a structured mathematical representation---typically a system of polynomial constraints---that captures exactly what it means for the computation to be correct. The _backend_ then takes that representation and produces a cryptographic proof of its satisfiability. Concretely, the backend performs a one-time _setup_ that yields a pair $(sans("pk"), vk)$: a _proving key_ used to generate proofs of the frontend's constraint system, and a _verification key_ that summarizes the constraint system in a form the verifier can check against. Verification of a proof $pi$ against a public statement $x$ is then the deterministic procedure $verifier(vk, x, pi) in {"accept", "reject"}$. The two layers are decoupled by design: a single frontend can target different backends, and improvements to either do not require redesigning the other.

ZisK's _arithmetization framework_ is its frontend. The choice of arithmetization is consequential: it determines how computations are structured, what operations are native, and how efficiently the backend can prove them. ZisK's arithmetization is designed to be modular and flexible, capturing a wide range of computations while optimizing for the patterns that arise most frequently in zkVM execution.

The frontend is based on a generalization of the _algebraic intermediate representation (AIR)_ framework @EPRINT:BBHR18, which specifies polynomial constraints over a witness matrix, coupled with arguments such as LogUp @EPRINT:Habock22b, which extends AIR with logarithmic derivative-based lookups. A single AIR captures the behavior of one logical unit (e.g., the CPU, the ALU, or the memory). Since realistic computations involve multiple interacting units, we group AIRs together and define _interactions_ between them ---messages exchanged through shared communication channels called _buses_. This modular design has several advantages:
- *Separation of concerns*: Each AIR can be designed, implemented, and tested independently.
- *Composability*: AIRs can be reused across different computations or combined in different configurations.
- *Scalability*: Different AIRs can have different sizes, allowing resources to be allocated based on actual usage.
- *Backend independence*: The arithmetization can be paired with any compatible proving system.

The remainder of this section describes these concepts. Their formal definitions are those of the companion security analysis @ZISK:RECURSION, which this section follows.

== AIRs

An _algebraic intermediate representation_ (AIR) @EPRINT:BBHR18 is a finite set of polynomial _constraints_ over the columns of a trace, each read at a fixed set of row offsets, and over a vector of _AIR values_: field elements attached to the instance rather than to a row. A _witness_ is a trace $bold(T) in FF^(N times W)$, of a height $N$ that is a power of two, together with its AIR values; it _satisfies_ the AIR if every constraint vanishes at every row, row indices being taken modulo $N$. AIR values are a non-standard but necessary extension: they express instance-wide constants, such as the index of a segment, as first-class citizens of the constraint system rather than as workarounds encoded in the trace. The constraints of a ZisK AIR have coefficients in the Goldilocks field $FF$, and its trace and values lie in $FF$; the proving system extends them over the cubic extension $KK$ to realize the interactions (@sec:logup-reduction).

Not all columns in a trace have the same lifecycle. Some are fully determined by the program before any execution begins; others depend on the specific inputs provided; and others are intermediate values the prover computes but need not reveal. Distinguishing these cases allows the proving system to avoid redundant work ---a column that is the same across all executions of a program need only be committed once--- and to be precise about what the verifier is entitled to see. Trace columns are therefore partitioned into three categories according to when they are determined and who can access them:

- *Fixed*: Determined at setup time, independent of any particular execution. Fixed columns are shared with the verifier as part of the AIR's description; when an AIR has fixed columns, the trace height $N$ is also fixed at setup. Typical uses include lookup tables and instruction encodings.

- *Cached*: Computed by the prover and committed once, then reused across multiple executions of the same program. Cached columns capture data that depends on the program but not on its inputs ---such as the ROM instruction trace--- avoiding redundant recomputation.

- *Witness*: Computed fresh for each execution and not revealed to the verifier. These columns carry the execution-specific state: operation values, memory accesses, and all intermediate values produced during a run.

== Interactions and Buses <sec:interactions>

A single AIR is self-contained: its constraint polynomials relate columns within the same trace and cannot reference columns of another AIR. Yet realistic computations are inherently cross-cutting ---the CPU must read values that the memory has written, and a hash precompile must receive inputs from and return outputs to the main execution trace. To express these relationships without merging all AIRs into one monolithic constraint system, we introduce _interactions_: row-level messages that one AIR sends and another receives, mediated by a shared channel called a _bus_. An interaction specifies which values are communicated at each row and with what multiplicity; consistency across AIRs is then enforced by requiring that every bus is _balanced_ ---the total signed flow of messages sums to zero.

An _interaction_ of an AIR is a tuple $(b, m, bold(e))$ of a _bus identifier_ $b in FF$, a _multiplicity_ $m$ and a _message_ $bold(e) = (e_1, dots, e_ell)$, the last two polynomials in the variables of the AIR. Evaluated on a witness at row $r$, they give $m(r) in FF$ and $bold(e)(r) in FF^ell$, and the interaction puts the message $bold(e)(r)$ on the bus $b$ with multiplicity $m(r)$: positive when the AIR proves the message and negative when it assumes it, in the sense of @sec:bus-meaning. A _bus_ is the set of interactions that share a bus identifier, and all the interactions on a bus have the same message length.

The fundamental consistency condition is that every bus is _balanced_: over all the AIR instances of a proof, together with the _global messages_ that the system adds as a function of the public statement (@sec:zisk-statement), the signed multiplicities of every message on every bus add up to zero. Nothing is sent that is not received, and vice versa. As stated, the condition ranges over an exponentially large set of candidate messages and is impractical to check directly; arguments and LogUp turn it into a small set of polynomial constraints. Interactions and bus balancing define the communication structure, but not what semantic relationship is enforced: that is the role of arguments, and the meaning of each bus of ZisK is given in @sec:bus-meaning.

== Arguments <sec:arguments>

_Arguments_ are the semantic tools used to specify what consistency must hold across bus interactions: a permutation argument asserts that two multisets are equal or a lookup argument asserts containment in a table. Each argument type is realized as a pair of interactions on a shared bus ---one AIR proving messages with positive multiplicity, another assuming them with negative multiplicity--- so that bus balancing becomes equivalent to the desired relationship holding. A detailed description of the specific arguments used in ZisK is provided in @appendix:arguments.

Bus balancing is therefore the unified consistency condition underlying all arguments. However, checking it naively ---summing over every row of every AIR--- requires the verifier to process the full witness, defeating succinctness. We use _LogUp_ @EPRINT:Habock22b to reduce bus balancing to a small set of polynomial constraints that the backend can verify efficiently. The reduction proceeds in two steps: first, compress each multi-element message into a single field element; then, express the balancing sum as a polynomial identity checkable at a random location.

=== LogUp Reduction <sec:logup-reduction>

The key insight of LogUp is that multiset equality can be recast as a rational identity over a random challenge. Two multisets $S$ and $R$ (with multiplicities below $p$) are equal if and only if
$
  sum_(s in S) frac(1, X + s) = sum_(r in R) frac(1, X + r)
$
as rational functions in $X$. Evaluating both sides at a random _challenge_ $alpha$ detects a difference except with probability at most $(abs(S) + abs(R)) \/ abs(KK)$.
Here, by _challenge_ we refer to a random field element sent by the verifier after the prover has committed to its witness; because the prover cannot predict it before committing, the challenge breaks any attempt to craft a witness that satisfies the identity by accident. In the non-interactive setting, challenges are derived deterministically from the prover's commitments via a collision-resistant hash (Fiat–Shamir transform @C:FiaSha86), preserving the same guarantee without interaction.

To apply this idea to bus balancing, we first need to compress each multi-element message $bold(e)(r)$ into a single field element. This compression itself uses a second challenge $gamma in KK$. The two challenges are derived together: the pair $chi = (alpha, gamma) in KK^2$, which we call the _key_ of the bus argument, is a single Fiat–Shamir output that becomes available only after the witness has been committed (@sec:challenge-derivation).

#definition(title: "Compressed Interaction Value")[
  Given an interaction $(b, m, bold(e))$ of length $ell$ and a challenge $gamma in KK$, the _compressed value_ at row $r$ is:
  $
    hat(e)(r) = b + sum_(j=1)^(ell) gamma^j dot e_j (r)
  $
  The bus identifier $b$ is included to prevent cancellation across different buses.
] <def:compressed-interaction-value>

After compression, LogUp defines an auxiliary column to account for the sum. For each AIR instance $i$ of a proof, with AIR $cal(C)_i$, trace of length $N_i$ and set of interactions $cal(I)_i$, the contributions of all its interactions to the bus are accumulated row by row into a _partial sum_ $S_i$, defined by the recurrence:
$
  S_i (r) = cases(
    display(sum_((b, m, bold(e)) in cal(I)_i) frac(m(0), alpha + hat(e)(0)))\, & " if" r = 0,
    display(S_i (r-1) + sum_((b, m, bold(e)) in cal(I)_i) frac(m(r), alpha + hat(e)(r)))\, & " if" r > 0,
  )
$
The final value $s_i = S_i (N_i - 1)$ is the instance's total signed contribution to the bus. We call it the _bus contribution_ of the witness under the key $chi$ and write
$
  s_i = BusCont_chi (cal(I)_i, (bold(T)_i, bold(a)_i)).
$
Global bus balancing then reduces to a single scalar constraint, summed over all the AIR instances of the proof:
$
  sum_i s_i + s_"glob" = 0,
$
where $s_"glob"$ is the same LogUp sum taken over the _global messages_: messages that no AIR emits but that the system as a whole adds to some buses, such as the anchors that open and close the continuation chains (@sec:continuation-bus). They are determined by the public statement, and @sec:zisk-statement lists them. The bus contribution is computed in the extension field $KK$ of the challenges; the exact columns and constraints that compute it are those of @ZISK:RECURSION, which also accounts for the keys at which a denominator vanishes. This constraint is enforced at the aggregation level: individual AIR proofs expose $s_i$ in their statement, and the recursion verifies that they sum, together with $s_"glob"$, to zero (see @sec:recursion).

== Chips <sec:circuits-and-balancing>

A _chip_ is an AIR together with its set of interactions. ZisK is a fixed family of chips
$
  frak(A) = {(cal(C)_tau, cal(I)_tau)}_(tau in [M]),
$
listed in @tbl:chip-inventory, whose index $tau$ is the _type_ of the chip. When the design of @sec:design groups several AIRs under one name, such as the three AIRs of the Memory chip, the formal objects remain the AIRs, each with its interactions.

Each chip carries its _own_ trace height $N_tau$. This is a deliberate design choice and one of the main reasons for organizing a computation as a family of chips rather than as a single monolithic AIR. Different AIRs typically encode different units of work with different natural sizes ---one AIR may scale with the length of the program being proved, another with the number of times a particular operation is invoked, and another with the size of a fixed lookup table--- and there is no reason for these sizes to coincide. Forcing all AIRs to share a common height would either pad the cheap ones with empty rows or truncate the expensive ones below their needs, both of which translate directly into wasted prover work. Allowing per-AIR heights instead lets each AIR be sized to its true workload, so the prover only pays for what each unit actually does. This independence is also what makes per-AIR mechanisms such as continuations (@sec:continuations) possible without affecting the rest of the system.

A collection of witnesses, with any number of witnesses of each type, _satisfies_ the family if every witness satisfies the AIR of its type and every bus is balanced, counting the global messages of the public statement. This is what the recursion of @sec:recursion establishes about the AIR instances of a proof, and the security analysis @ZISK:RECURSION states it as a relation.
