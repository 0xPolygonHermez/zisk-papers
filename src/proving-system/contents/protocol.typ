#import "../../lib.typ": definition, remark

We now assemble the pieces into the protocol that produces one basic proof, and state what it attests.

== Transcript Schedule

The proof is made non-interactive by Fiat--Shamir @C:FiaSha86 over a Poseidon2 sponge @AFRICACRYPT:GraKhoSch23; the same hash instantiates the Merkle trees. The prover and verifier maintain a common transcript, and every challenge is squeezed from it after the messages it must depend on have been absorbed. For an $n = log_2 N$ instance of AIR $cal(A)_tau$ with $sigma$ stages of witness columns:

#[
  #set enum(numbering: "1.")
  + Absorb the statement: the AIR identifier $tau$, the public inputs $bold(p)$, and the fixed/cached commitments from $sans("vk")$.
  + Absorb the stage-$1$ witness commitment. Absorb the stage challenges; for a single instance in isolation these are inputs, not squeezed here.
  + Absorb the remaining stage commitments and the AIR values $bold(a)$ (prover messages, bound before any zerocheck randomness).
  + Squeeze the zerocheck randomness $bold(r) in KK^n$ and the constraint-batching challenge $mu in KK$.
  + Run the zerocheck: for $t = 1, dots, n$, absorb the round polynomial $g_t$ and squeeze $lambda_t$.
  + Absorb the claim matrix $(v_(j,i))$; squeeze the opening batching challenges $delta, gamma in KK$.
  + Run the opening: for each round, absorb the round polynomial and (until the last) the folded-oracle root, squeezing $lambda'_t$; absorb $Phi_"final"$.
  + Squeeze the $q$ query positions and answer them.
]

== The Proof Object

#definition(title: "Basic Proof")[
  A _basic proof_ $pi$ for an instance of $cal(A)_tau$ consists of: the witness-stage commitment roots and the cached-commitment roots; the AIR values $bold(a)$ (including the exposed bus contribution $s$) and the publics $bold(p)$; the zerocheck round polynomials $(g_t)_(t=1)^n$; the claim matrix $(v_(j,i))$; and the opening (opening round polynomials, folded-oracle roots, $Phi_"final"$, and the $q$ query openings with their Merkle paths).
]

== Verification

The verifier $V(sans("vk"), x, pi)$, with public statement $x = (bold(p), alpha, s)$, replays the transcript to re-derive every challenge and checks, in order: the claim matrix and round polynomials have the expected shapes; each zerocheck round satisfies $g_t (0) + g_t (1) = s_(t-1)$; the zerocheck final identity $s_n = "eq"(bold(r), bold(lambda)) dot sum_i mu^(i-1) C_i(dots)$ holds when the constraints are evaluated on the claimed openings; each boundary constraint vanishes on the claimed corner openings; the opening's final identity $sigma_n = tilde(Phi)(bold(lambda)') dot tilde(W)(bold(lambda)')$ holds; and every query's folding-consistency and Merkle checks pass against the roots.

== The Relation Attested

Collecting these, a basic proof attests exactly the AIR-leaf relation of the whitepaper:
$
  cal(R)_"AIR"^((tau)) = {
    (bold(p), alpha, s\; (bold(T), bold(a)))
    mid(|)
    (bold(T), bold(a)) "satisfies" cal(A)_tau, "consistent with" bold(p), and s = "BusCont"_alpha (cal(I)_tau, bold(T), bold(a))
  }.
$
The first conjunct is enforced by the zerocheck plus the boundary corner checks; consistency with $bold(p)$ is a family of first-row boundary constraints; and $s = "BusCont"_alpha (cal(I)_tau, bold(T), bold(a))$ is enforced as ordinary AIR constraints ---the LogUp partial-sum recurrence emitted by the standard library (the whitepaper's LogUp reduction)--- with the final value $s = S(N)$ exposed as an AIR value. The soundness-critical randomness $alpha$ (and its derived companion $gamma$) is supplied as a public input; how it is fixed across instances is the subject of the next section.
