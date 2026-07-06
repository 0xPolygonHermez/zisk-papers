#import "../../lib.typ": definition, remark

The zerocheck is the polynomial interactive oracle proof (PIOP) that certifies the $abs(I) dot N$ pointwise conditions of @sec:mle with a single sumcheck. It is the multilinear counterpart of the univariate quotient check.

== Batching Constraints and the eq Trick

Two independent reductions collapse the conditions. First, all constraints are batched with a challenge $mu in KK$ into
$
  C_mu (bold(X)) = sum_(i in I) mu^(i-1) accent(C, hat)_i (bold(X)),
$
sampled after the trace is committed. Batching does not raise the degree: $deg C_mu = max_i deg accent(C, hat)_i$. Second, a single constraint vanishes on the whole cube if and only if its multilinear extension is the zero polynomial, which is caught at a random point:

#definition(title: "Zerocheck")[
  For a challenge point $bold(r) in KK^n$, define
  $
    G(bold(X)) = "eq"(bold(r), bold(X)) dot C_mu (bold(X)).
  $
  Then $accent(C, hat)_i (bold(b)) = 0$ for all $bold(b) in {0,1}^n$ and all $i$ implies $sum_(bold(b) in {0,1}^n) G(bold(b)) = 0$; conversely, if some constraint is violated, then over the random draw of $(bold(r), mu)$ the sum is non-zero except with probability $O((abs(I) + n) slash abs(KK))$ by Schwartz--Zippel.
]

The quantity $sum_(bold(b)) G(bold(b))$ is precisely the multilinear extension of $C_mu|_{"cube"}$ evaluated at $bold(r)$, which is why a single random $bold(r)$ suffices. Both $bold(r)$ and $mu$ are drawn, by Fiat--Shamir @C:FiaSha86, after all commitments.

== Running the Sumcheck

The sumcheck @JACM:LFKN92 proves $sum_(bold(b)) G(bold(b)) = 0$ in $n$ rounds. In round $t$, with challenges $lambda_1, dots, lambda_(t-1)$ fixed, the prover sends the univariate round polynomial
$
  g_t (Z) = sum_(bold(b) in {0,1}^(n-t)) G(lambda_1, dots, lambda_(t-1), Z, bold(b)),
$
of degree $d = deg C_mu + 1$ (the $+1$ is the $"eq"$ factor). It is transmitted as its evaluations at $Z = 0, 1, dots, d$. The verifier checks $g_t (0) + g_t (1) = s_(t-1)$ (with $s_0 = 0$ and $s_t = g_t (lambda_t)$) and replies with a fresh $lambda_t in KK$. After $n$ rounds the claim is the single value $G(bold(lambda))$ at $bold(lambda) = (lambda_1, dots, lambda_n)$.

The prover evaluates the round polynomials by running the AIR's constraint expression over the partially bound column tables; the round degree, and hence prover cost per row, is set by the highest-degree gate. Because the composed constraint is evaluated at $d + 1$ points per pair rather than committed, a high-degree gate costs field work linear in $d$ and never a larger commitment (this is the multilinear analogue of high-degree custom gates being cheap @EPRINT:CBBZ22; further round-polynomial savings are possible @EPRINT:Gruen24).

== From the Final Claim to Evaluation Claims

To discharge $G(bold(lambda))$ the verifier needs to reconstruct it. It computes $"eq"(bold(r), bold(lambda))$ itself and knows $mu$ and how each $C_i$ is built from the columns, so it can assemble $G(bold(lambda)) = "eq"(bold(r), bold(lambda)) dot sum_i mu^(i-1) C_i(dots)$ once it is told each _committed column value the constraints reference at $bold(lambda)$_. These are the evaluation claims:
$
  underbrace(tilde(T)_1 (bold(lambda)) \, dots \, tilde(T)_W (bold(lambda)), "current-row openings")
  quad
  underbrace(tilde(T)_j^((k)) (bold(lambda)) " for each " j\, k, "shifted-row openings, via" "rot"_k).
$
By the rotation identity each shifted evaluation reduces to an evaluation of the _base_ column $tilde(T)_j$ against the kernel $"rot"_k (dot, bold(lambda))$. No matter how many constraints or offsets an AIR has, the backend reduces to a set of "open this committed column at this point" claims against the $W$ base columns only.

// == Boundary Constraints

// Constraints that must hold only on the first or last row (the whitepaper's boundary conditions, e.g. binding a public to row $0$) never enter the sumcheck. A first-row constraint reduces to an evaluation claim at the hypercube corner $bold(0)$ and a last-row constraint to the corner $bold(1) = (1, dots, 1)$; the verifier evaluates the constraint on the claimed corner openings directly. In the opening (@sec:opening) these corner claims are handled by the equality kernel $"eq"(dot, bold(0))$ (resp. $"eq"(dot, bold(1))$), a special case of the machinery already in place.
