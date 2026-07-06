#import "../../lib.typ": definition, remark

The zerocheck leaves a set of evaluation claims on the committed columns. Every such claim ---plain, shifted, or corner--- is a weighted sum over the hypercube against a verifier-computable kernel, and #smallcaps[Basefold] discharges them all with one batched opening.

== Claims as Weighted Sums

Each claim has the form $v = sum_(bold(b) in {0,1}^n) w_j (bold(b)) dot K(bold(b))$, where $w_j$ is a committed column and $K$ is a _kernel_ the verifier can evaluate at any point:
- a plain opening $tilde(w)_j (bold(lambda))$ uses $K = "eq"(dot, bold(lambda))$;
- a shifted opening $tilde(w)_j^((k)) (bold(lambda))$ uses the rotation kernel $K = "rot"_k (dot, bold(lambda))$;
- a corner claim $w_j (r)$ at a boundary row uses $K = "eq"(dot, bold(r))$.

Enumerate the committed columns $w_1, dots, w_L$ (witness stages, then fixed, then cached) and the distinct kernels $K_1, dots, K_m$. The prover sends the full matrix of claimed values $v_(j,i) = sum_bold(b) w_j (bold(b)) K_i (bold(b))$.

== Two-Level Batching

The verifier draws $delta, gamma in KK$ and forms a single random combination of columns and of kernels:
$
  Phi = sum_(j=1)^L delta^(j) w_j, quad
  W = sum_(i=1)^m gamma^(i) K_i, quad
  sigma = sum_(j,i) delta^(j) gamma^(i) v_(j,i).
$
Because $Phi dot W = sum_(j,i) delta^j gamma^i w_j K_i$, the batched claim $sum_(bold(b)) Phi(bold(b)) W(bold(b)) = sigma$ holds if and only if every $v_(j,i)$ is correct (the cross terms are why the _full_ matrix is sent, not only the entries the constraint check uses). The combined codeword of $Phi$ is the same $delta$-combination of the committed column codewords.

== Interleaved Sumcheck and Folding

#definition(title: "Basefold Opening")[
  To prove $sum_(bold(b)) Phi(bold(b)) W(bold(b)) = sigma$, run an $n$-round degree-$2$ sumcheck on the product $Phi dot W$. In round $t$ the verifier's challenge $lambda'_t$ is used _both_ to bind the sumcheck variable and to fold the codeword of $Phi$ one step (@sec:commitment). The intermediate folded oracles $Phi_1, dots, Phi_(L' - 1)$ are Merkle-committed and their roots absorbed into the transcript; after $L'$ folds the remaining polynomial is small and sent in the clear as its coefficient vector $Phi_"final"$.
]

The final sumcheck value must equal $tilde(Phi)(bold(lambda)') dot tilde(W)(bold(lambda)')$; the verifier computes $tilde(W)(bold(lambda)')$ itself (all kernels are $"eq"$/rotation kernels, evaluable in $O(n)$), and reads $tilde(Phi)(bold(lambda)')$ off $Phi_"final"$. This last check is what makes the claim matrix _binding_.

== Query Phase

Proximity to the code is enforced by repeated queries. The verifier derives $q$ query positions from the transcript; for each, it opens the stage commitments at the position (recovering $Phi$ at $x$ and $-x$ via the paired leaf), then walks the folding cascade, at each level checking the folding-consistency relation against the opened pair and its Merkle path, down to $Phi_"final"$. A prover that committed a word far from the code is rejected with probability growing in $q$; the number of queries is chosen for the target soundness at rate $rho$.
