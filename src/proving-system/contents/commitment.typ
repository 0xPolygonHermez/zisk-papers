#import "../../lib.typ": definition, remark

The prover commits each column with #smallcaps[Basefold] @EPRINT:ZCF23, a polynomial commitment scheme for multilinears built from a foldable Reed--Solomon code. We fix a rate parameter $kappa gt.eq 1$ (the log-blowup) and write $rho = 2^(-kappa)$ for the code rate.

== The Univariate--Multilinear Bijection

Basefold commits a multilinear by committing an equivalent univariate. Order the $2^n$ multilinear monomial coefficients of $tilde(T)_j$ into a vector $bold(c) in FF^(2^n)$ (the Möbius transform of the column values), and form the univariate
$
  hat(g)_j (X) = sum_(i=0)^(2^n - 1) c_i X^i, quad "so that" quad hat(g)_j (x) = tilde(T)_j (x^(2^0), x^(2^1), dots, x^(2^(n-1))).
$
This is a bijection between $n$-variate multilinears and univariates of degree $< 2^n$. The point of using the _coefficient_ form is the folding identity below.

== Encoding and Merkle Commitment

#definition(title: "Column Commitment")[
  Let $g$ be a coset generator and $H$ a multiplicative subgroup with $abs(H) = 2^(n + kappa)$. The _Reed--Solomon codeword_ of column $T_j$ is the evaluation vector $(hat(g)_j (g dot omega))_(omega in H) in FF^(2^(n+kappa))$. The _commitment_ to $T_j$ is the Merkle root of this codeword. A stage (a group of columns committed together) is committed by one Merkle tree whose leaf at position $ell$ holds the values of all the stage's codewords at the paired points $ell$ and $ell + abs(H) slash 2$.
]

Pairing $ell$ with $ell + abs(H) slash 2$ per leaf is deliberate: these two positions map to $x$ and $-x$, which is exactly the pair a folding-consistency check reads, so a query opens one leaf per tree. The verification key $sans("vk")$ is the tuple of commitments to the fixed and cached columns; per-instance witness stages are committed by the prover and their roots travel in the proof.

== Folding is Partial Evaluation

The mechanism that makes Basefold an _evaluation_ scheme, and not merely a low-degree test, is that one folding step of the codeword equals binding one variable of the multilinear.

#definition(title: "Fold")[
  For $lambda in KK$, the _fold_ of a codeword $f$ on the domain $g H$ maps $g H arrow (g H)^2$ (half the size) by
  $
    "Fold"(f, lambda)(x^2) = frac(f(x) + f(-x), 2) + lambda dot frac(f(x) - f(-x), 2 x).
  $
]

If $f$ is the codeword of $tilde(T)_j$, then $"Fold"(f, lambda)$ is the codeword of $tilde(T)_j (lambda, X_2, dots, X_n)$: folding with $lambda$ fixes the first variable to $lambda$. Equivalently, in the coefficient form, folding is $c'_i = c_(2 i) + lambda dot c_(2 i + 1)$. Iterating $n$ folds with challenges $lambda_1, dots, lambda_n$ collapses the codeword to the single scalar $tilde(T)_j (lambda_1, dots, lambda_n)$. This is the identity every multilinear PCS in the #smallcaps[Basefold]/#smallcaps[WHIR] @EPRINT:ACFY24 family turns on, and it is what lets an evaluation proof be produced by folding rather than by a separate opening argument.
