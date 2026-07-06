#import "../../lib.typ": definition, remark

The single structural change from a univariate STARK is how the trace is read. Instead of interpolating each column on a multiplicative subgroup, we regard it as a function on the Boolean hypercube and take its multilinear extension.

== Columns as Multilinear Polynomials

#definition(title: "Multilinear Extension and Equality Kernel")[
  Let $T_j : [N] arrow FF$ be a trace column with $N = 2^n$. Its _multilinear extension_ (MLE) is the unique polynomial $tilde(T)_j in FF[X_1, dots, X_n]$ of individual degree $lt.eq 1$ in each variable such that
  $
    tilde(T)_j (bold(b)) = T_j (r_bold(b)) quad "for every" b in \{0,1\}^n,
  $
  where $r_bold(b)$ is the row index whose bit decomposition is $bold(b)$.

  It is given explicitly by
  $
    tilde(T)_j (bold(X)) = sum_(bold(b) in {0,1}^n) T_j (r_bold(b)) dot "eq"(bold(b), bold(X)),
  $
  where $"eq"$ is the _equality kernel_, the multilinear indicator of $bold(X) = bold(Y)$ on the hypercube; that is:
  $
    "eq"(bold(X), bold(Y)) = product_(i=1)^n bracket.l X_i Y_i + (1 - X_i)(1 - Y_i) bracket.r,
  $
]

The map $T_j arrow.r.bar tilde(T)_j$ is a bijection between columns (functions $[N] arrow FF$) and $n$-variate multilinear polynomials: both spaces have dimension $N = 2^n$. This is the multilinear analogue of "a degree-$(< N)$ univariate is determined by its values on $N$ points", and it is the only sense in which the trace is reinterpreted; the AIR and its constraints are untouched.

== Shifted Columns and the Rotation Kernel

An AIR of depth $D$ references not only $T_j (r)$ but the shifted values $T_j (r + k)$ for $0 lt.eq k lt.eq D$, with the row index taken modulo $N$. The shifted column $T_j^((k)) : r arrow.r.bar T_j (r + k)$ has its own MLE $tilde(T)_j^((k))$.

#definition(title: "Rotation Kernel")[
  For an offset $k$, let $phi_k : {0,1}^n arrow {0,1}^n$ be the bijection that increments a bit-address by $k$ modulo $2^n$ (so $phi_k (bold(r)) = bold(r + k)$). The _rotation kernel_ is the bivariate polynomial, multilinear in $bold(Y)$,
  $
    "rot"_k (bold(x), bold(Y)) = "eq"(bold(x), phi_k (bold(Y))),
  $
  and it satisfies, for every column $T_j$,
  $
    tilde(T)_j^((k)) (bold(Y)) = sum_(bold(x) in {0,1}^n) tilde(T)_j (bold(x)) dot "rot"_k (bold(x), bold(Y)).
  $
  Incrementing by $k$ ripples a binary carry, so $"rot"_k$ is $"eq"$ composed with that carry chain; for $k = 0$ it degenerates to $"eq"$.
]

Because the increment is a carry ripple rather than a clean coordinate map, evaluating $"rot"_k (dot, bold(z))$ at a point $bold(z)$ is not a single coordinate substitution; it is computed in $O(n)$ by a two-state dynamic program over the carry bit. The consequence is what matters: a depth-$D$ AIR commits only its $W$ base columns, and every shifted reference $T_j (r + k)$ becomes an evaluation of the _same_ committed $tilde(T)_j$ against a verifier-computable kernel.

== Column Categories and AIR Values

The whitepaper's three column categories map onto the backend as follows. _Fixed_ columns are committed once at setup and summarized in $sans("vk")$. _Cached_ columns are committed once and reused; the backend treats each cached commitment as an additional fixed matrix whose root is bound into the transcript. _Witness_ columns are committed per instance. The value vector $bold(a) in FF^(V)$ is not indexed by row; each $a_j$ enters constraints as the constant $Y_j$, and---crucially for the circuit-level argument---the components of $bold(a)$ that a stage $gt.eq 2$ argument produces (notably a partial bus sum $s$) are exposed as part of the instance's public output.

== Constraint Satisfaction as Vanishing on the Hypercube

Substituting the MLEs into a constraint gives a polynomial in $bold(X)$. Writing $bold(tilde(T))(bold(X))$ for the tuple of all base and shifted column MLEs evaluated at $bold(X)$, define the _composed constraint_
$
  accent(C, hat)_i (bold(X)) = C_i (bold(tilde(T))(bold(X)), a_1, dots, a_V).
$
Its individual degree may exceed $1$ (a multiplication gate multiplies columns), so it is generally not multilinear. The witness satisfies $cal(A)$ if and only if every composed constraint vanishes at every hypercube point:
$
  accent(C, hat)_i (bold(b)) = 0 quad "for all" bold(b) in {0,1}^n "and all" i in I.
$
This is $abs(I) dot N$ scalar conditions. The zerocheck PIOP (@sec:zerocheck) collapses them into a single sumcheck.
