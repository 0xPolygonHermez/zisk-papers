#import "../lib.typ": Bind, Commit, Local, definition

#definition(title: "AIR and Witness")[
  An _algebraic intermediate representation_ (AIR) of width $W$, depth $D$ and
  $V$ values is a finite set of _constraint polynomials_
  $
    cal(C) subset FF[X_1^((0)), dots, X_W^((0)), dots, X_1^((D)), dots, X_W^((D)), Y_1, dots, Y_V].
  $
  A _witness_ of height $N$ for $cal(C)$ is a pair
  $w = (bold(T), bold(a))$ with $bold(T) in FF^(N times W)$, the _trace_, and
  $bold(a) in FF^V$, the _AIR values_. At row $r in [N]$ the variable
  $X_j^((k))$ takes the value $T_j (r + k)$, with row indices taken modulo
  $N$, and $Y_j$ takes the value $a_j$. The witness _satisfies_ $cal(C)$ if
  every constraint polynomial evaluates to zero at every row.
] <def:air>

#definition(title: "Interaction")[
  An _interaction_ of an AIR $cal(C)$ on the bus $b in FF$ is a tuple
  $iota = (b, m_iota, bold(e)_iota)$, where the _multiplicity_ $m_iota$ and
  the _message_ components $e_(iota, 1), dots, e_(iota, ell_b)$ are
  polynomials over $FF$ in the variables of $cal(C)$. Given a witness $w$ and a row
  $r$, we write $m_iota (w, r) in FF$ and $bold(e)_iota (w, r) in FF^(ell_b)$
  for their evaluations at row $r$. The set of bus identifiers in use is
  $cal(B)$; every interaction on bus $b$ has the common message length
  $ell_b$, and $ell := max_(b in cal(B)) ell_b$.
] <def:interaction>

Throughout, we fix a positive integer $M$ and an indexed family of
_AIR types_
$
  frak(A) = { (cal(C)_tau, cal(I)_tau) }_(tau in [M]),
$
where each $cal(C)_tau$ is an AIR of width $W_tau$, depth $D_tau$ and $V_tau$
values and $cal(I)_tau$ is a finite set of interactions of $cal(C)_tau$. Given a fixed trace height $N_tau$, we write $cal(W)_tau := FF^(N_tau times W_tau) times FF^(V_tau)$ for
the witness space of type $tau$ and fix the public-statement space
$cal(P) := FF^k$.

#definition(title: "Column Classes and Public Bindings")[
  The description of an AIR $cal(C)$ of width $W$ and $V$ values, used at
  height $N$, partitions its column indices as
  $[W] = J^"fix" union.sq J^"cach" union.sq J^"wit"$ and carries:
  + The _fixed columns_ $J^"fix"$, whose values are prescribed as part of the
    description of $cal(C)$ and hence known to both the prover and the verifier.
  + The _cached columns_ $J^"cach"$, whose values are computed once and
    reused across different proofs. Their values are not part of the
    description; instead, a commitment to them (@def:commitment) travels in the public statement at the coordinates designated
    by a _cached-commitment binding_ $gamma : [m] -> [k]$.
  + The _witness columns_ $J^"wit"$, computed afresh for every proof and
    only known in full to the prover.
  + A _public binding map_ $beta : "dom"(beta) -> [k]$ from a set
    $"dom"(beta) subset [V]$ to coordinates of the public statement.
  The _prescribed data_ of $cal(C)$ is the family
  $bold(d) = (d_j)_(j in J^"fix")$ of fixed columns $d_j in FF^N$. For a
  trace $bold(T)$ and a set of columns $J$ we write $bold(T)|_J$ for the
  submatrix of the columns in $J$.
] <def:columns>

Each AIR type carries this data; we index it by the type, as in
$J^"fix"_tau$, $bold(d)_tau$ and $beta_tau$.

#definition(title: "Local Satisfaction")[
  For $tau in [M]$, $bold(p) in cal(P)$ and $w = (bold(T), bold(a)) in cal(W)_tau$,
  the predicate $Local_tau (bold(p), w)$ holds if and only if
  + $w$ satisfies $cal(C)_tau$.
  + $bold(T)$ agrees with the prescribed data on the fixed columns:
    $T_j (r) = d_(tau, j)(r)$ for every $j in J^"fix"_tau$ and $r in [N_tau]$.
  + $Bind_tau (bold(p), w)$: $a_j = p_(beta_tau (j))$ for every
    $j in "dom"(beta_tau)$.
  + The cached columns open the commitment carried in $bold(p)$:
    $ Commit_"cach" (bold(T)|_(J^"cach"_tau)) = (p_(gamma_tau (1)), dots, p_(gamma_tau (m))). $
] <def:local>
