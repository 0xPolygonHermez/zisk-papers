#import "../../lib.typ": (
  Balanced, BusCont, Com, Commit, DeriveAlpha, Local, accept, definition, mult, negl, poly, remark, vk,
)

This section fixes the notation used in the security analysis and restates,
in the exact form the proofs consume, the objects introduced in the ZisK
whitepaper: the arithmetization layer (AIRs, interactions and buses), the
cryptographic components of the recursion (trace commitments, the multiset
hash and challenge derivation), and the four relations attested by the nodes
of the aggregation tree. This document compiles independently of the
whitepaper, so nothing is assumed from there. Where a relation below differs
from the whitepaper text, the difference is deliberate; all such differences
are collected in @rem:deviations.

== Notation and Parameters

$FF$ is a prime field of order $p$ (Goldilocks, $p = 2^64 - 2^32 + 1$) and
$KK$ is its cubic extension, $abs(KK) = p^3$. $ZZ_p^n$ denotes the additive
group of $n$-vectors of integers modulo $p$, the same set as $FF^n$ viewed as
a $ZZ$-module. For integers $a <= b$, $[a, b]$ and $[a, b)$ are the closed and
half-open integer intervals and $[b] := [1, b]$. Field elements are identified
with integers in $[0, p)$ when needed. $lambda$ is the security parameter;
"PPT" means probabilistic polynomial time in $lambda$, and
$negl(lambda)$ and $poly(lambda)$ denote negligible and polynomially bounded
functions. All algorithms have oracle access to the random oracles introduced
in @sec:components; $Q$ bounds the total number of oracle queries an adversary
makes.

The recursion is governed by one integer parameter, the _leaf-count exponent_
$B$: an aggregation tree may contain at most $2^B - 1$ leaves. We assume throughout that
$
  2^(B+1) <= p, quad 2^B < p, quad 2^B <= poly(lambda):
$
the first condition guarantees that sums of two range-checked counters never
wrap around in $FF$, the second is the cardinality restriction required by the
multiset hash, and the third makes the number of leaves, and hence the running
time of the extractor, polynomial.

== Arithmetization <sec:arithmetization>

#definition(title: "AIR and Witness")[
  An _algebraic intermediate representation_ (AIR) of width $W$, depth $D$ and
  $V$ values is a finite set of _constraint polynomials_
  $
    cal(A) subset FF[X_1^((0)), dots, X_W^((0)), dots, X_1^((D)), dots, X_W^((D)), Y_1, dots, Y_V].
  $
  A _witness_ of height $N$ for $cal(A)$ is a pair
  $w = (bold(T), bold(a))$ with $bold(T) in FF^(N times W)$, the _trace_, and
  $bold(a) in FF^V$, the _AIR values_. At row $r in [N]$ the variable
  $X_j^((k))$ takes the value $T_j (r + k)$, with row indices taken modulo
  $N$, and $Y_j$ takes the value $a_j$. The witness _satisfies_ $cal(A)$ if
  every constraint polynomial evaluates to zero at every row.
] <def:air>

#definition(title: "Interaction")[
  An _interaction_ of an AIR $cal(A)$ on the bus $b in FF$ is a tuple
  $iota = (b, m_iota, bold(e)_iota)$, where the _multiplicity_ $m_iota$ and
  the _message_ components $e_(iota, 1), dots, e_(iota, ell_b)$ are
  polynomials over $FF$ in the variables of $cal(A)$. Given a witness $w$ and a row
  $r$, we write $m_iota (w, r) in FF$ and $bold(e)_iota (w, r) in FF^(ell_b)$
  for their evaluations at row $r$. The set of bus identifiers in use is
  $cal(B)$; every interaction on bus $b$ has the common message length
  $ell_b$, and $ell := max_(b in cal(B)) ell_b$.
] <def:interaction>

Throughout, we fix a positive integer $M$ and an indexed family of
_AIR types_
$
  cal(C) = { (cal(A)_tau, cal(I)_tau) }_(tau in [M]),
$
where $cal(A)_tau$ is an AIR of width $W_tau$, depth $D_tau$ and $V_tau$
values, $cal(I)_tau$ is a finite set of interactions of $cal(A)_tau$. Given a fixed trace height $N_tau$, we write $cal(W)_tau := FF^(N_tau times W_tau) times FF^(V_tau)$ for
the witness space of type $tau$ and fix the public-statement space
$cal(P) := FF^k$.

#definition(title: "Local Satisfaction")[
  For $tau in [M]$, $bold(p) in cal(P)$ and $w = (bold(T), bold(a)) in cal(W)_tau$,
  the predicate $Local_tau (bold(p), w)$ holds if and only if
  + $w$ satisfies $cal(A)_tau$.
  + The fixed columns of $bold(T)$ equal the fixed data prescribed by
    $cal(A)_tau$ (cached columns, committed once at setup, are treated as fixed
    data whose commitment is part of the verification key of type $tau$).
  + $"Bind"_tau (bold(p), w)$: every trace cell and AIR value that
    $cal(A)_tau$ designates as a binding to the public statement equals the
    designated coordinate of $bold(p)$.
] <def:local>

The program being executed is not a separate parameter: the program ROM and
the boot state are bound through fixed and cached columns of the relevant AIR
types, hence through their verification keys. This plays the role of the
program code hard-wired into the step circuit of the reference architecture.

#definition(title: "Message multiset of a witness")[
  Let $cal(V) := {(b, v) : b in cal(B), v in FF^(ell_b)}$ be the set of
  _bus messages_. An _$FF$-weighted multiset_ of messages is a finitely
  supported map $D : cal(V) -> FF$; we write $abs(D)$ for the size of its
  support and add such maps pointwise. For $tau in [M]$ and $w in cal(W)_tau$,
  the _message multiset_ of $w$ is
  $
    "Msg"_tau (w)(b, v) := sum_(iota in cal(I)_tau, b_iota = b) sum_(r=1)^(N_tau) m_iota (w, r) dot bold(1)[bold(e)_iota (w, r) = v].
  $
  Its support has at most $N_tau dot abs(cal(I)_tau)$ elements.
] <def:msg>

A row that sends a message with positive multiplicity and a row of the same
witness that receives it with negative multiplicity cancel in
$"Msg"_tau (w)$: the multiset records the net flow of every message out of the
witness.

#definition(title: "Bus fingerprint")[
  A _bus fingerprint_ is a family $cal(F) = {cal(F)_chi}_(chi in KK^2)$ of
  maps from $FF$-weighted multisets of messages to $KK union {bot}$ such that
  + (_additivity_) $cal(F)_chi (0) = 0$, and
    $cal(F)_chi (D + D') = cal(F)_chi (D) + cal(F)_chi (D')$.
  + (_soundness_) there is a non-decreasing function $epsilon_(cal(F))$ such
    that for every $D != 0$ with $abs(D) <= Lambda$ and uniform $chi in KK^2$,
    $Pr_chi [cal(F)_chi (D) = 0] <= epsilon_(cal(F))(Lambda)$.
  The _bus contribution_ of $w in cal(W)_tau$ under the _challenge pair_
  $chi in KK^2$ is
  $
    BusCont_chi (cal(I)_tau, w) := cal(F)_chi ("Msg"_tau (w)) in KK.
  $
] <def:fingerprint>

A fingerprint is a keyed, additive summary of a multiset that vanishes on a
nonzero multiset only at few keys; it is to bus balancing what the multiset
hash $cal(H)$ of @sec:components is to challenge derivation. ZisK instantiates
it with LogUp @EPRINT:Habock22b: for $chi = (alpha, gamma)$ the message
$(b, v)$ is _compressed_ to
$hat(e)_gamma (b, v) := b + sum_(j=1)^(ell_b) gamma^j v_j in KK$ and
$
  cal(F)^"LogUp"_chi (D) := sum_((b, v) in "supp" D) frac(D(b, v), alpha + hat(e)_gamma (b, v)),
$
with $cal(F)^"LogUp"_chi (D) := bot$ if some denominator vanishes.
@lem:logup shows that this is a bus fingerprint with
$epsilon_(cal(F))(Lambda) = (ell dot binom(Lambda, 2) + Lambda - 1) slash abs(KK)$.
The AIR argument does not evaluate this closed form. It constrains a running
sum over the rows of the trace, adding
$m_iota (w, r) slash (alpha + hat(e)_gamma (b_iota, bold(e)_iota (w, r)))$ at
every row through an explicitly constrained inverse, and exposes the final
value $s$; this is the whitepaper's $S(N_tau)$. Grouping the row terms by
message shows that the exposed value equals
$cal(F)^"LogUp"_chi ("Msg"_tau (w))$ whenever every row denominator is
nonzero. The circuit therefore proves a sub-relation of
$cal(R)_"AIR"^((tau))$ below: it additionally rejects when a row of zero
multiplicity, or a pair of rows that cancel in the multiset, hits a pole. This
only strengthens the statements of @sec:security, since knowledge soundness
for a sub-relation implies knowledge soundness for the relation.

#definition(title: "Typed witness collection")[
  A _typed witness collection_ is a finite list
  $
    L = ((tau_1, w_1), dots, (tau_(abs(L)), w_(abs(L)))), quad tau_i in [M], quad w_i in cal(W)_(tau_i).
  $
  Types and witnesses may repeat, and each entry counts separately; the order
  of the list carries no meaning. The _number of bus terms_ of $L$ is
  $Lambda(L) := sum_(i=1)^(abs(L)) N_(tau_i) dot abs(cal(I)_(tau_i))$, and we set
  $Lambda_"max" := (2^B - 1) dot max_(tau in [M]) N_tau abs(cal(I)_tau)$, so
  that $Lambda(L) <= Lambda_"max"$ whenever $abs(L) < 2^B$.
] <def:collection>

#definition(title: "Balance of a witness collection")[
  The _signed multiplicity_ of a typed witness collection $L$ is the
  $FF$-weighted multiset
  $
    cal(M)_L := sum_(i=1)^(abs(L)) "Msg"_(tau_i)(w_i),
  $
  that is,
  $
    cal(M)_L (b, v) = sum_(i=1)^(abs(L)) sum_(iota in cal(I)_(tau_i), b_iota = b) sum_(r=1)^(N_(tau_i)) m_iota (w_i, r) dot bold(1)[bold(e)_iota (w_i, r) = v].
  $
  The collection is _balanced_, written $Balanced(L)$, if $cal(M)_L = 0$,
  i.e. $cal(M)_L (b, v) = 0$ for every bus $b in cal(B)$ and every message
  $v in FF^(ell_b)$. Note that $abs(cal(M)_L) <= Lambda(L)$.
] <def:balanced>

This is the whitepaper's bus-balancing condition extended from one witness
per AIR type to an arbitrary collection of instances. Its multiplicities are
field elements: $Balanced(L)$ does not by itself assert that every message is
sent and received the same number of times as integers, since $p$ copies of a
message cancel. We return to this point in @rem:integer-balance.

== Proof-System Components <sec:components>

A _non-interactive argument system_ for a relation $cal(R)$ is a pair
$Pi = (sans("Prove"), sans("Verify"))$ with a verification key $vk_Pi$
produced at setup; $sans("Verify")(vk_Pi, x, pi) in {accept, "reject"}$ is
deterministic. We write $V_X (x, pi) := sans("Verify")(vk_X, x, pi)$ for the
verifier of the system attesting to the relation $cal(R)_X$, and simply
$V(vk, x, pi)$ when the key is a variable. The recursion uses the following
components.

- *Trace commitment.* $Com$ is a deterministic commitment scheme with
  algorithm $Commit : union.big_tau cal(W)_tau -> {0, 1}^*$, built from a
  hash function modelled as a random oracle (a Merkle tree in ZisK). A
  commitment $"com" = Commit(bold(T), bold(a))$ covers every column of the
  trace and every AIR value; the auxiliary columns that the prover of an AIR
  argument adds for the LogUp running sums are internal to that argument and
  are not part of the witness. The argument system for an AIR type takes the
  challenge pair $chi$ as a public input, so the witness is
  challenge-independent.
- *Hash-to-group and multiset hash.* $h : [M] times {0,1}^* -> ZZ_p^n$ maps a
  _typed commitment_ $(tau, "com")$ to a group element, and
  $
    cal(H)(cal(S)) := sum_(x in cal(S)) mult_cal(S)(x) dot h(x) in ZZ_p^n
  $
  is the induced multiset hash on finite multisets $cal(S)$ of typed
  commitments, where $mult_cal(S)(x)$ is the multiplicity of $x$ in $cal(S)$.
  $cal(H)$ is additively homomorphic over multiset union, which is what lets
  the aggregation tree accumulate it. ZisK instantiates $h$ and $cal(H)$ with
  LtHash @ZISK:LTHASH @AC:CDDGS03, $n = 372$.
- *Challenge derivation.* $DeriveAlpha : ZZ_p^n -> KK^2$ maps an accumulated
  group element to a challenge pair $chi = (alpha, gamma)$. ZisK derives
  $alpha$ as a hash of the accumulator and $gamma$ as a hash of
  $alpha$; we treat the pair as a single oracle output, see
  @rem:deviations.
- *Argument systems.* For every type $tau in [M]$ an argument system
  $Pi_"AIR"^((tau))$ for $cal(R)_"AIR"^((tau))$ and one $Pi_"LEAF"^((tau))$
  for $cal(R)_"LEAF"^((tau))$; a single $Pi_"AGG"$ for $cal(R)_"AGG"$; and a
  single $Pi_"FINAL"$ for $cal(R)_"FINAL"$. The relations are defined in
  @sec:relations-def.

The verification keys involved play different roles, which the whitepaper
distinguishes only in prose; @tbl:vk-ledger records them.

#figure(
  table(
    stroke: 0.3pt,
    columns: (18%, 47%, 35%),
    align: (left, left, left),
    table.header([*Key*], [*Selected by*], [*Hard-coded in*]),
    [$vk_"AIR"^((tau))$], [the type $tau$ of the leaf verifier circuit], [$Pi_"LEAF"^((tau))$],
    [$vk_"LEAF"^((tau))$], [the child type $tau_X in [M]$ read from the child statement], [$Pi_"AGG"$ (all $M$ keys)],
    [$vk_"AGG"$], [the child type $tau_X = M + 1$; the key itself arrives as the public $vk$], [$Pi_"FINAL"$ only],
    [$vk_"FINAL"$], [---], [the external verifier],
  ),
  caption: [
    Verification-key ledger. The circuit type $tau$ selects which hard-coded
    key an aggregation node uses for a child; the propagated public $vk$ is
    the aggregation verifier's own key, which no aggregation circuit can
    hard-code and which the Final Verifier fixes.
  ],
  kind: table,
) <tbl:vk-ledger>

#definition(title: "Recursive dispatch")[
  For a type $tau in [M + 1]$ and a key $vk$, the _dispatched verifier_ is
  $
    V_"REC"^((tau)) [vk](x, pi) := cases(
      V_"LEAF"^((tau))(x, pi) & "if" tau in [M]\,,
      V(vk, x, pi) & "if" tau = M + 1\,,
    )
  $
  and $V_"REC"^((tau))[vk]$ rejects everything if $tau in.not [M + 1]$.
  The _typing predicate_ on a type and a counter is
  $
    sans("Typed")(tau, kappa) :<=> (tau in [M] and kappa = 1) or (tau = M + 1 and 2 <= kappa < 2^B).
  $
] <def:dispatch>

The dispatch is a function of the key $vk$ carried in the statement, not of
any fixed key. This is what removes the apparent circularity of a circuit
verifying proofs of itself: $cal(R)_"AGG"$ below is one ordinary relation over
statements that contain an arbitrary string $vk$; the key $vk_"AGG"$ of the
argument system for that relation is produced afterwards at setup; and
$cal(R)_"FINAL"$ fixes $vk := vk_"AGG"$, at which point
$V_"REC"^((M+1))[vk_"AGG"] = V_"AGG"$.

== Recursive Relations <sec:relations-def>

We write a relation as $cal(R) = { (x; w) mid(|) phi(x, w) }$ with public
statement $x$ and witness $w$. The _recursive statement_ carried by every node
of the tree is the tuple $sigma = (s, tau, kappa, bold(c))$ of a bus partial
sum $s in KK$, a type $tau in [M+1]$, a leaf counter $kappa in FF$ and a
challenge accumulator $bold(c) in ZZ_p^n$; we access its components as
$sigma . s$, $sigma . tau$ and so on.

#definition(title: "AIR relation")[
  For $tau in [M]$,
  $
    cal(R)_"AIR"^((tau)) = lr(
      {
        cases(
          delim: #none,
          ,
          (bold(p), chi\, s\, "com")\; (bold(T), bold(a)),
          ,
        )
        mid(|)
        cases(
          delim: #none,
          gap: #(0pt + 0.4em),
          Local_tau (bold(p), (bold(T), bold(a))),
          and quad s = BusCont_chi (cal(I)_tau, (bold(T), bold(a))),
          and quad Commit(bold(T), bold(a)) = "com"
        )
      }
    )
  $
  with $bold(p) in cal(P)$, $chi in KK^2$, $s in KK$ and
  $(bold(T), bold(a)) in cal(W)_tau$.
] <def:r-air>

The relation is in _commit-and-prove_ form: the trace commitment is part of
the statement. A STARK proof for $cal(A)_tau$ already contains this
commitment, so $V_"AIR"^((tau))$ simply reads it off the proof and compares it
with the statement component; the point of exposing it is that the leaf
verifier can then bind the challenge contribution to a value that is a
function of the statement and witness rather than of an object that occurs in
neither (@rem:deviations).

#definition(title: "Leaf-verifier relation")[
  For $tau in [M]$,
  $
    cal(R)_"LEAF"^((tau)) = lr(
      {
        cases(
          delim: #none,
          ,
          (bold(p), chi\, sigma\, vk)\; ("com", pi_"AIR"),
          ,
        )
        mid(|)
        cases(
          delim: #none,
          gap: #(0pt + 0.4em),
          sigma = (s, tau, 1, bold(c)),
          and quad V_"AIR"^((tau))((bold(p), chi, s, "com"), pi_"AIR") = accept,
          and quad bold(c) = h(tau, "com")
        )
      }
    )
  $
  The key $vk$ is carried in the statement but not used.
] <def:r-leaf>

#definition(title: "Aggregation relation")[
  Write $x_X := (bold(p), chi, sigma_X, vk)$ for the statement of the child
  $X in {L, R}$ and $sigma_X = (s_X, tau_X, kappa_X, bold(c)_X)$ for its
  recursive statement. Then
  $
    cal(R)_"AGG" = lr(
      {
        cases(
          delim: #none,
          ,
          (bold(p), chi\, sigma\, vk)\; ((sigma_L, pi_L), (sigma_R, pi_R)),
          ,
        )
        mid(|)
        cases(
          delim: #none,
          gap: #(0pt + 0.4em),
          sigma = (s, M + 1, kappa, bold(c)),
          and quad sans("Typed")(tau_X, kappa_X) "for" X in {L, R},
          and quad V_"REC"^((tau_X))[vk](x_X, pi_X) = accept "for" X in {L, R},
          and quad kappa = kappa_L + kappa_R "and" s = s_L + s_R "and" bold(c) = bold(c)_L + bold(c)_R
        )
      }
    )
  $
] <def:r-agg>

Two invariants of this relation are used repeatedly. First, the
_propagation invariant_: both children are verified on statements that carry
the parent's own $(bold(p), chi, vk)$, so every node of a valid tree carries
the root's public statement, challenge pair and key; in particular an
aggregation child is verified under $V(vk, dot, dot)$ for the very $vk$ the
parent declares. Second, the _counter invariant_: $sans("Typed")$ places both
children's counters in $[1, 2^B)$, and $2^(B+1) <= p$ makes
$kappa = kappa_L + kappa_R$ an identity of integers, so every child has
$kappa_X <= kappa - 1$.

#definition(title: "Final relation")[
  Fix the aggregation key $vk_"AGG"$ as a parameter. Then
  $
    cal(R)_"FINAL" = lr(
      {
        cases(
          delim: #none,
          ,
          bold(p)\; (chi, sigma, pi),
          ,
        )
        mid(|)
        cases(
          delim: #none,
          gap: #(0pt + 0.4em),
          sigma = (s, tau, kappa, bold(c)) "and" sans("Typed")(tau, kappa),
          and quad V_"REC"^((tau))[vk_"AGG"]((bold(p), chi, sigma, vk_"AGG"), pi) = accept,
          and quad s = 0,
          and quad chi = DeriveAlpha(bold(c))
        )
      }
    )
  $
] <def:r-final>

Only the public statement $bold(p)$ survives at the root: the challenge pair,
the recursive statement and the child proof are witnesses. Dispatching on
$tau$ lets the Final Verifier accept a leaf-verifier proof directly when the
execution fits in a single AIR instance, the degenerate case treated as a
remark in the whitepaper.

#remark(numbered: true, title: "Well-foundedness")[
  With the whitepaper's range check $kappa_L, kappa_R < 2^B$ alone, a child
  with counter $0$ is admissible. Such a child cannot be a leaf (leaves have
  counter $1$), so it is an aggregation node whose children again have
  counter $0$, and so on: the relation admits infinite descending chains of
  locally satisfiable aggregation statements, none of which contains a leaf,
  while every node of the chain contributes an arbitrary $(s, bold(c))$ to the
  sums. No extractor whose work is bounded by the root statement can exist for
  such a relation, and no knowledge-soundness break is ever charged. The
  typing predicate of @def:dispatch removes the problem: by the counter
  invariant, every child has a strictly smaller counter, a valid tree with root
  counter $kappa$ has exactly $kappa$ leaves and $kappa - 1$ aggregation nodes,
  and strong induction on $kappa$ is well-founded. This is the analogue of the
  step-count typing of the reference architecture's combine circuit.
] <rem:wellfounded>

#remark(numbered: true, title: "Deviations from the whitepaper")[
  The relations above differ from the whitepaper's in the following respects,
  each needed by the proofs of @sec:security.
  + $cal(R)_"AIR"^((tau))$ exposes the trace commitment in its statement, and
    $cal(R)_"LEAF"^((tau))$ takes it as a witness component. In the whitepaper
    the leaf relation computes $bold(c) = h("com"(bold(T), bold(a)))$ although
    neither $bold(T)$ nor $bold(a)$ is a variable of that relation.
  + The challenge contribution is $h(tau, "com")$ rather than $h("com")$. A
    commitment determines the witness but not the type under which it is
    proved; without the type, a prover could choose the type, and hence the
    bus contribution, after the challenge is known
    (@prop:bus-soundness).
  + $cal(R)_"AGG"$ is parametrized by the public $vk$ through the dispatched
    verifier, the types of both children are constrained to $[M+1]$, and both
    children are typed by $sans("Typed")$; in particular $kappa_X >= 1$
    (@rem:wellfounded). The whitepaper states the same key-propagation rule in
    prose and range-checks the counters only from above.
  + $cal(R)_"LEAF"^((tau))$ requires $sigma . tau = tau$, so that the type
    declared in the statement is the type of the circuit.
  + $cal(R)_"FINAL"$ dispatches on the child type and requires
    $sans("Typed")(tau, kappa)$, so $kappa >= 1$ and the single-leaf case is
    covered without a separate remark.
  + The leaves receive the challenge pair $chi = (alpha, gamma)$ and the Final
    Verifier checks $chi = DeriveAlpha(bold(c))$. ZisK broadcasts only $alpha$
    and derives $gamma$ from it by a further hash; modelling that hash as a
    random oracle as well, the analysis of @sec:security goes through with an
    additional $(Q+1) slash abs(KK)$ term for the event that a derived $alpha$
    collides with a previously queried input, which we suppress.
  + The bus contribution is defined abstractly, as a bus fingerprint of the
    witness's message multiset (@def:fingerprint), with LogUp as the
    instantiation (@lem:logup); the whitepaper uses the name $BusCont$ for the
    LogUp running sum without defining it. The leaf-count exponent $B$ is
    used consistently (@sec:relations).
] <rem:deviations>
