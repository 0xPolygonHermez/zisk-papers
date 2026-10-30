#import "../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, fwd, game, lemma, mult,
  negl, poly, proof, proposition, prover, remark, theorem, todo, verifier, vk,
)

This section fixes the notation and the definitions shared by the rest
of the paper: the arithmetization layer (AIRs, interactions and buses),
the interfaces of the cryptographic components (trace commitments, the
multiset hash and key derivation) and the security notions they are required
to satisfy. ZisK's
concrete choices are collected in @sec:instantiation.

*Notation and Parameters.* Let $FF$ be a prime field of order $p$ and $KK$ an extension field of $FF$. $ZZ_p^n$ denotes the additive
group of $n$-vectors of integers modulo $p$, the same set as $FF^n$ viewed as
a $ZZ$-module. For integers $a <= b$, $[a, b]$ and $[a, b)$ are the closed and
half-open integer intervals and $[b] := [1, b]$. Field elements are identified
with integers in $[0, p)$ when needed. $lambda$ is the security parameter;
"PPT" means probabilistic polynomial time in $lambda$, and
$negl(lambda)$ and $poly(lambda)$ denote negligible and polynomially bounded
functions. All algorithms have oracle access to the random oracles; $Q$ bounds the total number of oracle queries an adversary
makes.

The recursion is governed by two integer parameters: the _aggregation arity_
$A >= 2$, the number of children an aggregation node can take, and the
_leaf-count exponent_ $B >= 1$: an aggregation tree may contain at most
$2^B - 1$ leaves. We assume throughout that
$
  A dot 2^B <= p, quad 2^B < p, quad 2^B <= poly(lambda):
$
the first condition guarantees that sums of $A$ range-checked counters never
wrap around in $FF$, the second is the cardinality restriction required by the
multiset hash, and the third makes the number of leaves, and hence the running
time of the extractor, polynomial.

== Arithmetization <sec:arithmetization>

A ZisK proof covers many _instances_ of a fixed family of chips. The constraints of an instance read two kinds of
values: the _columns_ of its trace, which take one value per row, and the
_scalar values_, which are constant over the rows.

#definition(title: "AIR and Witness")[
  Given integers $N >= 1$, $W >= 1$ and $V >= 0$ and a finite set
  $O subset ZZ$ of _row offsets_, an _algebraic intermediate representation_
  (AIR) of _height_ $N$ is a finite set of _constraints_
  $
    cal(C) subset FF[X_j^((o)), Y_l : j in [W], o in O, l in [V]].
  $
  The variables $X_j^((o))$ refer to the columns and the variables $Y_l$ to
  the scalar values. A _witness_ for $cal(C)$ is a pair
  $w = (bold(T), bold(v))$ with $bold(T) in FF^(N times W)$, the _trace_, and
  $bold(v) in FF^V$, the _values_. At row $r in [0, N)$ the variable
  $X_j^((o))$ takes the value $T_j (r + o)$, with row indices taken modulo
  $N$, and the variable $Y_l$ the value $v_l$. The witness _satisfies_
  $cal(C)$ if every constraint polynomial evaluates to zero at every row.
] <def:air>

Offsets may be negative: $X_j^((o))$ with $o < 0$ reads row $r - abs(o)$.
Since the rows are taken modulo $N$, the constraints are enforced on a
cyclic domain, and shifting every constraint by $min O$ rows gives an
equivalent AIR with offsets in $[0, max O - min O]$.

The columns and the values of a witness are of several kinds, which differ in
who chooses them, who sees them and how many instances share them. The
description of an AIR partitions both.

#definition(title: "Column Classes")[
  The description of an AIR $cal(C)$ with $W$ columns and height $N$
  partitions its column indices as
  $[W] = J^"fix" union.sq J^"cach" union.sq J^"wit"$:
  + The _fixed columns_ $J^"fix"$, whose values are prescribed as part of the
    description of $cal(C)$ and hence known to both the prover and the
    verifier.
  + The _cached columns_ $J^"cach"$, whose values are computed once and
    reused across different proofs. Their values are not part of the
    description; instead, a commitment to them (@def:commitment) travels in
    the publics, at the coordinates designated by a
    _cached-commitment binding_ $psi : [m] -> [k]$.
  + The _witness columns_ $J^"wit"$, computed afresh for every proof and
    only known in full to the prover.
  The _prescribed data_ of $cal(C)$ is the family
  $bold(d) = (d_j)_(j in J^"fix")$ of fixed columns $d_j in FF^N$. For a
  trace $bold(T)$ and a set of columns $J$ we write $bold(T)|_J$ for the
  submatrix of the columns in $J$.
] <def:columns>

#definition(title: "Value Classes")[
  The description of an AIR $cal(C)$ with $V$ values partitions its value
  indices as
  $[V] = I^"pub" union.sq I^"pv" union.sq I^"air"$,
  with $abs(I^"pub") = k$ and $abs(I^"pv") = k'$ for every AIR of a proof.
  For values $bold(v)$ and a set of indices $I$ we write $bold(v)|_I$ for
  the subvector of the coordinates in $I$.
  + The _publics_ $bold(p)_"ext" := bold(v)|_(I^"pub") in cal(P)_"ext" := FF^k$, shared by all
    instances and seen by the external verifier.
  + The _proof values_ $bold(p)_"pv" := bold(v)|_(I^"pv") in cal(P)_"pv" := FF^(k')$, chosen by
    the prover once per proof and shared by all instances, but not seen by
    the external verifier.
  + The _AIR values_ $bold(a) := bold(v)|_(I^"air")$ of an instance, chosen
    by the prover for that instance.
  The publics and the proof values form the _public statement_
  $
    bold(p) = (bold(p)_"ext", bold(p)_"pv") in cal(P) := cal(P)_"ext" times cal(P)_"pv".
  $
  Every AIR that takes part in a proof reads the whole public statement,
  but the external verifier sees only $bold(p)_"ext"$: the proof values are
  hidden by the Final Verifier (@def:r-final).
] <def:proof-values>

The constraints of an AIR therefore read, besides its trace, only its own
AIR values and the public statement: they are satisfied or not under a
public statement $bold(p)$. They are also _local_: a constraint relates a
few rows of a single trace, those within its window of offsets $O$. Many of
the facts that a zkVM must establish are not of this kind. When the main
loop delegates an addition to an arithmetic unit, the result it uses must
be the one that the unit computed; and a load must return the value of the
last store to the same address, which may have been executed in another
segment and recorded by another AIR. ZisK expresses such relations with
_buses_. Every row of an AIR may put messages, tuples of field elements, on
a bus, each with a _multiplicity_: positive when the row proves the message
and negative when it assumes it (#fwd(<sec:per-bus>)[Part III]). The relation holds when, on every bus, the
multiplicities of each message add up to zero over all the AIR instances of
a proof, that is, when the bus is _balanced_ (@def:balanced). An
_interaction_ declares, for one AIR, the message that each of its rows puts
on a bus and with which multiplicity.

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

#definition(title: "Chip")[
  A _chip_ is a pair $(cal(C), cal(I))$ of an AIR $cal(C)$ and a finite set
  $cal(I)$ of interactions of $cal(C)$.
] <def:chips>

A chip is the unit into which ZisK splits the work of the VM: the main loop,
each memory region, each arithmetic unit and each precompile is a chip.
Throughout, we fix a positive integer $M$ and an indexed family of chips
$
  frak(A) = { (cal(C)_tau, cal(I)_tau) }_(tau in [M]),
$
where $tau$ is the _type_ of the chip and $cal(C)_tau$ has height $N_tau$
and parameters $W_tau$, $O_tau$ and $V_tau$. We write
$cal(W)_tau := FF^(N_tau times W_tau) times FF^(V_tau)$ for the witness space
of type $tau$.

Each chip carries its column and value classes and its prescribed data;
we index them by the type, as in $J^"fix"_tau$, $I^"air"_tau$, $bold(d)_tau$
and $psi_tau$.

#definition(title: "Local Satisfaction")[
  For $tau in [M]$, $bold(p) = (bold(p)_"ext", bold(p)_"pv") in cal(P)$ and
  $w = (bold(T), bold(v)) in cal(W)_tau$, the predicate $Local_tau (bold(p), w)$
  holds if and only if:
  + $w$ satisfies $cal(C)_tau$.
  + The values carry the public statement:
    $bold(v)|_(I^"pub"_tau) = bold(p)_"ext"$ and
    $bold(v)|_(I^"pv"_tau) = bold(p)_"pv"$.
  + $bold(T)$ agrees with the prescribed data on the fixed columns:
    $T_j (r) = d_(tau, j)(r)$ for every $j in J^"fix"_tau$ and $r in [0, N_tau)$.
  + The cached columns open the commitment carried in $bold(p)_"ext"$:
    $ Commit_"cach" (bold(T)|_(J^"cach"_tau)) = (p_(psi_tau (1)), dots, p_(psi_tau (m))), $
    where $p_i$ is the $i$-th coordinate of $bold(p)_"ext"$.
] <def:local>

Fixed columns are part of the description of $cal(C)_tau$. Cached columns are not: they are computed
once per program, committed with $Commit_"cach"$, and the commitment travels
in the publics, where the description of $cal(C)_tau$ designates its
coordinates. The program being executed is therefore bound through
$bold(p)$ rather than hard-wired into the AIRs: the program ROM
lives in the cached columns of the Rom chip, and whoever accepts a
final proof for $bold(p)_"ext"$ must check that the cached commitments
carried in $bold(p)_"ext"$ are those of the intended program.

#definition(title: "Message Multiset of a Witness")[
  Let $cal(V) := {(b, v) : b in cal(B), v in FF^(ell_b)}$ be the set of
  _bus messages_. An _$FF$-weighted multiset_ of messages is a finitely
  supported map $D : cal(V) -> FF$; we write $abs(D)$ for the size of its
  support and add such maps pointwise. For $tau in [M]$ and $w in cal(W)_tau$,
  the _message multiset_ of $w$ is
  $
    "Msg"_tau (w)(b, v) := sum_(iota in cal(I)_tau, b_iota = b) sum_(r=0)^(N_tau - 1) m_iota (w, r) dot bold(1)[bold(e)_iota (w, r) = v].
  $
  Its support has at most $N_tau dot abs(cal(I)_tau)$ elements.
] <def:msg>

A row that proves a message, with positive multiplicity, and a row of the
same witness that assumes it, with negative multiplicity, cancel in
$"Msg"_tau (w)$: the multiset records the net flow of every message out of the
witness.

#definition(title: "Bus Fingerprint")[
  A _bus fingerprint_ $cal(F)$ consists of a finite _key space_ $cal(X)$, an
  abelian group $G_(cal(F))$ of _values_, a class $cal(D)$ of _admissible_
  nonzero $FF$-weighted multisets of messages, and, for every key
  $chi in cal(X)$, a map $cal(F)_chi$ from $FF$-weighted multisets of
  messages to $G_(cal(F)) union {bot}$, such that:
  + (_Additivity_) $cal(F)_chi (0) = 0$, and
    $cal(F)_chi (D + D') = cal(F)_chi (D) + cal(F)_chi (D')$ whenever the
    right-hand side is defined;
  + (_Soundness_) For every $Lambda$ and every adversary $cal(A)$ that
    outputs a multiset before the key is drawn uniformly from $cal(X)$, the
    _fingerprint advantage_:
    $
      Adv("fp", (cal(F), Lambda))(cal(A)) := Pr[
        D <- cal(A); chi <- cal(X) :
        D in cal(D) and abs(D) <= Lambda and cal(F)_chi (D) = 0
      ]
    $
    is small. The fingerprint is _statistically sound_ with error
    $epsilon_(cal(F))$ if $Adv("fp", (cal(F), Lambda))(cal(A)) <= epsilon_(cal(F))(Lambda)$
    for every adversary, with $epsilon_(cal(F))$ non-decreasing, and
    _computationally sound_ if the advantage is negligible for every PPT
    adversary.
  The _bus contribution_ of $w in cal(W)_tau$ under the key $chi$ is
  $
    BusCont_chi (cal(I)_tau, w) := cal(F)_chi ("Msg"_tau (w)) in G_(cal(F)) union {bot}.
  $
] <def:fingerprint>

A fingerprint is an additive summary of a multiset that vanishes on an
admissible nonzero multiset only for few keys, or only for keys no efficient
adversary can anticipate.


#definition(title: "Typed Witness Collection")[
  A _typed witness collection_ is a finite list
  $
    L = ((tau_1, w_1), dots, (tau_(abs(L)), w_(abs(L)))), quad tau_i in [M], quad w_i in cal(W)_(tau_i).
  $
  Types and witnesses may repeat, and each entry counts separately; the order
  of the list carries no meaning. The _number of bus terms_ of $L$ is
  $Lambda(L) := sum_(i=1)^(abs(L)) N_(tau_i) dot abs(cal(I)_(tau_i))$, and we set
  $Lambda_"max" := (2^B - 1) dot max_(tau in [M]) N_tau abs(cal(I)_tau) + g$,
  so that $Lambda(L) + g <= Lambda_"max"$ whenever $abs(L) < 2^B$, where $g$
  bounds the global messages introduced below.
] <def:collection>

Some messages are not emitted by any witness: they belong to the system as
a whole and are determined by the public statement. In ZisK these _global
messages_ open and close the continuation chains, initialize the registers
and inject the public outputs into the buses. We model them as a fixed
function $cal(G)$ that maps every public statement $bold(p) in cal(P)$ to an
$FF$-weighted multiset of messages $cal(G)(bold(p))$, with
$abs(cal(G)(bold(p))) <= g$ for a constant $g$.

#definition(title: "Balance of a Witness Collection")[
  The _signed multiplicity_ of a typed witness collection $L$ is the
  $FF$-weighted multiset
  $
    cal(M)_L := sum_(i=1)^(abs(L)) "Msg"_(tau_i)(w_i),
  $
  that is,
  $
    cal(M)_L (b, v) = sum_(i=1)^(abs(L)) sum_(iota in cal(I)_(tau_i), b_iota = b) sum_(r=0)^(N_(tau_i) - 1) m_iota (w_i, r) dot bold(1)[bold(e)_iota (w_i, r) = v].
  $
  The collection is _balanced for_ $bold(p) in cal(P)$, written
  $Balanced_bold(p) (L)$, if $cal(M)_L + cal(G)(bold(p)) = 0$, i.e.
  $cal(M)_L (b, v) + cal(G)(bold(p))(b, v) = 0$ for every bus $b in cal(B)$
  and every message $v in FF^(ell_b)$. Note that
  $abs(cal(M)_L + cal(G)(bold(p))) <= Lambda(L) + g$.
] <def:balanced>

Note that multiplicities are
field elements: $Balanced_bold(p) (L)$ does not by itself assert that every message is
sent and received the same number of times as integers, since $p$ copies of a
message cancel. We return to this point in #fwd(<rem:integer-balance>)[Part II].

== Interfaces <sec:components>

A _non-interactive argument system_ $Pi = (prover, verifier)$ for a relation
$cal(R)$ consists of a _prover_ $prover$, which on input a statement
$bb(x)$ and a witness $bb(w)$ outputs a proof $pi <- prover(bb(x), bb(w))$,
and a deterministic _verifier_ $verifier$, together with a verification key
$vk_Pi$ produced at setup, where $verifier(vk_Pi, bb(x), pi) in {0, 1}$ and
the value $1$ means that the proof $pi$ is accepted for the statement
$bb(x)$. We write
$verifier_X (bb(x), pi) := verifier(vk_X, bb(x), pi)$ for the verifier of the system attesting to the
relation $cal(R)_X$, and keep the explicit form $verifier(vk, bb(x), pi)$ where the key is
a variable. The relations of @sec:relations-def refer to argument systems
only through their verifiers, so the prover is never named again, and to the
following fixed public maps only through their signatures. Their
security properties are defined in @sec:definitions, and
ZisK's choices are given in @sec:instantiation. Two of the maps are
commitments, in the following sense.

#definition(title: "Deterministic Commitment Scheme")[
  A _deterministic commitment scheme_ $Com$ consists of a set of _messages_,
  a finite set of _commitments_, and a polynomial-time computable function
  $Commit$ from the former to the latter. It is _binding_ if for every PPT
  adversary $cal(A)$
  $
    Adv("bind", Com)(cal(A)) := Pr[ (m, m') <- cal(A)(1^lambda) :
      m != m' and Commit(m) = Commit(m') ] <= negl(lambda).
  $
  Since $Commit$ is deterministic, binding is collision resistance of
  $Commit$. When the messages are vectors or matrices over $FF$, the scheme
  is a _vector commitment_ if it also offers openings of individual
  positions.
] <def:commitment>

The following interface elements are used throughout:
- *Carriers.* A finite key space $cal(X)$ and an abelian group
  $G_(cal(F))$ of fingerprint values (@def:fingerprint), and a finite
  abelian _accumulator group_ $G_(cal(H))$.
- *Trace commitment.* A deterministic commitment scheme $Com$ whose messages
  are the first-stage parts of witnesses, with commitment space ${0, 1}^*$:
  for $w in union.big_(tau in [M]) cal(W)_tau$, the commitment
  $"com" = Commit(w)$ covers the witness columns and the first-stage AIR
  values of $w$, and binding and extraction (@def:ext-com) refer to this
  part. The argument system for a chip takes the key
  $chi in cal(X)$ as a public input, so the witness is key-independent.
- *Cached-column commitment.* A deterministic commitment scheme $Com_"cach"$
  with message space $union.big_(tau in [M]) FF^(N_tau times abs(J^"cach"_tau))$
  and commitment space $FF^m$. Its output for the cached columns of a type is
  not part of a verification key but of the public statement (@def:columns).
- *Hash-to-group and multiset hash.* $h : [M] times {0,1}^* -> G_(cal(H))$
  maps a _typed commitment_ $(tau, "com")$ to a group element, and
  $
    cal(H)(cal(S)) := sum_(x in "supp" cal(S)) mult_cal(S)(x) dot h(x) in G_(cal(H))
  $
  is the induced multiset hash on finite multisets $cal(S)$ of typed
  commitments, where $mult_cal(S)(x)$ is the multiplicity of $x$ in $cal(S)$.
  $cal(H)$ is additively homomorphic over multiset union.
- *Key derivation.* $DeriveKey : cal(P) times G_(cal(H)) -> cal(X)$, a
  fixed public function of the public statement and the accumulated value.

== Security Definitions <sec:definitions>

#definition(title: "Knowledge Soundness")[
  A non-interactive argument system $Pi$ for
  a relation $cal(R)$ is _knowledge-sound_ if there exists a PPT algorithm
  $cal(E)$, the _extractor_, such that for every PPT adversary $cal(A)$:
  $
    Adv("ks", Pi)(cal(A)) := Pr[ & (bb(x), pi) <- cal(A)(1^lambda); bb(w) <- cal(E)(bb(x), pi) : verifier(vk_Pi, bb(x), pi) = 1 and (bb(x); bb(w)) in.not cal(R) ] <= negl(lambda),
  $
  the probability taken over the coins of $cal(A)$ and $cal(E)$ and the
  random oracles, to which all algorithms have access. We assume that the
  running time of $cal(E)(bb(x), pi)$ is at most $Time(cal(A)(1^lambda)) + poly(lambda)$
  for every $cal(A)$ and every $(bb(x), pi)$ in the support of $cal(A)$'s output:
  the extractor incurs an additive polynomial overhead over one evaluation of
  $cal(A)$. Besides $(bb(x), pi)$, the extractor reads the list of
  $cal(A)$'s random-oracle queries and answers, which we leave implicit in
  the notation. We call $Adv("ks", Pi)(cal(A))$ the _knowledge-soundness error_ of
  $cal(A)$ against $Pi$.
] <def:ks>

#remark(title: "Straight-Line Extraction")[
  The extractor of @def:ks is straight-line: it receives the statement, the
  proof and the adversary's oracle queries, and does not rewind the
  adversary. For succinct proofs this is not achievable in the plain model,
  and in the random-oracle model it holds for one argument but does not
  compose across a recursion (@rem:idealized). The definition is a proxy that
  makes the reduction structure explicit; a concrete instantiation replaces it
  by extractability in the random-oracle model with the overhead discussed
  there.
]

#definition(title: "Straight-Line Extractable Commitment")[
  A deterministic commitment scheme $Com$ (@def:commitment) is
  _straight-line extractable_ if there is a PPT algorithm $cal(E)_Com$ that,
  given a transcript $cal(T)$ of random-oracle queries and answers and a
  value $"com"$, outputs a message or $bot$, such that for every PPT
  adversary $cal(A)$ that at some point during its execution announces a
  value $"com"$ and at the end outputs a message $m$,
  $
    Adv("ext", Com)(cal(A)) := Pr[
      Commit(m) = "com" and cal(E)_Com (cal(T)_(<= t), "com") != m
    ] <= negl(lambda),
  $
  where $t$ is the time of the announcement and $cal(T)_(<= t)$ the transcript
  up to it.
] <def:ext-com>

For a Merkle tree over a random oracle the extractor recomputes the leaves
from the tree of queried nodes below the root; it fails only if the adversary
later opens the root to a leaf it had not queried, which requires guessing an
oracle output or finding a collision. Straight-line extractability implies binding: if $cal(A)$ outputs
$m != m'$ with $Commit(m) = Commit(m') = "com"$, the extractor's output on
$"com"$ differs from at least one of them, so the adversary $cal(D)$ that
runs $cal(A)$, announces $"com"$ and returns one of $m, m'$ chosen at
random fails extraction with at least half of $cal(A)$'s success probability:
$Adv("bind", Com)(cal(A)) <= 2 dot Adv("ext", Com)(cal(D))$.

#definition(title: "Preimage Awareness of the Accumulator")[
  The multiset hash $cal(H)$ is _preimage aware on multisets of cardinality
  below $2^B$_ @EC:DodRisShr09 if there is a PPT algorithm $cal(E)_(cal(H))$
  that, given a transcript $cal(T)$ of random-oracle queries and answers and a
  value $y in G_(cal(H))$, outputs a multiset of typed commitments or
  $bot$, such that for every PPT adversary $cal(A)$ that at some point during
  its execution announces a value $y$ and at the end outputs a multiset
  $cal(S)$,
  $
    Adv("pa", cal(H))(cal(A)) := Pr[
      abs(cal(S)) < 2^B and cal(H)(cal(S)) = y and cal(E)_(cal(H)) (cal(T)_(<= t), y) != cal(S)
    ] <= negl(lambda),
  $
  where $t$ is the time of the announcement, $cal(T)_(<= t)$ the transcript
  up to it, and $abs(cal(S))$ the cardinality of $cal(S)$, counted with
  multiplicity.
] <def:cr>

The definition mirrors @def:ext-com, with the accumulator in the role of the
commitment: what is announced is a value of $G_(cal(H))$, and what is
extracted is the small multiset the adversary later opens it to. The
cardinality restriction is necessary for ZisK's accumulator group: $ZZ_p^n$
has exponent $p$, so adding $p$ copies of any element to a multiset leaves
$cal(H)$ unchanged, and $2^B < p$ rules this out. Preimage awareness implies
collision resistance on such multisets, since two distinct small multisets
with the same hash would both have to equal the extractor's output.

For LtHash, collision resistance on bounded multisets reduces to the
short-integer-solution problem @STOC:Ajtai96 @EPRINT:LKMW19 @ZISK:LTHASH; the reduction
requires the inner digest of $h$ to be collision resistant on its own, which
a single field element is not, so we assume the digest has at least
$2 lambda$ bits (#fwd(<sec:discussion>)[Part IV]). Preimage awareness, however, is not known
to follow from any standard assumption for an algebraic accumulator, and
assuming it is the second idealization of @rem:idealized. It is nevertheless
the property the analysis needs, and collision resistance alone would not do:
an adversary may fix a target $y$ by querying $DeriveKey$ at it and only
afterwards obtain the $h$-values of the elements it assembles into a multiset
hashing to $y$, choosing which fresh values to combine after seeing them.
Whether this succeeds is a preimage question, computational rather than
statistical, and it is exactly what the extractor of @def:cr rules out.

#definition(title: "Random-Oracle Model")[
  The hash-to-group function $h$, the key derivation $DeriveKey$, the
  Fiat–Shamir transcript of every argument and the compression functions of
  the Merkle trees of $Com$ and $Com_"cach"$ are independent random
  oracles. An
  adversary makes at most $Q$ queries in total; every algorithm, including
  verifiers and extractors, has oracle access.
] <def:rom>

The definitions above, together with the random-oracle model, are the
setting of the whole analysis. Two of the properties it relies on are
idealizations, which we make explicit.

#remark(numbered: true, title: "Idealized Proof Model")[
  The analysis is idealized in two respects.

  First, @def:ks postulates a straight-line extractor that runs in essentially
  the time of the adversary. Because the argument systems are hash-based, the
  natural model is the random-oracle model, in which such extractors
  exist for a single argument @TCC:BenChiSpo16. Composing straight-line
  extraction across the layers of a recursion tree, however, requires every
  argument to remain knowledge-sound relative to the same oracle, and such
  relativized succinct arguments do not exist in general
  @EPRINT:BarChiGua24. In our analysis we idealize over this
  obstruction and assume that straight-line extraction composes.

  Second, the bus argument is sound only if the multiset of typed commitments
  that the accumulator $bold(c)$ stands for is fixed before the random oracle
  answers at $bold(c)$. For the trace commitments this is the straight-line
  extractability of Merkle trees in the random-oracle model (@def:ext-com). For the
  accumulator we assume the analogous property, preimage awareness
  (@def:cr): a straight-line extractor recovers, from the transcript at the
  time a value is announced, the multiset the adversary later opens it to.
  For the algebraic accumulator $cal(H)$ this is an idealization. Distinct
  small multisets with equal hash exist in abundance; only the hardness of
  finding them protects the scheme; and recovering a multiset from its
  accumulator is a subset-sum problem, so no straight-line extractor is
  known; only collision resistance follows from standard assumptions.
  #fwd(<rem:forking>)[Part II] discusses the rigorous alternative.

  Consequently, while the analysis produces explicit advantage bounds and reduction
  running times (#fwd(<thm:main>)[Part II]), the two idealizations mean that these should be
  read as statements about the reduction structure (the recursion topology is
  sound and the relations compose) rather than as a concrete security level.
] <rem:idealized>
