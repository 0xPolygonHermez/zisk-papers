#import "../../lib.typ": (
  Adv, Balanced, BusCont, Com, Commit, DeriveKey, Local, Pr, definition, mult, negl, poly, remark, vk,
)
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

This section fixes the notation used in the security analysis and restates,
in the exact form the proofs consume: the arithmetization layer (AIRs, interactions and buses), the
aggregation tree and the interfaces of its cryptographic components (trace
commitments, the multiset hash and key derivation), the three accumulators
the tree carries, and the four relations attested by its nodes. ZisK's
concrete choices are collected in @sec:instantiation.

== Notation and Parameters

Let $FF$ be a prime field of order $p$ and $KK$ an extension field of $FF$. $ZZ_p^n$ denotes the additive
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
$B >= 1$: an aggregation tree may contain at most $2^B - 1$ leaves. We assume throughout that
$
  2^(B+1) <= p, quad 2^B < p, quad 2^B <= poly(lambda):
$
the first condition guarantees that sums of two range-checked counters never
wrap around in $FF$, the second is the cardinality restriction required by the
multiset hash, and the third makes the number of leaves, and hence the running
time of the extractor, polynomial.

== Arithmetization <sec:arithmetization>

#include "../../shared/air.typ"

Fixed columns are part of the description of $cal(C)_tau$, hence of the
verification key of type $tau$. Cached columns are not: they are computed
once per program, committed with $Commit_"cach"$, and the commitment travels
in the public statement, where the description of $cal(C)_tau$ designates
its coordinates. The program being executed is therefore bound through
$bold(p)$ rather than hard-wired into the circuits, as the program code is in
the step circuit of the reference architecture @EF:VanillaVM: the program ROM
and the boot
state live in cached columns of the relevant AIR types, and whoever accepts a
Final proof for $bold(p)$ must check that the cached commitments carried in
$bold(p)$ are those of the intended program. Since every node of a valid
tree carries the same $bold(p)$ (@sec:relations-def), binding of
$Commit_"cach"$ makes the cached columns of all leaves of one type equal.

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
  A _bus fingerprint_ $cal(F)$ consists of a finite _key space_ $cal(X)$, an
  abelian group $cal(G)_(cal(F))$ of _values_, a class $cal(D)$ of _admissible_
  nonzero $FF$-weighted multisets of messages, and, for every key
  $chi in cal(X)$, a map $cal(F)_chi$ from $FF$-weighted multisets of
  messages to $cal(G)_(cal(F)) union {bot}$, such that
  + (_additivity_) $cal(F)_chi (0) = 0$, and
    $cal(F)_chi (D + D') = cal(F)_chi (D) + cal(F)_chi (D')$ whenever the
    right-hand side is defined;
  + (_soundness_) for every $Lambda$ and every adversary $cal(A)$ that
    outputs a multiset before the key is drawn uniformly from $cal(X)$, the
    _fingerprint advantage_
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
    BusCont_chi (cal(I)_tau, w) := cal(F)_chi ("Msg"_tau (w)) in cal(G)_(cal(F)) union {bot}.
  $
] <def:fingerprint>

A fingerprint is an additive summary of a multiset that vanishes on an
admissible nonzero multiset only for few keys, or only for keys no efficient
adversary can anticipate. The relations of @sec:relations-def are stated for
an arbitrary fingerprint; ZisK's, LogUp, is described in @sec:instantiation.


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

Note that multiplicities are
field elements: $Balanced(L)$ does not by itself assert that every message is
sent and received the same number of times as integers, since $p$ copies of a
message cancel. We return to this point in @rem:integer-balance.

== The Aggregation Tree <sec:tree>

A ZisK proof is a tree. Its leaves are the AIR instances of an execution: for
each type $tau in [M]$ the prover produces some number of witnesses in
$cal(W)_tau$, one per segment of that type, and proves each with an argument
system for the AIR of the type. Directly above every AIR proof sits a _leaf
verifier_, a circuit that verifies the AIR proof and re-exposes its statement
in a common format. Above the leaf verifiers, _aggregation nodes_ verify two
child proofs each, so the tree is binary; it need not be balanced, because a
node is proved as soon as its two children are available. At the top, a
single _Final Verifier_ verifies the root of the aggregation tree and performs
the global checks; its statement, the public statement $bold(p)$, is the only
thing an external verifier sees. @fig:aggregation-tree shows an example with
three leaves.

Three quantities travel up the tree and are combined at every aggregation
node: the number of leaves, an accumulation of the leaves' commitments, and an
accumulation of the leaves' bus contributions. They are the _accumulators_ of
@sec:accumulators; the counter is range-checked at every node, and the Final
Verifier checks one condition on each.

The order of operations matters for the bus argument. Bus contributions are
fingerprints under a key $chi$, and the key must be fixed before any leaf is
proved yet must not be under the prover's control. ZisK derives it from the
leaves themselves: the prover commits to every witness, accumulates the typed
commitments with the multiset hash $cal(H)$, derives $chi$ from the
accumulated value with $DeriveKey$, and only then proves the leaves with
$chi$ as a public input. The tree recomputes the accumulation as it
aggregates, and the Final Verifier checks that the key the leaves used is the
one derived from what was actually aggregated. Because the shape of the tree
is not known when the key is derived, the accumulation must not depend on it;
this is why the accumulators below are commutative monoids.

#figure(
  {
    set text(size: 7pt)
    let sub(body) = text(size: 6pt, body)
    let lbl(body) = text(size: 6pt, body)
    let leaf-fill = rgb("dde8fb")
    let leaf-stroke = rgb("4a6fa5")
    let lv-fill = rgb("fbe4c2")
    let lv-stroke = rgb("a86e2c")
    let agg-fill = rgb("fbd5d5")
    let agg-stroke = rgb("a84444")
    let root-fill = rgb("c8e6e0")
    let root-stroke = rgb("2e7d6e")
    let arr = 0.5pt + luma(80)
    let dash = (dash: "dashed", paint: luma(130), thickness: 0.4pt)

    let box(f, s, w, h) = (fill: f, stroke: 0.5pt + s, width: w, height: h, inset: 3pt, corner-radius: 2pt)
    let agg-body = align(center)[
      *Aggregation node* #linebreak()
      #sub[$V_"REC"[vk](pi_L), V_"REC"[vk](pi_R) = 1$] #linebreak()
      #sub[$sans("Typed")(tau_L, kappa_L), quad sans("Typed")(tau_R, kappa_R)$] #linebreak()
      #sub[$kappa = kappa_L + kappa_R, quad s = s_L + s_R$] #linebreak()
      #sub[$bold(c) = bold(c)_L + bold(c)_R$]
    ]
    let lv-body = align(center)[
      *Leaf verifier* $tau$ #linebreak()
      #sub[$V_"AIR"^((tau))(pi_"AIR") = 1$] #linebreak()
      #sub[$kappa = 1, quad bold(c) = h(tau, "com")$]
    ]
    let air-body = align(center)[*AIR instance* #linebreak() #sub[type $tau$, witness $w$]]

    diagram(
      spacing: (0.7cm, 1.15cm),
      label-sep: 2pt,

      // Final Verifier
      node(
        (0, 0),
        align(center)[
          *Final Verifier* #linebreak()
          #sub[$V_"REC"[vk_"AGG"](pi) = 1$] #linebreak()
          #sub[$sans("Typed")(tau, kappa), quad s = 0$] #linebreak()
          #sub[$chi = DeriveKey(bold(c))$]
        ],
        ..box(root-fill, root-stroke, 3.2cm, 1.25cm),
      ),
      // Aggregation nodes
      node((0, 1), agg-body, ..box(agg-fill, agg-stroke, 3.4cm, 1.5cm)),
      node((-1, 2), agg-body, ..box(agg-fill, agg-stroke, 3.4cm, 1.5cm)),
      // Leaf verifiers
      node((-1.5, 3), lv-body, ..box(lv-fill, lv-stroke, 2.5cm, 1.0cm)),
      node((-0.5, 3), lv-body, ..box(lv-fill, lv-stroke, 2.5cm, 1.0cm)),
      node((1, 3), lv-body, ..box(lv-fill, lv-stroke, 2.5cm, 1.0cm)),
      // AIR instances
      node((-1.5, 4), air-body, ..box(leaf-fill, leaf-stroke, 2.2cm, 0.7cm)),
      node((-0.5, 4), air-body, ..box(leaf-fill, leaf-stroke, 2.2cm, 0.7cm)),
      node((1, 4), air-body, ..box(leaf-fill, leaf-stroke, 2.2cm, 0.7cm)),

      // Public statement and key enter every AIR instance
      edge((-1.5, 4.5), (-1.5, 4), lbl[$(bold(p), chi)$], "->", stroke: dash, label-side: right),
      edge((-0.5, 4.5), (-0.5, 4), lbl[$(bold(p), chi)$], "->", stroke: dash, label-side: right),
      edge((1, 4.5), (1, 4), lbl[$(bold(p), chi)$], "->", stroke: dash, label-side: right),

      // Statements and proofs flowing upward
      edge((-1.5, 4), (-1.5, 3), lbl[$(bold(p), chi, s, "com")\, pi_"AIR"$], "->", stroke: arr, label-side: right),
      edge((-0.5, 4), (-0.5, 3), lbl[$(bold(p), chi, s, "com")\, pi_"AIR"$], "->", stroke: arr, label-side: right),
      edge((1, 4), (1, 3), lbl[$(bold(p), chi, s, "com")\, pi_"AIR"$], "->", stroke: arr, label-side: right),
      edge((-1.5, 3), (-1, 2), lbl[$(bold(p), chi, sigma_L, vk)\, pi_L$], "->", stroke: arr, label-side: left),
      edge((-0.5, 3), (-1, 2), lbl[$(bold(p), chi, sigma_R, vk)\, pi_R$], "->", stroke: arr, label-side: right),
      edge((-1, 2), (0, 1), lbl[$(bold(p), chi, sigma_L, vk)\, pi_L$], "->", stroke: arr, label-side: left),
      edge((1, 3), (0, 1), lbl[$(bold(p), chi, sigma_R, vk)\, pi_R$], "->", stroke: arr, label-side: right),
      edge((0, 1), (0, 0), lbl[$(bold(p), chi, sigma, vk)\, pi$], "->", stroke: arr, label-side: right),
    )
  },
  caption: [
    An aggregation tree with three AIR instances. Each arrow carries the
    statement and the proof a node produces, which the node above takes as
    witness: an AIR instance of type $tau$ proves $(bold(p), chi, s, "com")$; a
    leaf verifier re-exposes it as $(bold(p), chi, sigma, vk)$ with
    $sigma = (tau, 1, bold(c), s)$; an aggregation node adds its children's
    accumulators, dispatches on their types and declares type $M + 1$; the
    Final Verifier fixes $vk = vk_"AGG"$, checks the root predicates and
    exposes only $bold(p)$. The dashed arrows are the public inputs common to
    every leaf.
  ],
) <fig:aggregation-tree>

== Interfaces <sec:components>

A _non-interactive argument system_ $Pi$ for a relation $cal(R)$ consists of a
prover and a deterministic _verifier_ $V$, together with a verification key
$vk_Pi$ produced at setup, where $V(vk_Pi, x, pi) in {0, 1}$ and the value $1$
means that the proof $pi$ is accepted for the statement $x$. We write
$V_X (x, pi) := V(vk_X, x, pi)$ for the verifier of the system attesting to the
relation $cal(R)_X$, and keep the explicit form $V(vk, x, pi)$ where the key is
a variable. The relations below refer to argument systems only through their
verifiers, so the prover is never named again. The relations of
@sec:relations-def refer to argument systems only through their verifiers,
and to the following fixed public maps only through their signatures. Their
security properties are defined where they are used, in @sec:security, and
ZisK's choices are given in @sec:instantiation. Two of the maps are
commitments, in the following sense.

#include "../../shared/commitment.typ"

The following interface elements are used throughout:
- *Carriers.* A finite key space $cal(X)$ and an abelian group
  $cal(G)_(cal(F))$ of fingerprint values (@def:fingerprint), and a finite
  abelian _accumulator group_ $cal(G)_(cal(H))$.
- *Trace commitment.* A deterministic commitment scheme $Com$ with message
  space $union.big_(tau in [M]) cal(W)_tau$ and commitment space ${0, 1}^*$.
  A commitment $"com" = Commit(bold(T), bold(a))$ covers every column of the
  trace and every AIR value. The argument system for an AIR type takes the key
  $chi in cal(X)$ as a public input, so the witness is key-independent.
- *Cached-column commitment.* A deterministic commitment scheme $Com_"cach"$
  with message space $union.big_(tau in [M]) FF^(N_tau times abs(J^"cach"_tau))$
  and commitment space $FF^m$. Its output for the cached columns of a type is
  not part of a verification key but of the public statement (@def:columns).
- *Hash-to-group and multiset hash.* $h : [M] times {0,1}^* -> cal(G)_(cal(H))$
  maps a _typed commitment_ $(tau, "com")$ to a group element, and
  $
    cal(H)(cal(S)) := sum_(x in "supp" cal(S)) mult_cal(S)(x) dot h(x) in cal(G)_(cal(H))
  $
  is the induced multiset hash on finite multisets $cal(S)$ of typed
  commitments, where $mult_cal(S)(x)$ is the multiplicity of $x$ in $cal(S)$.
  $cal(H)$ is additively homomorphic over multiset union.
- *Key derivation.* $DeriveKey : cal(G)_(cal(H)) -> cal(X)$, a fixed public
  function of the accumulated value.

== Accumulators <sec:accumulators>

#definition(title: "Accumulator")[
  An _accumulator_ over the aggregation tree consists of a commutative monoid
  of _values_, a _leaf contribution_ assigning a value to every leaf, a
  _child check_, a predicate on values that every aggregation node evaluates
  on the value of each of its children, and a _root check_, a predicate on
  values that the Final Verifier evaluates on the value of the root of the
  aggregation tree. The value of a leaf is its
  contribution, and the value of an aggregation node is the sum of the values
  of its two children. By associativity and commutativity, the value of any
  node is the sum of the contributions of the leaves below it, whatever the
  shape of the subtree.
] <def:accumulator>

The recursion carries three accumulators. Their values at a node, together
with the node's type, form the _recursive statement_
$
  sigma = (tau, kappa, bold(c), s),
$
where the type $tau in [M + 1]$ is the AIR type for a leaf verifier and the
marker $M + 1$ for an aggregation node. We write $sigma . tau$, $sigma . kappa$,
$sigma . bold(c)$ and $sigma . s$ for the components of a recursive statement.

#figure(
  {
    set text(size: 8.5pt, hyphenate: false)
    table(
      stroke: 0.3pt,
      columns: (26%, 12%, 20%, 18%, 24%),
      align: (left, left, left, left, left),
      table.header([*Accumulator*], [*Monoid*], [*Leaf contribution*], [*Child check*], [*Root check*]),
      [leaf counter $kappa$], [$(FF, +)$], [$1$], [$kappa_X in [1, 2^B)$], [$kappa in [1, 2^B)$],
      [challenge accumulator $bold(c)$],
      [$(cal(G)_(cal(H)), +)$],
      [$h(tau, "com")$],
      [---],
      [$chi = DeriveKey(bold(c))$],

      [bus partial sum $s$], [$(cal(G)_(cal(F)), +)$], [$cal(F)_chi ("Msg"_tau (w))$], [---], [$s = 0$],
    )
  },
  caption: [The three accumulators of the recursion.],
  kind: table,
) <tbl:accumulators>

The counter is added in $FF$. Its child check is the typing predicate of
@def:dispatch, which every aggregation node applies to both children and the
Final Verifier applies to the root; it places every counter in $[1, 2^B)$,
and $2^(B+1) <= p$ then rules out wrap-around, so the field sums are integer
sums and no node has $2^B$ or more leaves below it. The other two
accumulators are checked only at the root. The value of the
challenge accumulator at a node is $cal(H)$ of the multiset of typed
commitments below it, by the homomorphism of $cal(H)$; the value of the bus
partial sum is $cal(F)_chi$ of the summed message multisets below it, by the
additivity of $cal(F)$, so at the root it equals $cal(F)_chi (cal(M)_L)$ for
the collection $L$ of all leaves.

An update rule that is not associative and commutative would make the root
value depend on the shape of the tree, which is not known when the key is
derived (@sec:tree); a hash-tree accumulation
$bold(c) = H(bold(c)_L, bold(c)_R)$, for instance, would force the prover to
fix the tree before deriving $chi$. Writing every update as the monoid sum
therefore loses no generality.

== Recursive Relations <sec:relations-def>

We write a relation as $cal(R) = { (x; w) mid(|) phi(x, w) }$ with public
statement $x$, witness $w$ and _defining predicate_ $phi$; in the definitions
below, $phi$ is the conjunction of the clauses displayed to the right of the
bar. Every node statement below the Final Verifier
carries the public statement $bold(p) in cal(P)$, a key $chi in cal(X)$, a
recursive statement $sigma$ and a verification key $vk$. We proceed from the
leaves to the root, naming after each relation the argument system that
proves it, since the relation above uses its verifier.

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
  with $bold(p) in cal(P)$, $chi in cal(X)$, $s in cal(G)_(cal(F))$ and
  $(bold(T), bold(a)) in cal(W)_tau$.
] <def:r-air>

The relation is in _commit-and-prove_ form: the trace commitment is part of
the statement. A proof for $cal(C)_tau$ already contains this
commitment, so $V_"AIR"^((tau))$ simply reads it off the proof and compares it
with the statement component; the point of exposing it is that the leaf
verifier can then bind the challenge contribution to a value that is a
function of the statement and witness rather than of an object that occurs in
neither.

Let $Pi_"AIR"^((tau))$ be an argument system for $cal(R)_"AIR"^((tau))$, one
per type, with verifier $V_"AIR"^((tau))$ and key $vk_"AIR"^((tau))$.

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
          sigma = (tau, 1, bold(c), s),
          and quad V_"AIR"^((tau))((bold(p), chi, s, "com"), pi_"AIR") = 1,
          and quad bold(c) = h(tau, "com")
        )
      }
    )
  $
  The key $vk$ carried in the statement is the propagated aggregation key, which is not used here.
] <def:r-leaf>

In the terms of @sec:accumulators, a leaf verifier of type $tau$ contributes
$1$, $h(tau, "com")$ and the bus contribution $s$ certified by the AIR proof.
Let $Pi_"LEAF"^((tau))$ be an argument system for $cal(R)_"LEAF"^((tau))$,
with verifier $V_"LEAF"^((tau))$ and key $vk_"LEAF"^((tau))$; its circuit
hard-codes $vk_"AIR"^((tau))$.

An aggregation node must verify children of every kind, leaf verifiers of any
type and other aggregation nodes. It hard-codes the $M$ leaf-verifier keys and
selects among them by the child's type; for an aggregation child it uses a
key that it does not hard-code but reads from its own statement.

#definition(title: "Recursive Dispatch")[
  #set math.cases(gap: 1em)
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
    sans("Typed")(tau, kappa) := (tau in [M] and kappa = 1) or (tau = M + 1 and 2 <= kappa < 2^B).
  $
] <def:dispatch>

The dispatch is a function of the key $vk$ carried in the statement, and the
typing predicate is what makes the counter meaningful (@sec:accumulators).

#definition(title: "Aggregation relation")[
  Write $x_X := (bold(p), chi, sigma_X, vk)$ for the statement of the child
  $X in {L, R}$ and $sigma_X = (tau_X, kappa_X, bold(c)_X, s_X)$ for its
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
          sigma = (M + 1, kappa, bold(c), s),
          and quad sans("Typed")(tau_X, kappa_X) "for" X in {L, R},
          and quad V_"REC"^((tau_X))[vk](x_X, pi_X) = 1 "for" X in {L, R},
          and quad kappa = kappa_L + kappa_R "and" bold(c) = bold(c)_L + bold(c)_R "and" s = s_L + s_R
        )
      }
    )
  $
] <def:r-agg>

Two invariants of this relation are used repeatedly. First, the
_propagation invariant_: both children are verified on statements that carry
the parent's own $(bold(p), chi, vk)$, so every node of a valid tree carries
the root's public statement, fingerprint key and verification key; in particular an
aggregation child is verified under $V(vk, dot, dot)$ for the very $vk$ the
parent declares. Second, the _counter invariant_: $sans("Typed")$ places both
children's counters in $[1, 2^B)$, and $2^(B+1) <= p$ makes
$kappa = kappa_L + kappa_R$ an identity of integers, so every child has
$kappa_X <= kappa - 1$.

Let $Pi_"AGG"$ be an argument system for $cal(R)_"AGG"$, with verifier
$V_"AGG"$ and key $vk_"AGG"$. There is no circularity: $cal(R)_"AGG"$ is one
ordinary relation over statements that contain an arbitrary string $vk$, the
key $vk_"AGG"$ of the argument system for that relation is produced afterwards
at setup, and the Final relation below fixes $vk := vk_"AGG"$, at which point
$V_"REC"^((M+1))[vk_"AGG"] = V_"AGG"$.

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
          sigma = (tau, kappa, bold(c), s) "and" sans("Typed")(tau, kappa),
          and quad V_"REC"^((tau))[vk_"AGG"]((bold(p), chi, sigma, vk_"AGG"), pi) = 1,
          and quad s = 0,
          and quad chi = DeriveKey(bold(c))
        )
      }
    )
  $
] <def:r-final>

Only the public statement $bold(p)$ survives at the root: the fingerprint key,
the recursive statement and the child proof are witnesses. Dispatching on
$tau$ lets the Final Verifier accept a leaf-verifier proof directly when the
execution fits in a single AIR instance.

Let $Pi_"FINAL"$ be an argument system for $cal(R)_"FINAL"$, with verifier
$V_"FINAL"$ and key $vk_"FINAL"$; this is the verifier run by the external
party. The verification keys involved play different roles. @tbl:vk-ledger records them.

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

== ZisK Instantiation <sec:instantiation>

The security analysis of @sec:security is stated for the following choices,
which fix the carriers and the maps of @sec:components. Four of them are
built from one _underlying hash function_, and the analysis depends on that
function only through the random-oracle model of @def:rom, never through its
internals. ZisK currently instantiates it with Poseidon2
@AFRICACRYPT:GraKhoSch23, whose arithmetisation-friendly design makes the
recursive circuits cheap; a general-purpose hash such as BLAKE3 @BLAKE3 or
SHA-2 @FIPS180-4 is an equally valid instantiation, and switching among them
changes none of the statements below. The only requirements are those the
analysis names where it uses them: collision resistance of the digest, with
at least $2 lambda$ bits (@sec:discussion), and the random-oracle idealization.

*Bus fingerprint.* The key space is $cal(X) = KK^2$, a key being a _challenge
pair_ $chi = (alpha, gamma)$, and the values lie in $cal(G)_(cal(F)) = KK$.
The fingerprint is LogUp @EPRINT:Habock22b: for $chi = (alpha, gamma)$ the
message $(b, v)$ is _compressed_ to
$hat(e)_gamma (b, v) := b + sum_(j=1)^(ell_b) gamma^j v_j in KK$ and
$
  cal(F)^"LogUp"_chi (D) := sum_((b, v) in "supp" D) frac(D(b, v), alpha + hat(e)_gamma (b, v)),
$
with $cal(F)^"LogUp"_chi (D) := bot$ if some denominator vanishes. It admits
every nonzero multiset, and @lem:logup shows that it is statistically sound
with $epsilon_(cal(F))(Lambda) = (ell dot binom(Lambda, 2) + max(Lambda - 1, 0)) slash abs(KK)$.
The AIR argument does not evaluate this closed form. It constrains a running
sum over the rows of the trace, adding
$m_iota (w, r) slash (alpha + hat(e)_gamma (b_iota, bold(e)_iota (w, r)))$ at
every row through an explicitly constrained inverse, and exposes the final
value $s$. Grouping the row terms by message shows that the exposed value
equals $cal(F)^"LogUp"_chi ("Msg"_tau (w))$ whenever every row denominator is
nonzero. The circuit therefore proves a sub-relation of
$cal(R)_"AIR"^((tau))$: it additionally rejects when a row of zero
multiplicity, or a pair of rows that cancel in the multiset, hits a pole. This
only strengthens the statements of @sec:security, since knowledge soundness
for a sub-relation implies knowledge soundness for the relation.

*Multiset hash.* The accumulator group is $cal(G)_(cal(H)) = ZZ_p^n$ with
$n = 372$, and $h$ and $cal(H)$ are LtHash @ZISK:LTHASH @AC:CDDGS03: $h$
hashes the typed commitment with the underlying hash function and expands the
digest into a pseudorandom vector of $ZZ_p^n$, and $cal(H)$ adds these vectors
with multiplicity. Its collision resistance on multisets of
cardinality below $2^B$ rests on the hardness of the short integer solution
problem @STOC:Ajtai96; the analysis assumes the stronger preimage awareness
(@def:cr), which is the second idealization of @rem:idealized. The cardinality
bound is what the leaf counter enforces.

*Key derivation.* $DeriveKey$ hashes the
accumulated vector with the underlying hash function and reads the digest as
$alpha in KK$; the second component $gamma$ is a
further hash of $alpha$. The analysis treats the pair as a single
random-oracle output (@def:rom) and suppresses the $(Q + 1) slash abs(KK)$
term for a derived $alpha$ colliding with a previously queried input.

*Trace commitment.* $Commit$ is a Merkle tree over the underlying hash
function, so it is straight-line extractable in the random-oracle model
(@def:ext-com).

*Cached-column commitment.* $Commit_"cach"$ is likewise a Merkle tree over
the underlying hash function. The program ROM is the cached column group of the ROM AIR type,
and its root is one of the program's public inputs, so a proof is bound to a
program through $bold(p)$. The analysis requires the leaf commitment
$"com" = Commit(bold(T), bold(a))$ to bind the cached columns as well, since
the challenge accumulator hashes $"com"$ and not $bold(p)$: if the leaf
commitment covered the witness columns only, a prover could choose the ROM
after seeing the key $chi$, and the fingerprint argument of
@prop:bus-soundness would not apply. Either $"com"$ includes the cached
commitment, or the latter must enter the challenge contribution by other
means; this is a circuit requirement to be checked (@sec:discussion).

