#import "../../lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, fwd, game, lemma, mult,
  negl, poly, proof, proposition, prover, remark, theorem, todo, verifier, vk,
)
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

This section describes the system that the rest of the paper analyzes: the
aggregation tree into which a ZisK proof is organized, the three accumulators
that its nodes carry, the relation attested by each kind of node, and the
concrete choices ZisK makes for the components of @sec:preliminaries. Part I
proves knowledge soundness for the argument systems that attest to these
relations, Part II shows what an accepting proof of the whole tree implies,
and Part III gives the result its meaning in terms of program execution.

== Structure <sec:tree>

A ZisK proof is a tree. Its leaves are the AIR instances of an execution: for
each type $tau in [M]$ the prover produces some number of witnesses in
$cal(W)_tau$, one per segment of that type, and proves each with an argument
system for the AIR of the type. Directly above every AIR proof sits a _leaf
verifier_, which verifies the AIR proof and re-exposes its statement
in a common format. Above the leaf verifiers, _aggregation nodes_ have $A$
child slots each, where $A$ is the aggregation arity. A slot holds either a child proof or a _null child_, a
placeholder that is not verified and contributes nothing, and at least two
slots of every aggregation node hold proofs. The tree need not be balanced,
because a node is proved as soon as enough children are available. At the
top, a single _Final Verifier_ verifies the root of the aggregation tree and
performs the global checks; its statement, the external statement
$bold(p)_"ext"$, is the only thing an external verifier sees. @fig:aggregation-tree shows an example with
three leaves. The leaf verifiers, the aggregation nodes and the Final
Verifier are the _recursive verifiers_: each is itself an AIR, whose
constraints encode a verifier, and is proved with the same argument system as
the chips (#fwd(<sec:stark>)[Part I]).

Three quantities travel up the tree and are combined at every aggregation
node: the number of leaves, an accumulation of the leaves' commitments, and an
accumulation of the leaves' bus contributions. They are the _accumulators_ of
@sec:accumulators; the counter is range-checked at every node, and the Final
Verifier checks one condition on each.

The order of operations matters for the bus argument. Bus contributions are
fingerprints under a key $chi$, and the key must be fixed before any leaf is
proved yet must not be under the prover's control. ZisK derives it from the
leaves themselves: the prover commits to every witness, accumulates the typed
commitments with the multiset hash $cal(H)$, derives $chi$ from the public
statement and the accumulated value with $DeriveKey$, and only then proves the
leaves with $chi$ as a public input. The tree recomputes the accumulation as it
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
      #sub[$verifier_"REC"[vk](pi_L), verifier_"REC"[vk](pi_R) = 1$] #linebreak()
      #sub[$sans("Typed")(tau_L, kappa_L), quad sans("Typed")(tau_R, kappa_R)$] #linebreak()
      #sub[$kappa = kappa_L + kappa_R, quad s = s_L + s_R$] #linebreak()
      #sub[$bold(c) = bold(c)_L + bold(c)_R$]
    ]
    let lv-body = align(center)[
      *Leaf verifier* $tau$ #linebreak()
      #sub[$verifier_"AIR"^((tau))(pi_"AIR") = 1$] #linebreak()
      #sub[$kappa = 1, quad bold(c) = h(tau, "com")$]
    ]
    let air-body = align(center)[*AIR instance* #linebreak() #sub[type $tau$, witness $w$]]

    diagram(
      spacing: (0.7cm, 1.15cm),
      label-sep: 2pt,

      // External verifier
      node((0, -0.75), align(center)[*External verifier*], stroke: 0.5pt + luma(120), inset: 3pt, corner-radius: 2pt),
      edge((0, 0), (0, -0.75), lbl[$bold(p)_"ext"\, pi_"FINAL"$], "->", stroke: arr, label-side: right),

      // Final Verifier
      node(
        (0, 0),
        align(center)[
          *Final Verifier* #linebreak()
          #sub[$verifier_"REC"[vk_"AGG"](pi) = 1$] #linebreak()
          #sub[$sans("Typed")(tau, kappa), quad s + cal(F)_chi (cal(G)(bold(p))) = 0$] #linebreak()
          #sub[$chi = DeriveKey(bold(p), bold(c))$]
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
    exposes only $bold(p)_"ext"$. The dashed arrows are the public inputs common to
    every leaf. Aggregation nodes are drawn with two children; in general they
    have $A$ slots, the unused ones holding null children.
  ],
) <fig:aggregation-tree>

== Accumulators <sec:accumulators>

#definition(title: "Accumulator")[
  An _accumulator_ over the aggregation tree consists of a commutative monoid
  of _values_, a _leaf contribution_ assigning a value to every leaf, a
  _child check_, a predicate on values that every aggregation node evaluates
  on the value of each of its children, and a _root check_, a predicate on
  values that the Final Verifier evaluates on the value of the root of the
  aggregation tree. The value of a leaf is its
  contribution, and the value of an aggregation node is the sum of the values
  of its non-null children. By associativity and commutativity, the value of any
  node is the sum of the contributions of the leaves below it, whatever the
  shape of the subtree.
] <def:accumulator>

The recursion carries three accumulators. Their values at a node, together
with the node's type, form the _recursive statement_
$
  sigma = (tau, kappa, bold(c), s),
$
where the type $tau in [M + 1]$ is the type of the verified chip for a leaf verifier and the
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
      [$(G_(cal(H)), +)$],
      [$h(tau, "com")$],
      [---],
      [$chi = DeriveKey(bold(p), bold(c))$],

      [bus partial sum $s$],
      [$(G_(cal(F)), +)$],
      [$cal(F)_chi ("Msg"_tau (w))$],
      [---],
      [$s + cal(F)_chi (cal(G)(bold(p))) = 0$],
    )
  },
  caption: [The three accumulators of the recursion.],
  kind: table,
) <tbl:accumulators>

The counter is added in $FF$. Its child check is the following predicate on a
node's type and counter, which every aggregation node applies to each
non-null child and the Final Verifier applies to the root.

#definition(title: "Typing Predicate")[
  For a type $tau$ and a counter $kappa$,
  $
    sans("Typed")(tau, kappa) := (tau in [M] and kappa = 1) or (tau = M + 1 and 2 <= kappa < 2^B).
  $
] <def:typed>

The typing predicate places every counter in $[1, 2^B)$,
and $A dot 2^B <= p$ then rules out wrap-around, so the field sums are integer
sums and no node has $2^B$ or more leaves below it. The other two
accumulators are checked only at the root. The value of the
challenge accumulator at a node is $cal(H)$ of the multiset of typed
commitments below it, by the homomorphism of $cal(H)$; the value of the bus
partial sum is $cal(F)_chi$ of the summed message multisets below it, by the
additivity of $cal(F)$, so at the root it equals $cal(F)_chi (cal(M)_L)$ for
the collection $L$ of all leaves. The Final Verifier adds the contribution
$cal(F)_chi (cal(G)(bold(p)))$ of the global messages, which it computes
itself from the public statement and the key, so its root check
$s + cal(F)_chi (cal(G)(bold(p))) = 0$ is a fingerprint test on
$cal(M)_L + cal(G)(bold(p))$.

An update rule that is not associative and commutative would make the root
value depend on the shape of the tree, which is not known when the key is
derived (@sec:tree); a hash-tree accumulation
$bold(c) = H(bold(c)_1, bold(c)_2, bold(c)_3)$, for instance, would force the prover to
fix the tree before deriving $chi$. Writing every update as the monoid sum
therefore loses no generality.

== Recursive Relations <sec:relations-def>

We write a relation as $cal(R) = { (bb(x); bb(w)) mid(|) phi(bb(x), bb(w)) }$ with public
statement $bb(x)$, witness $bb(w)$ and _defining predicate_ $phi$; in the definitions
below, $phi$ is the conjunction of the clauses displayed to the right of the
bar. Every node statement below the Final Verifier
carries the public statement $bold(p) in cal(P)$, a key $chi in cal(X)$, a
recursive statement $sigma$ and a verification key $vk$. We proceed from the
leaves to the root, naming after each relation the argument system that
proves it, since the relation above uses its verifier.

#definition(title: "AIR Relation")[
  For $tau in [M]$,
  $
    cal(R)_"AIR"^((tau)) = lr(
      {
        cases(
          delim: #none,
          ,
          (bold(p), chi\, s\, "com")\; w,
          ,
        )
        mid(|)
        cases(
          delim: #none,
          gap: #(0pt + 0.4em),
          Local_tau (bold(p), w),
          and quad s = BusCont_chi (cal(I)_tau, w),
          and quad Commit(w) = "com"
        )
      }
    )
  $
  with $bold(p) in cal(P)$, $chi in cal(X)$, $s in G_(cal(F))$ and
  $w = (bold(T), bold(v)) in cal(W)_tau$.
] <def:r-air>

The relation is in _commit-and-prove_ form: the trace commitment is part of
the statement. A proof for $cal(C)_tau$ already contains this
commitment, so $verifier_"AIR"^((tau))$ simply reads it off the proof and compares it
with the statement component; the point of exposing it is that the leaf
verifier can then bind the challenge contribution to a value that is a
function of the statement and witness rather than of an object that occurs in
neither.

Let $Pi_"AIR"^((tau))$ be an argument system for $cal(R)_"AIR"^((tau))$, one
per type, with verifier $verifier_"AIR"^((tau))$ and key $vk_"AIR"^((tau))$.

#definition(title: "Leaf-Verifier Relation")[
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
          and quad verifier_"AIR"^((tau))((bold(p), chi, s, "com"), pi_"AIR") = 1,
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
with verifier $verifier_"LEAF"^((tau))$ and key $vk_"LEAF"^((tau))$; it
hard-codes $vk_"AIR"^((tau))$.

An aggregation node must verify children of every kind, leaf verifiers of any
type and other aggregation nodes. It hard-codes the $M$ leaf-verifier keys and
selects among them by the child's type; for an aggregation child it uses a
key that it does not hard-code but reads from its own statement. The reserved
type $0$ marks a null child.

#definition(title: "Recursive Dispatch")[
  #set math.cases(gap: 1em)
  For a type $tau in [M + 1]$ and a key $vk$, the _dispatched verifier_ is
  $
    verifier_"REC"^((tau)) [vk](bb(x), pi) := cases(
      verifier_"LEAF"^((tau))(bb(x), pi) & "if" tau in [M]\,,
      verifier(vk, bb(x), pi) & "if" tau = M + 1\,,
    )
  $
  and $verifier_"REC"^((tau))[vk]$ rejects everything if $tau in.not [M + 1]$; in
  particular a null child ($tau = 0$) never passes the dispatched verifier.
] <def:dispatch>

The dispatch is a function of the key $vk$ carried in the statement; the
typing predicate of @def:typed is what makes the counter meaningful.

#definition(title: "Aggregation Relation")[
  Write $bb(x)_X := (bold(p), chi, sigma_X, vk)$ for the statement of the child
  in slot $X in [A]$, $sigma_X = (tau_X, kappa_X, bold(c)_X, s_X)$ for its
  recursive statement, and $N := {X in [A] : tau_X != 0}$ for the set of
  non-null slots. Then
  $
    cal(R)_"AGG" = lr(
      {
        cases(
          delim: #none,
          ,
          (bold(p), chi\, sigma\, vk)\; ((sigma_X, pi_X))_(X in [A]),
          ,
        )
        mid(|)
        cases(
          delim: #none,
          gap: #(0pt + 0.4em),
          sigma = (M + 1, kappa, bold(c), s) "and" abs(N) >= 2,
          and quad sans("Typed")(tau_X, kappa_X) "for" X in N,
          and quad verifier_"REC"^((tau_X))[vk](bb(x)_X, pi_X) = 1 "for" X in N,
          and quad kappa = sum_(X in N) kappa_X "and" bold(c) = sum_(X in N) bold(c)_X "and" s = sum_(X in N) s_X
        )
      }
    )
  $
  Null slots carry no constraint: their proofs are not verified and their
  recursive statements do not enter the sums.
] <def:r-agg>

Two invariants of this relation are used repeatedly. First, the
_propagation invariant_: every non-null child is verified on a statement that
carries the parent's own $(bold(p), chi, vk)$, so every node of a valid tree
carries the root's public statement, fingerprint key and verification key; in
particular an aggregation child is verified under $verifier(vk, dot, dot)$ for the
very $vk$ the parent declares. Since the cached-column commitments travel in
$bold(p)$ (@def:columns), the binding of $Commit_"cach"$ then makes the cached
columns of all leaves of one type equal. Second, the _counter invariant_: $sans("Typed")$
places the counters of the non-null children in $[1, 2^B)$, there are at
least two and at most $A$ of them, and $A dot 2^B <= p$ makes $kappa = sum_(X in N) kappa_X$
an identity of integers; hence every non-null child has
$kappa_X <= kappa - 1$.

Let $Pi_"AGG"$ be an argument system for $cal(R)_"AGG"$, with verifier
$verifier_"AGG"$ and key $vk_"AGG"$. There is no circularity: $cal(R)_"AGG"$ is one
ordinary relation over statements that contain an arbitrary string $vk$, the
key $vk_"AGG"$ of the argument system for that relation is produced afterwards
at setup, and the Final relation below fixes $vk := vk_"AGG"$, at which point
$verifier_"REC"^((M+1))[vk_"AGG"] = verifier_"AGG"$.

#definition(title: "Final Relation")[
  Fix the aggregation key $vk_"AGG"$ as a parameter. Then, with
  $bold(p) := (bold(p)_"ext", bold(p)_"pv")$,
  $
    cal(R)_"FINAL" = lr(
      {
        cases(
          delim: #none,
          ,
          bold(p)_"ext"\; (bold(p)_"pv", chi, sigma, pi),
          ,
        )
        mid(|)
        cases(
          delim: #none,
          gap: #(0pt + 0.4em),
          sigma = (tau, kappa, bold(c), s) "and" sans("Typed")(tau, kappa),
          and quad verifier_"REC"^((tau))[vk_"AGG"]((bold(p), chi, sigma, vk_"AGG"), pi) = 1,
          and quad s + cal(F)_chi (cal(G)(bold(p))) = 0,
          and quad chi = DeriveKey(bold(p), bold(c))
        )
      }
    )
  $
] <def:r-final>

Only the external statement $bold(p)_"ext"$ survives at the root: the proof
values, the fingerprint key, the recursive statement and the child proof are
witnesses. The typing predicate excludes a null child at the root, which would
otherwise leave $bold(c)$ and $s$ unconstrained. Dispatching on
$tau$ lets the Final Verifier accept a leaf-verifier proof directly when the
execution fits in a single AIR instance.

Let $Pi_"FINAL"$ be an argument system for $cal(R)_"FINAL"$, with verifier
$verifier_"FINAL"$ and key $vk_"FINAL"$; this is the verifier run by the external
party. The verification keys involved play different roles. @tbl:vk-ledger records them.

#figure(
  table(
    stroke: 0.3pt,
    columns: (18%, 47%, 35%),
    align: (left, left, left),
    table.header([*Key*], [*Selected by*], [*Hard-coded in*]),
    [$vk_"AIR"^((tau))$], [the type $tau$ of the leaf verifier], [$Pi_"LEAF"^((tau))$],
    [$vk_"LEAF"^((tau))$], [the child type $tau_X in [M]$ read from the child statement], [$Pi_"AGG"$ (all $M$ keys)],
    [$vk_"AGG"$], [the child type $tau_X = M + 1$; the key itself arrives as the public $vk$], [$Pi_"FINAL"$ only],
    [$vk_"FINAL"$], [---], [the external verifier],
  ),
  caption: [
    Verification-key ledger. The type $tau$ selects which hard-coded
    key an aggregation node uses for a child; the propagated public $vk$ is
    the aggregation verifier's own key, which no aggregation node can
    hard-code and which the Final Verifier fixes.
  ],
  kind: table,
) <tbl:vk-ledger>

== ZisK Instantiation <sec:instantiation>

The security analysis is stated for the following choices,
which fix the carriers and the maps of @sec:components. Four of them are
built from one _underlying hash function_, and the analysis depends on that
function only through the random-oracle model of @def:rom, never through its
internals. ZisK currently instantiates it with Poseidon2
@AFRICACRYPT:GraKhoSch23, whose arithmetisation-friendly design makes the
recursive verifiers cheap; a general-purpose hash such as BLAKE3 @BLAKE3 or
SHA-2 @FIPS180-4 is an equally valid instantiation, and switching among them
changes none of the statements below. The only requirements are those the
analysis names where it uses them: collision resistance of the digest, with
at least $2 lambda$ bits (#fwd(<sec:discussion>)[Part IV]), and the random-oracle idealization.

*Bus fingerprint.* The key space is $cal(X) = KK^2$, a key being a _challenge
pair_ $chi = (alpha, gamma)$, and the values lie in $G_(cal(F)) = KK$.
The fingerprint is LogUp @EPRINT:Habock22b: for $chi = (alpha, gamma)$ the
message $(b, v)$ is _compressed_ to
$hat(e)_gamma (b, v) := b + sum_(j=1)^(ell_b) gamma^j v_j in KK$ and
$
  cal(F)^"LogUp"_chi (D) := sum_((b, v) in "supp" D) frac(D(b, v), alpha + hat(e)_gamma (b, v)),
$
with $cal(F)^"LogUp"_chi (D) := bot$ if some denominator vanishes. It admits
every nonzero multiset, and #fwd(<lem:logup>)[Part II] shows that it is statistically sound
with $epsilon_(cal(F))(Lambda) = (ell dot binom(Lambda, 2) + max(Lambda - 1, 0)) slash abs(KK)$.
The AIR argument does not evaluate this closed form. It constrains a running
sum over the rows of the trace, adding
$m_iota (w, r) slash (alpha + hat(e)_gamma (b_iota, bold(e)_iota (w, r)))$ at
every row through an explicitly constrained inverse, and exposes the final
value $s$. Grouping the row terms by message shows that the exposed value
equals $cal(F)^"LogUp"_chi ("Msg"_tau (w))$ whenever every row denominator is
nonzero. At a pole the constraints do not determine $s$: a row of zero
multiplicity whose denominator vanishes satisfies its fraction constraint for
every value of the fraction column. The poles of a witness are at most
$N_tau abs(cal(I)_tau)$ values of $alpha$ for each $gamma$, fixed by the
witness, and the key is derived after the commitment to the witness; the
probability of hitting one is charged in #fwd(<lem:binding>)[the binding lemma of Part I].

*Multiset hash.* The accumulator group is $G_(cal(H)) = ZZ_p^n$ with
$n = 368$, and $h$ and $cal(H)$ are LtHash @ZISK:LTHASH @AC:CDDGS03: $h$
absorbs the typed commitment into a sponge of the underlying hash function
and expands it, by $22$ further permutations, into a pseudorandom vector of
$ZZ_p^n$ (the $23$ states of width $16$). The type enters $h$ as the root of
the type's fixed columns, which identifies the type provided that no two types
have the same fixed columns, and $cal(H)$ adds these vectors
with multiplicity. Its collision resistance on multisets of
cardinality below $2^B$ rests on the hardness of the short integer solution
problem @STOC:Ajtai96; the analysis assumes the stronger preimage awareness
(@def:cr), which is the second idealization of @rem:idealized. The cardinality
bound is what the leaf counter enforces.

*Key derivation.* $DeriveKey$ hashes the public statement $bold(p)$ ---the
external statement and the proof values--- and the accumulated vector with the
underlying hash function into a _global challenge_ in $KK$, from which a fresh
sponge squeezes the pair $(alpha, gamma)$. The analysis treats the pair as a single
random-oracle output (@def:rom) and suppresses the $(Q + 1) slash abs(KK)$
term for a derived $alpha$ colliding with a previously queried input.

*Trace commitment.* $Commit$ is a Merkle tree over the underlying hash
function, so it is straight-line extractable in the random-oracle model
(@def:ext-com).

*Cached-column commitment.* $Commit_"cach"$ is likewise a Merkle tree over
the underlying hash function. The program ROM is the cached column group of
the ROM chip, and its root is one of the publics, so a
proof is bound to a program through $bold(p)$. The leaf commitment
$"com"$ covers the witness columns and the AIR values of the first stage, not
the cached columns; this is sound because $DeriveKey$ absorbs $bold(p)$, and
with it the cached-column commitment, so the cached columns are fixed before
the key $chi$ is derived, exactly as the committed witnesses are.
