#import "../../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Spec, Time, Zisk, definition, fwd, game, lemma,
  mult, negl, poly, proof, proposition, remark, theorem, todo, vk,
)

Part II ends with a balanced collection: from an accepting final proof it
extracts proof values $bold(p)_"pv"$ and a typed witness collection $L$ with
$(bold(p)_"ext"; (bold(p)_"pv", L)) in cal(R)_Zisk$, so that every witness is
locally satisfying for $bold(p) = (bold(p)_"ext", bold(p)_"pv")$ and $L$ is
balanced for $bold(p)$. Balance states only that the multiplicities of every
message add up to zero in $FF$. What a message _means_ is a contract between
the chips on its bus. This section turns balance and the
contracts into guarantees: every message that a chip assumes holds, and on the
buses that only count, the messages proved are the messages assumed.

== Pulls and Pushes

#definition(title: "Interactions of a Collection")[
  The _interactions_ of a typed witness collection $L$ for a public statement
  $bold(p)$ form the finite list $cal(J)_bold(p) (L)$ of triples $(b, mu, v)$,
  of a bus, a multiplicity $mu in FF$ and a message $v$, that contains
  $(b_iota, m_iota (w_i, r), bold(e)_iota (w_i, r))$ for every entry
  $(tau_i, w_i)$ of $L$, every interaction $iota in cal(I)_(tau_i)$ and every
  row $r in [0, N_(tau_i))$, and $(b, cal(G)(bold(p))(b, v), v)$ for every global
  message $(b, v)$ in the support of $cal(G)(bold(p))$. An interaction is a
  _pull_ if $mu = -1$, and a _push_ if $mu in.not {0, -1}$.
] <def:interactions-of>

The list has at most $Lambda(L) + g$ entries, and $L$ is balanced for
$bold(p)$ exactly when, for every bus $b$ and message $v$, the multiplicities
of the entries of $cal(J)_bold(p) (L)$ that carry $(b, v)$ add up to zero
(@def:balanced). Whether an interaction pulls or pushes depends on the value of
its multiplicity, not on how the chip writes it. A chip _assumes_ a message
with the multiplicity $-1$ of a selected row, and _proves_ it with any other
nonzero multiplicity, such as the free multiplicity column of a lookup table.

#lemma(title: "Balance with Few Interactions")[
  Let $L$ be balanced for $bold(p)$, with $Lambda(L) + g < p$.
  + For every pull of a message $(b, v)$ in $cal(J)_bold(p) (L)$, there is a
    push of $(b, v)$ in $cal(J)_bold(p) (L)$.
  + If every interaction on the bus $b$ has its multiplicity in ${0, 1, -1}$,
    then every message $v$ is pushed on $b$ exactly as many times as it is
    pulled: the multiset of messages pushed on $b$ is the multiset of messages
    pulled from it.
] <lem:few-interactions>

#proof[
  (1) Suppose that $(b, v)$ is pulled and never pushed. Then every entry that
  carries $(b, v)$ has multiplicity $0$ or $-1$, and $k >= 1$ of them have
  $-1$, so the multiplicities of $(b, v)$ add up to $-k$. Since
  $k <= abs(cal(J)_bold(p) (L)) <= Lambda(L) + g < p$, this is not zero in
  $FF$, which contradicts balance.

  (2) The multiplicities of $(b, v)$ add up to $k_+ - k_-$, where $k_+$ and
  $k_-$ count the entries with multiplicities $1$ and $-1$. Both are below
  $p$, so $k_+ - k_- equiv 0 mod p$ forces $k_+ = k_-$.
]

For a collection of fewer than $2^B$ witnesses, $Lambda(L) + g <=
Lambda_"max"$, so the lemma applies to every collection that Part II extracts
as soon as $Lambda_"max" < p$. In ZisK, with $B = 20$ and trace heights of at
most $2^(22)$, this holds whenever no chip has $2^(21)$ or more interactions
per row, far more than any chip has. The second statement resolves @rem:integer-balance
for the buses whose multiplicities are $0$, $1$ and $-1$; the others need only
the first.

== Contracts

A contract is attached to messages rather than to buses, because some chips of
ZisK both prove and assume messages on the same bus, of different kinds: Arith
proves multiplications and assumes comparisons, both on the Operation Bus. A
bus is therefore split into _channels_ by a key read from the message, such as
the opcode of an operation.

#definition(title: "Channels and Contracts")[
  A _channel assignment_ gives every bus $b$ a function $kappa_b$ on its
  messages, whose values are the _channels_ $(b, kappa_b (v))$ of the bus, and
  gives every channel $c$ either a _predicate_ $Phi_c (bold(p), v)$ on the
  public statement and the messages of $c$, or none. A channel with a
  predicate is a _predicate channel_; a channel without one is a _counted
  channel_. A pull or a push of a message _meets_ its contract if the message
  satisfies the predicate of its channel, or if its channel is counted.
] <def:contracts>

#definition(title: "Sound Chip")[
  Let $R_tau$ be a set of predicate channels and $Spec_tau$ a predicate on
  public statements and witnesses of type $tau$. The chip of type $tau$ is
  _sound_, relying on $R_tau$ and establishing $Spec_tau$, if for every
  $bold(p)$ and every $w in cal(W)_tau$ with $Local_tau (bold(p), w)$ whose
  pulls on the channels of $R_tau$ meet their contracts, every push of $w$
  meets its contract and $Spec_tau (bold(p), w)$ holds. Its pushes on a
  channel $c$ are _unconditional_ if they meet their contract for every
  $w$ with $Local_tau (bold(p), w)$, whatever its pulls.
] <def:sound-chip>

Local soundness alone does not make balance useful: a chip that assumes a
message and proves the same message on every row balances by itself and is
locally sound for any predicate, true or not. What rules this out is an order
in which every guarantee rests on requirements established before it.

#definition(title: "Ordered Chips")[
  Sound chips are _ordered_ by a linear order $<$ on $[M]$ if, for all types
  $sigma$ and $tau$ and every channel $c in R_tau$ on which $sigma$ pushes,
  either $sigma < tau$ or the pushes of $sigma$ on $c$ are unconditional.
] <def:ordered>

In particular no chip relies on a channel on which it pushes conditionally.
The global messages come before every chip: they read only the public
statement, and a channel assignment is _compatible_ with them if every global
message that is pushed meets its contract.

#theorem(title: "System Soundness")[
  Let the chips of ZisK be sound and ordered for a channel assignment
  compatible with the global messages, and let $L$ be balanced for
  $bold(p)$, with $Local_(tau_i) (bold(p), w_i)$ for every entry
  $(tau_i, w_i)$ of $L$ and $Lambda(L) + g < p$. Then:
  + every pull and every push of $cal(J)_bold(p) (L)$ meets its contract;
  + $Spec_(tau_i) (bold(p), w_i)$ holds for every entry of $L$; and
  + on every bus whose interactions have multiplicities in ${0, 1, -1}$, the
    multiset of messages pushed is the multiset of messages pulled.
] <thm:system-soundness>

#proof[
  We show, by induction along the order, that for every type $tau$ every
  entry of type $tau$ meets the contracts of its pushes and satisfies
  $Spec_tau$. Let the claim hold for every type before $tau$, and let $w$ be
  an entry of type $tau$. Every pull of $w$ on a channel $c in R_tau$ carries
  a message $(b, v)$ that, by @lem:few-interactions, is also pushed, on the
  same channel since the channel is a function of the message. The push comes
  from a global message, which meets its contract by compatibility; from an
  entry of a type $sigma < tau$, which meets it by induction; or from an entry
  of a type whose pushes on $c$ are unconditional, which meets it by
  $Local$. In every case $v$ satisfies $Phi_c (bold(p), dot)$, so the pull
  meets its contract too. Since the chip of type $tau$ is sound, every push of
  $w$ meets its contract and $Spec_tau (bold(p), w)$ holds.

  Every push of $cal(J)_bold(p) (L)$ therefore meets its contract, and so does
  every pull, by the same argument: its message is pushed, and a push and a
  pull of the same message are on the same channel. This proves (1) and (2);
  (3) is the second statement of @lem:few-interactions.
]

The theorem gives each assumed message the meaning that its provers
establish, but only up to what the contracts say. Counted channels carry no
predicate: their meaning comes from the third statement, which the memory
argument (@sec:memory) and the stitching of segments (@sec:stitching) turn into
consequences about the execution.

== The Channels of ZisK

The channel assignment of ZisK follows the contracts of the whitepaper, in
the word encoding of @sec:encoding.

#definition(title: "Channels of ZisK")[
  + _Operation bus._ The key of a message
    $("op", a_0, a_1, b_0, b_1, c_0, c_1, "flag", t, x, "extra")$ is its opcode
    $"op"$. For every opcode other than `pubout`, the predicate states that,
    if $a_0, a_1, b_0, b_1 < 2^(32)$, then $c_0, c_1 < 2^(32)$ and
    $(c, "flag") = "op"(a, b)$, for the words $a$, $b$ and $c$ of the limbs
    (@def:words); for a precompile, it states moreover that the memory effect
    of the operation, at step $t$ and with extended argument $x$, is the one
    its prover makes on the Memory Bus, with well-formed limbs. For `pubout`,
    the predicate states that $a < 32$, that $b = "out"_a$, the public output
    of index $a$ in $bold(p)_"ext"$, and that $(c, "flag") = (b, 0)$.
  + _ROM bus._ One channel, whose predicate states that the instruction of the
    committed program at the address of the message has the fields of the
    message.
  + _Table buses._ One channel per bus, whose predicate states that the
    message is a row of the table, or, on a range bus, that its value lies in
    the range.
  + _Memory bus and continuation buses._ Counted channels.
] <def:zisk-channels>

The global messages of ZisK are compatible with this assignment: the only
global messages on a predicate channel are those of the public outputs, which
state $b = "out"_a$ by construction. @sec:chips proves the chips of ZisK sound
for this assignment, or states their soundness as an obligation, and gives
the order.
