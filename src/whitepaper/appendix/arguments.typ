#import "../../lib.typ": definition

This appendix gives the formal statements of the argument types used in ZisK's arithmetization framework. All are realised through the same bus-balancing primitive of @sec:circuits-and-balancing ---one or more sender interactions with positive multiplicity, one or more receiver interactions with negative multiplicity, on a shared bus--- but they differ in the semantic relationship they enforce on the messages.

Throughout this appendix we fix the chips $(cal(C)_i, cal(I)_i)$, $i in [M]$, of ZisK, with witnesses ${(bold(T)_i, bold(a)_i)}_(i=1)^M$, and we write $m(r), bold(e)(r) in FF^ell$ for the row-$r$ evaluation of an interaction $(b, m, bold(e))$ under its witness.

== Permutation Argument

A _permutation argument_ enforces that two AIRs observe the same multiset of messages on a shared bus. It is the natural primitive whenever data is reordered ---e.g., between unsorted and sorted views of the same memory accesses--- but not modified.

#definition(numbered: false, title: "Permutation Argument")[
  Let $iota_1 = (b, m_1, bold(e)_1) in cal(I)_(i_1)$ and $iota_2 = (b, -m_2, bold(e)_2) in cal(I)_(i_2)$ be a sender/receiver pair of interactions of common length $ell$ on a shared bus $b$, with boolean multiplicities $m_1, m_2 in {0, 1}$. The pair $(iota_1, iota_2)$ realises a _permutation argument_ in the sense that the joint contribution of $iota_1$ and $iota_2$ to bus $b$ vanishes if and only if
  $
    {bold(e)_1 (r) : r in [N_(i_1)], m_1 (r) = 1} = {bold(e)_2 (r) : r in [N_(i_2)], m_2 (r) = 1}
  $
  as multisets.
]

== Lookup Argument

A _lookup argument_ enforces that every message sent on the bus by a "query" AIR also appears as a row of a "table" AIR, with the table free to receive each query any number of times.

#definition(numbered: false, title: "Lookup Argument")[
  Let $iota_q = (b, m_q, bold(e)_q) in cal(I)_(i_q)$ be a _query_ interaction with boolean multiplicity $m_q in {0, 1}$, and $iota_t = (b, -m_t, bold(e)_t) in cal(I)_(i_t)$ a _table_ interaction with $m_t (r) >= 0$ counting how many queries land on row $r$ of the table. Both interactions have common length $ell$. The pair $(iota_q, iota_t)$ realises a _lookup argument_ in the sense that their joint contribution to bus $b$ vanishes if and only if
  $
    forall r in [N_(i_q)] " with " m_q (r) = 1 : exists r' in [N_(i_t)] " s.t. " bold(e)_q (r) = bold(e)_t (r').
  $
]

Lookup arguments underpin most of ZisK's table-driven constraints: instruction decoding, byte and limb decompositions, and any check whose efficient form is "the output of a sub-chip must belong to a precomputed table".

== Range Check Argument

A _range check argument_ enforces that an expression takes values in a bounded interval. It is a specialisation of the lookup argument against a fixed interval table, but it is exposed as a first-class primitive because its receiving side is a shared system table rather than an AIR-specific one.

#definition(numbered: false, title: "Range Check Argument")[
  Fix integers $x <= y$ and let $b$ be the bus designated for the range check on $[x, y]$. Let $iota = (b, m, e) in cal(I)_i$ be an interaction of length $ell = 1$ with boolean multiplicity $m in {0, 1}$, paired with a receiver interaction $iota_t = (b, -m_t, e_t)$ on a dedicated table AIR whose trace materialises the set ${x, x+1, dots, y}$ and whose multiplicity $m_t (r) >= 0$ counts how many incoming queries land on each value. The pair $(iota, iota_t)$ realises a _range check argument_ on $[x, y]$ in the sense that their joint contribution to bus $b$ vanishes if and only if
  $
    forall r in [N_i] " with " m (r) = 1 : e (r) in [x, y].
  $
]

In practice ZisK shares each range-check table across all the chips: a single $[x, y]$ table absorbs queries from every AIR that needs that range, so the marginal cost of a range check is one row of querying plus one row of multiplicity bookkeeping in the shared table.

== Copy Argument

A _copy argument_ asserts that a designated set of cells in a single AIR's trace hold equal values. It is the wiring primitive used inside an AIR to relate values that must coincide but live in different rows or columns ---for instance, feeding the output of one row back as the input of a later row, or forcing two columns to agree on a shared intermediate value.

#definition(numbered: false, title: "Copy Argument")[
  Let $cal(C)$ be an AIR with witness $(bold(T), bold(a))$, and let $C = { (r_1, j_1), dots, (r_q, j_q) }$ be a finite set of _cell coordinates_ in $bold(T)$, each $(r, j)$ identifying the cell at row $r$ of column $j$. Let ${C_1, dots, C_t}$ be a partition of $C$ into _equivalence classes_. A _copy argument_ for $(C, {C_ell})$ enforces:
  $
    forall ell in [t], forall (r, j), (r', j') in C_ell : T_(j,r) = T_(j',r').
  $
  Operationally, a copy argument is realised as a permutation argument applied class-by-class: for each $C_ell$, the values at all cells in $C_ell$ are sent on a dedicated bus and required to coincide as multisets with the same values shifted by an arbitrary cycle on $C_ell$ ---this forces every pair of cells in the class to agree.
]
