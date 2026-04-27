#import "../lib.typ": definition

In this section, we describe the distinct argument types used in ZisK's arithmetization.

== Permutation Argument

A _permutation argument_ proves that two sequences of values are permutations of each other, i.e., they contain the same elements with the same multiplicities but possibly in different orders.

#definition(numbered: false, title: "Permutation Argument")[
  A _permutation argument_ between two AIRs $cal(A)_i$ and $cal(A)_j$ with interaction values $bold(e)_i$ and $bold(e)_j$ and selectors $s_i$ and $s_j$ proves that:
  $
    {bold(e)_i (r) : r in [0, n_i - 1], s_i (r) != 0} = {bold(e)_j (r) : r in [0, n_j - 1], s_j (r) != 0}
  $
  as multisets.
]

Permutation arguments are used when we need to verify that data is reorganized but not modified.

== Lookup Argument

A _lookup argument_ proves that every element in one sequence appears in another sequence (the "table"), without requiring the sequences to have the same length or the same multiplicity distribution.

#definition(numbered: false, title: "Lookup Argument")[
  A _lookup argument_ between two AIRs $cal(A)_("query")$ and $cal(A)_("table")$ proves that for a sequence of query values $bold(e)_("query")$ with selector $s_("query")$ and a table $bold(e)_("table")$ with selector $s_("table")$:
  $
    forall r : s_("query") (r) != 0 arrow.r.double exists r' : s_("table") (r') != 0 and bold(e)_("query") (r) = bold(e)_("table") (r')
  $
  This is expressed with the bus using multiplicities: queries typically contribute $+1$ per active row, and table entries contribute with their lookup count.
]

Lookup arguments are fundamental for range checks, table-driven computations, and verifying that values belong to a predefined set. For example, verifying that a byte value is in the range $[0, 255]$ can be done via a lookup into a table containing all valid byte values.

== Copy Argument

A _copy argument_ proves that designated cells across different parts of the witness hold equal values, establishing equivalence classes among witness cells.

#definition(numbered: false, title: "Copy Argument")[
  A _copy argument_ proves that a set of witness cells forms equivalence classes where all cells in each class have the same value. Given cells $C = {(i_1, r_1), ..., (i_m, r_m)}$ partitioned into equivalence classes ${C_1, ..., C_t}$:
  $
    forall (i, r), (i', r') in C_ell : e_i (r) = e_(i') (r')
  $
  for each equivalence class $C_ell$. This is implemented as a permutation argument on the cells within each equivalence class.
]

Copy arguments are used to enforce consistency between AIRs (not necessarily distinct) that share intermediate values. For example, ensuring that the output of an ALU operation matches the value written to a register, or establishing complex wiring patterns where multiple cells must hold identical values.
