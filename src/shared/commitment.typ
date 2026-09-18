#import "../lib.typ": Adv, Com, Commit, Pr, definition, negl

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
