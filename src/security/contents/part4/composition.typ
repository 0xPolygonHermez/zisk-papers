#import "../../../lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Time, Zisk, definition, fwd, game, lemma, mult,
  negl, poly, proof, proposition, remark, theorem, todo, verifier, vk,
)

The three parts compose into the statement that the paper set out to prove:
an accepting final proof certifies an execution of the committed program.
Part II extracts, from an accepting final proof, a balanced collection of
locally satisfying witnesses; Part I bounds the knowledge-soundness errors
that this extraction is charged with; and Part III decodes the collection into
an execution, adding no error.

== Execution Extractability

The external verifier checks a proof for a given program: it compares the
program commitment of the statement with the commitment of the program it
expects. The guarantee is therefore stated for a fixed program.

#definition(title: "Execution Extractability")[
  Let $P^*$ be a valid program (@sec:valid-programs) and $Pi^*$ the final
  argument system of ZisK (@def:final-as). For an extractor $cal(E)$ and a
  PPT adversary $cal(A)$, let $Adv("exec", P^*)(cal(A))$ be the probability
  that $cal(A)$ outputs $(bold(p)_"ext", pi)$ with
  $verifier^* (bold(p)_"ext", pi) = 1$ and $"root"_"ROM" = "RomRoot"(P^*)$,
  while $(bold(p)_"ext"; cal(E)(bold(p)_"ext", pi)) in.not cal(R)_"exec"$.
  ZisK is _execution-extractable_ for $P^*$ if there is an extractor, with the
  running time of @def:ks, for which this advantage is negligible.
] <def:exec-extract>

The definition is knowledge soundness in the sense of @def:ks for the
relation $cal(R)_"exec"$, restricted to the statements that commit to
$P^*$, in the random-oracle model of @def:rom and with a straight-line
extractor.

#theorem(title: "Main Theorem")[
  Let $P^*$ be a valid program, and assume the idealizations of
  @rem:idealized; that the AIR of every recursive verifier enforces its
  relation (@def:enforces); and the obligations of @tbl:obligations. Then for
  every PPT adversary $cal(A)$ that, together with the extractors composed with
  it, makes at most $Q$ random-oracle queries, there are reduction
  adversaries $cal(D)^"pa"$ and $cal(D)^"bind"$, running in time
  $O(kappa_"max") dot Time(cal(A)) + poly(lambda)$, such that
  $
    Adv("exec", P^*)(cal(A)) <= & epsilon_"rec" + Q dot epsilon^* + epsilon_"MT" (Q)
                                  + frac(Q dot Lambda_"pole", abs(KK)) + (Q + 1) dot epsilon_(cal(F))(Lambda_"max") \
                                & + Adv("pa", cal(H))(cal(D)^"pa") + Adv("bind", Com_"cach")(cal(D)^"bind"),
  $
  where the recursive arguments contribute
  $
    epsilon_"rec" := & epsilon_"ks" (Pi_"FINAL") + (kappa_"max" - 1) dot epsilon_"ks" (Pi_"AGG")
                       + kappa_"max" dot max_(tau in [M]) epsilon_"ks" (Pi_"LEAF"^((tau)))
                       + kappa_"max" dot max_(tau in T_"COMP") epsilon_"ks" (Pi_"COMP"^((tau))),
  $
  with $epsilon_"ks" (Pi_X) := Q dot epsilon^*_(Pi_X) + epsilon_"MT" (Q)$ the
  bound of @thm:arguments for the argument $Pi_X$.
] <thm:final>

#proof[
  The extractor runs the extractor $cal(E)_Zisk$ of @thm:main and decodes
  its output by @def:decoded. Let $cal(A)$ output $(bold(p)_"ext", pi)$,
  accepted, with $"root"_"ROM" = "RomRoot"(P^*)$.

  _Extraction._ By @thm:main, except with the probability that its bound
  states, $cal(E)_Zisk$ outputs $(bold(p)_"pv", L)$ with
  $(bold(p)_"ext"; (bold(p)_"pv", L)) in cal(R)_Zisk$. In that bound, every
  knowledge-soundness advantage of a recursive argument $Pi_X$ is at most
  $epsilon_"ks" (Pi_X)$ by the second statement of @thm:arguments, which
  applies since the AIR of its verifier enforces its relation; this gives
  $epsilon_"rec"$ and the remaining terms.

  _Program._ Every Rom witness of $L$ is locally satisfying, so its cached
  columns open $"root"_"ROM" = "RomRoot"(P^*)$. If the cached columns of some
  Rom witness are not the table of $P^*$, the adversary $cal(D)^"bind"$ that
  runs $cal(A)$ and $cal(E)_Zisk$ and outputs these columns together with the
  table of $P^*$ breaks the binding of $Com_"cach"$. Otherwise all the Rom
  witnesses have the same cached columns, and $P_L = P^*$ is valid.

  _Decoding._ In that case @thm:theorem-iii, under the obligations of
  @tbl:obligations, gives $(bold(p)_"ext"; w_L) in cal(R)_"exec"$, without
  further error. Summing the failure probabilities gives the bound. The
  reductions run $cal(A)$ once and the extraction chain of @thm:main, whose
  time @thm:main bounds, and the decoding is linear in the size of $L$.
]

The theorem is the composition of statements, three of which are proved in
this paper as stated ---@thm:arguments in Part I and @thm:main in Part II---
and one of which, @thm:theorem-iii, is stated in Part III together with the
lemmas it rests on, some of whose proofs are left to a machine-checked
formalization.
@sec:discussion records every assumption and obligation the theorem rests on.

#remark(numbered: true, title: "Concrete Reading")[
  The dominant terms are $Q dot epsilon^*$ and the knowledge-soundness
  errors of the recursive arguments, each about $Q$ times the query error of
  @tbl:security, and multiplied by $kappa_"max" = 2^(20) - 1$ for the leaf
  verifiers and the compressors. Every other term is negligible for
  $abs(KK) approx 2^(192)$. The factor $kappa_"max"$ comes from bounding the
  extractions layer by layer, and @rem:query-budget explains how a single union
  bound over the queries would remove it. With $B = 20$, $kappa_"max"
  approx 10^6$, and the extractor runs in time
  $(3 kappa_"max" + 2) dot Time(cal(A)) + poly(lambda)$ (@thm:main), about
  $3 dot 10^6$ times that of the adversary. Together with the idealizations of
  @rem:idealized, the bound should be read as a statement about the structure
  of the reduction rather than as a concrete security level.
] <rem:concrete>
