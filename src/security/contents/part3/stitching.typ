#import "../../../lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Spec, Time, Zisk, definition, fwd, game, lemma,
  mult, negl, poly, proof, proposition, remark, theorem, todo, vk,
)

A chip with state is split into segments, each proved on its own, and the
continuation buses chain them. These buses carry no
contract: their meaning comes from counting, which
@cor:zisk-contracts provides. This chapter states what counting gives.

== Chains of Segments

#definition(title: "Chain")[
  A finite list of _segments_, each with an index $k in NN$, a _start_
  payload, an _end_ payload and a _last_ flag, is a _chain from_ $b_0$ _to_
  $b_f$ if, for some $n >= 1$, the indices are $0, dots, n - 1$, one each;
  segment $0$ starts with $b_0$; the segment of index $k + 1$ starts with the
  end of the segment of index $k$; only the segment of index $n - 1$ is last;
  and it ends with $b_f$. It is an _open chain from_ $b_0$ if it satisfies the
  same conditions without the last one.
] <def:chain>

#lemma(title: "Chains by Counting")[
  Let every segment of a list pull the message $(k, "start")$ of its index and
  start, and push $(k + 1, "end")$ if it is not last, and the terminal
  message $"end"$ otherwise, which no indexed message equals; let a global message push $(0, b_0)$ and pull the
  terminal message $b_f$; and let the messages pushed be the messages pulled,
  as multisets, with fewer segments than $p$. Then the segments form a chain
  from $b_0$ to $b_f$. Without the terminal messages and the global pull, they
  form an open chain from $b_0$.
] <lem:chain>

#proof[
  Let $S$ be the list of segments, $n := abs(S) < p$, and fix a bijection
  $beta$ from the pushes to the pulls that preserves messages. The terminal
  messages are pushed by the last segments and pulled once, by the global
  message, so exactly one segment $ell$ is last, and it ends with $b_f$.
  Without the terminal messages, $n$ indexed messages are pulled and
  $1 + (n - k)$ pushed if $k$ segments are last, so again exactly one is.

  Let $s_0$ be the segment whose pull $beta$ matches with the global push of
  $(0, b_0)$, and, for a segment $s$ that is not last, let $"succ"(s)$ be the
  segment whose pull $beta$ matches with the push of $s$. Then $s_0$ has index
  $0$ and starts with $b_0$, and $"succ"(s)$ has index $k_s + 1$ in $FF$ and
  starts with the end of $s$. Since $beta$ is a bijection, $"succ"$ is
  injective, $s_0$ is not in its image, and every other segment is in it.

  Let $s_(i + 1) := "succ"(s_i)$ while $s_i$ is not last. The $s_i$ are
  distinct: for a repetition $s_i = s_j$ with $i < j$ and $i$ minimal,
  $i = 0$ is excluded since $s_0$ is not in the image of $"succ"$, and
  otherwise $s_(i - 1) = s_(j - 1)$ by injectivity. The sequence therefore
  ends, at $ell$. The other segments $R$ are not last, and each is the
  successor of a segment of $R$, so $"succ"$ permutes $R$; along a cycle of
  length $c$ the index increases by $1$ at every step, so $c equiv 0 mod p$,
  which is impossible for $0 < c <= n < p$. Hence $R$ is empty, the segments
  are $s_0, dots, s_(n - 1) = ell$, and $s_i$ has index $i$ in $FF$, which is
  the integer $i$ since $i < p$.
]

== Main and Memory Segments

#lemma(title: "Main Segments")[
  Under the hypotheses of @cor:zisk-contracts, the Main witnesses of $L$
  form a chain from $("pc"_"BOOT", 0)$ to $("pc"_"END", 0)$ for the payloads
  $("pc"^"in", c^"in")$ and $("pc"^"out", c^"out")$ of @lem:main-rows. If
  there are $m$ of them, $m N <= 2^(36)$.
] <lem:main-chain>

#todo[Proof: @lem:chain on the Main continuation bus, whose messages are
  $(j, "last", "pc", c_0, c_1)$, with the genesis and terminus anchors of the
  global messages; the range check of the segment index gives $m N <= 2^(36)$.]

#lemma(title: "Memory Segments")[
  Under the hypotheses of @cor:zisk-contracts, the witnesses of the Memory
  AIR of a region form an open chain from the genesis payload of the region,
  if the region is enabled, and there are none otherwise. Their rows,
  concatenated in the order of the chain, form one log of the region.
] <lem:mem-chain>

#todo[Proof: @lem:chain on the memory continuation bus, whose messages carry
  the base address of the region, and @lem:mem-rows for each segment; a
  region whose genesis anchor is switched off by its proof value has no start,
  hence no segment.]

The continuation buses of the DMA workers carry the operation in flight
across a segment boundary. That they form chains, so that every bulk
operation is processed once and completely, is part of the obligations on the
DMA chips (@tbl:obligations).

== The Global Step

#definition(title: "Steps of the Main Segments")[
  Let the Main witnesses of $L$ form a chain of $m$ segments. Row $r$ of the
  segment of index $j$ _executes_ step $t = j N + r$, for $t < T := m N$, and
  we write $"pc"_t$, $a_t$, $b_t$, $c_t$ and $c^"prev"_t$ for the values of
  that row.
] <def:main-steps>

#lemma(title: "Global Control Flow")[
  Under the hypotheses of @cor:zisk-contracts, every step $t < T$ is executed
  by exactly one row; $"pc"_0 = "pc"_"BOOT"$ and $c^"prev"_0 = 0$;
  $"pc"_(t + 1) = "next"_t$ and $c^"prev"_(t + 1) = c_t$ for $t + 1 < T$; and
  $"next"_(T - 1) = "pc"_"END"$ and $c_(T - 1) = 0$.
] <lem:global-control>

#proof[
  By @lem:main-chain the segments have the indices $0, dots, m - 1$, one each,
  so $(j, r) |-> j N + r$ is a bijection from their rows to $[0, T)$. By
  @cor:zisk-contracts every Main witness satisfies @lem:main-rows. Within a
  segment, its control statement gives $"pc"_(t + 1) = "next"_t$, and
  $c^"prev"_(t + 1) = c_t$ by the definition of $c^"prev"$. Across the
  boundary between the segments $j$ and $j + 1$, the segment $j + 1$ starts
  with the end of the segment $j$, so its first row has
  $"pc" = "pc"^"in" = "pc"^"out" = "next"_t$ and
  $c^"prev" = c^"in" = c^"out" = c_t$ for $t = (j + 1) N - 1$. The segment $0$
  starts with $("pc"_"BOOT", 0)$, which gives $"pc"_0$ and $c^"prev"_0$, and
  the segment $m - 1$ ends with $("pc"_"END", 0)$, which gives
  $"next"_(T - 1)$ and $c_(T - 1)$.
]
