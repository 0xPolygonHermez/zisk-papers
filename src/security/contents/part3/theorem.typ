#import "../../../shared/lib.typ": (
  Adv, Balanced, Bind, BusCont, Com, Commit, DeriveKey, Exp, Local, Pr, Spec, Time, Zisk, definition, fwd, game, lemma,
  mult, negl, poly, proof, proposition, remark, theorem, todo, vk,
)

The results of the previous chapters assemble into the decoding of a
balanced collection of locally satisfying witnesses into an execution of the
committed program. The decoding is deterministic and involves no
cryptography: it adds no error to the bounds of Parts I and II.

#definition(title: "Decoded Execution")[
  For a collection $L$ whose Main witnesses form a chain of $m$ segments, the
  _decoded execution_ $w_L = (P_L, "in", (h_t)_(t < T), (S_t)_(t <= T))$
  has $T = m N$; the program $P_L$ of @lem:rom; as input $"in"$, the values of
  the input data region in its log; as hints $h_t$, the values that the reads
  of step $t$ take from the free-input port; and as states
  $S_t = ("pc"_t, c^"prev"_t, bold(x)_t, "mem"_t)$, with the program counter
  and the output of the previous step of @def:main-steps, the values of the
  registers after step $t - 1$ given by @lem:registers, and the memory of
  @def:mem-of-step. The state $S_T$ takes $"pc"_T := "next"_(T - 1)$ and
  $c^"prev"_T := c_(T - 1)$.
] <def:decoded>

#theorem(title: "Reconstruction of the Execution")[
  Let $(bold(p)_"ext"; (bold(p)_"pv", L)) in cal(R)_Zisk$, let the Rom
  witnesses of $L$ have the same cached columns, with $P_L$ valid, and let the
  obligations of @tbl:obligations hold. Then
  $(bold(p)_"ext"; w_L) in cal(R)_"exec"$.
] <thm:theorem-iii>

#todo[Proof. By induction on $t$, every operand, result, register and memory
word of the steps before $t$ is well formed and $S_(t + 1) =
"Step"_(P_L) (S_t, h_t)$, with a valid step: @lem:main-rows gives the fetch,
the operation and the store of the row of step $t$, @lem:loads that its
loads read $S_t$, and @lem:global-control the next program counter and
output. The initial state, the termination at $"pc"_"END"$ with $c_T = 0$ and
$T <= 2^(36)$ are @lem:global-control and @lem:main-chain; the ROM data
clause is the log of the ROM data region; the program clause is @lem:rom.
For the public outputs, every `pubout` meets the contract $b = "out"_a$ of
the operation bus, and every output message, pushed once by the global
messages and by no chip, is pulled exactly once, by @lem:few-interactions.]
