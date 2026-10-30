#import "../../shared/lib.typ": definition

A single chip proof covers a trace of fixed height $N$. Real programs run for an a priori unbounded number of steps, so a single proof cannot certify an arbitrary execution. _Continuations_ are the mechanism by which a zkVM extends beyond this bound: the execution is divided into _segments_, each covered by an independent proof, and the proofs are linked into a single argument for the full run.

== The Standard Approach to Continuations

The most common continuation strategy splits execution into _checkpointed_ segments. Execution runs for $N$ steps, halts, and the prover generates a proof for those $N$ steps; the machine state at the halt ---the _checkpoint_--- is saved. A fresh execution then resumes from that checkpoint and runs for another $N$ steps, and so on. Each segment proof certifies one $N$-step block, and consecutive proofs are chained by having each segment verify the preceding checkpoint as part of its own public inputs.

This approach carries a significant overhead: _padding_. If a chip performs only $k << N$ operations in a given segment, its $N - k$ remaining rows must be filled with dummy entries that satisfy the constraints but carry no useful computation. In a multi-chip system, this cost compounds across every chip in every segment: different chips have wildly different utilization across segments, yet each padded row still enters the polynomial commitment and constraint evaluation. The result is a large blowup in prover time and proof size, which grows with the number of segments and the number of chips.

A solution at the cryptographic layer is the _jagged polynomial commitment scheme (Jagged PCS)_ @EPRINT:HJRRR25. This protocol commits to the full computation trace as a single polynomial over a jagged matrix ---where each column corresponds to a chip and can have a different height--- and lets the verifier emulate access to the individual per-chip polynomials. The prover pays proving cost proportional to the actual trace area rather than the padded one. The jagged PCS is, however, inherently multilinear: it is built on multilinear polynomial commitments and can be incorporated efficiently only into proving systems whose arithmetization is multilinear-based.

Rather than developing new cryptographic infrastructure and tying the solution to a specific class of proving system, ZisK addresses the problem at the system design level, described next.

== ZisK's Approach: Trace Splitting

ZisK decouples segmentation from execution and lets chips operate on demand. The program runs to completion in the host execution environment in a single pass, producing the full execution trace. Each chip records only the rows for instructions it handles: the Memory chip records only memory accesses, Keccak only hash operations, and so on. Chips that are rarely invoked produce short traces; chips that are heavily used produce long ones.

The prover then partitions each chip's trace independently into consecutive segments of that chip's fixed height $N_i$. Padding is limited to the final segment of each chip, where the last partial slice is padded to $N_i$ rows; all earlier segments are filled to capacity. This stands in contrast to the standard approach, where every chip is padded to its height in every execution segment regardless of how many operations it actually performed. @fig:padding illustrates this layout.

#figure(
  {
    set text(size: 8pt)
    let ca = rgb("#c8d4f0")
    let cm = rgb("#c0e0c0")
    let ck = rgb("#d8d8d8")
    let cp = rgb("#f0dcc0")
    let pad = luma(240)
    let W = 28pt
    let sp = 3pt

    // Segment box: n_rows total rows, n_filled colored, rest gray
    let seg(color, n_filled, seg_h, n_rows) = {
      let rh = seg_h / n_rows
      let rows = range(n_rows).map(i => box(
        fill: if i < n_filled { color } else { pad },
        width: W,
        height: rh,
        stroke: (bottom: 0.2pt + luma(200)),
      ))
      box(stroke: 0.5pt + luma(150), clip: true, stack(dir: ttb, ..rows))
    }

    // Per-chip segment parameters (height, N)
    let Hm = 54pt
    let Nm = 6
    let Hme = 40pt
    let Nme = 5
    let Hk = 24pt
    let Nk = 3
    let Hp = 33pt
    let Np = 4

    let li(c, body) = box(fill: c, width: 10pt, height: 10pt, stroke: 0.3pt) + h(3pt) + body

    let legend = grid(
      columns: (auto, auto, auto, auto, auto),
      align: left + horizon,
      column-gutter: 8pt,
      li(ca)[Main], li(cm)[Memory], li(ck)[ALU], li(cp)[Poseidon], li(pad)[Padding],
    )

    // Small chip label above its segments
    let chip_group(label, segs) = stack(dir: ttb, spacing: 3pt, strong(text(size: 7pt, label)), segs)

    // First horizontal: Main chip
    let main_row = stack(
      dir: ltr,
      spacing: 0pt,
      align(right + horizon, std.pad(right: 6pt, strong(text(size: 7.5pt)[Main chip]))),
      // 3 full (6/6) + 1 partial (2/6)
      stack(
        dir: ltr,
        spacing: sp,
        seg(ca, 6, Hm, Nm),
        seg(ca, 6, Hm, Nm),
        seg(ca, 6, Hm, Nm),
        seg(ca, 6, Hm, Nm),
        seg(ca, 6, Hm, Nm),
        seg(ca, 2, Hm, Nm),
      ),
    )

    // Second horizontal: Memory, Keccak, Poseidon stacked side by side
    let other_chips = stack(
      dir: ltr,
      spacing: 10pt,
      // Memory: 1 full (5/5) + 1 partial (1/5)
      chip_group("Memory", stack(dir: ltr, spacing: sp, seg(cm, 5, Hme, Nme), seg(cm, 5, Hme, Nme), seg(
        cm,
        4,
        Hme,
        Nme,
      ))),
      // Keccak: 1 partial (2/3)
      chip_group("ALU", stack(dir: ltr, spacing: sp, seg(ck, 3, Hk, Nk), seg(ck, 3, Hk, Nk), seg(ck, 1, Hk, Nk))),
      // Poseidon: 1 partial (2/4)
      chip_group("Poseidon", seg(cp, 2, Hp, Np)),
    )

    stack(dir: ttb, spacing: 10pt, main_row, other_chips) //, legend)
  },
  caption: [
    Padding layout for ZisK's trace-splitting approach. Chips define their own segment height $N_i$. Colored rows hold actual computation; gray rows are padding. Only the final segment of each chip requires padding.
  ],
) <fig:padding>

We now make the segmentation precise. Fix an execution $S_0, dots, S_T$ of a program (@sec:execution_model). Every step $t$ contributes a deterministic sequence of rows to some of the AIRs of ZisK (@tbl:chip-inventory): one row to Main, one row to the chip in charge of its opcode if the operation is delegated, as many rows as the operation needs to a precompile, and one row per memory access to the Memory AIR of the accessed region (possibly through MemAlign). For each AIR $cal(C)_i$, the concatenation of these rows over all steps, sorted by address and memory step for the Memory AIRs, is the _global trace_ $bold(T)_i^"glob"$ of $cal(C)_i$.

#definition(title: "Segmentation")[
  Let $N_i$ be the trace height of AIR $cal(C)_i$. The _segmentation_ of an execution splits every global trace into consecutive slices of $N_i$ rows,
  $
    bold(T)_i^"glob" = bold(T)_(i, 0) || bold(T)_(i, 1) || dots || bold(T)_(i, m_i - 1), quad m_i = ceil(abs(bold(T)_i^"glob") \/ N_i),
  $
  where only the last slice is padded to $N_i$ rows ($m_i = 0$ if $bold(T)_i^"glob"$ is empty). A _segment_ is one such slice $bold(T)_(i, j)$, together with its AIR values $bold(a)_(i, j)$; it is a witness for $cal(C)_i$ (@sec:arithmetization), proved on its own. For a chip with a continuation bus (@sec:continuation-bus), its AIR values include the segment index $j$, a flag indicating whether $j = m_i - 1$, and the _boundary payloads_ $B^"in"_(i, j)$ and $B^"out"_(i, j)$ that summarize the state of the chip at the start and at the end of the segment (@sec:continuation-bus).
] <def:segmentation>

For the Main chip, segment $j$ covers exactly the steps $t in [j N, (j + 1) N)$, with $N = N_"Main"$: as recalled in @sec:timestamps, the AIR reconstructs the step of each row from the segment index $j$, so the assignment of steps to Main segments is enforced by the constraints. For every other chip, the partition is by row count and does not align with step boundaries. This is why cross-segment consistency in ZisK is not an equality of whole VM states between consecutive segments, as in the standard approach, but decomposes into per-chip boundary payloads (@sec:continuation-bus).

Trace splitting eliminates most padding ---comparable in effect to the Jagged PCS approach--- but it introduces two problems that must be solved.

The first is _cross-chip consistency_. As commented in @sec:design, there are chips that delegate operations to other specialized chips and record the expected result. Proving that the delegation was correct requires that the involved chips agree on the exchanged values. In the standard continuation's solution this agreement is enforced directly by proving all the chips of a segment together, in a single proof. In the trace-splitting design the proofs for different chips are generated independently. Binding them into a globally consistent argument requires a shared challenge that spans all chip instances ---a check that cannot be performed locally and is instead delegated to the recursive aggregation layer. We explain the solution to this problem in @sec:recursion.

The second is _cross-segment state_. Because each chip's trace is divided independently, a chip whose state evolves over the course of execution cannot restart cold at the beginning of each segment: consecutive segment instances must agree on the machine state at their shared boundary. This is the problem that continuations, in the classical sense, solve.

For chips whose computation is self-contained within each segment ---such as base operations--- the cross-segment state is empty: consecutive segment instances are independent and carry no shared context. For chips with persistent state, however, consecutive instances must agree on the state at their shared boundary. This shared boundary state is enforced by the _continuation bus_.

// @fig:segmentation shows the corresponding per-chip trace breakdown.

// #figure(
//   {
//     set text(size: 8pt)

//     let ca = rgb("#c8d4f0")
//     let cm = rgb("#c0e0c0")
//     let ck = rgb("#d8d8d8")
//     let cp = rgb("#f0dcc0")
//     let cb = rgb("#f8f8a0")
//     let W = 82pt

//     let row(c, body) = box(
//       fill: c,
//       stroke: 0.3pt + luma(150),
//       width: W,
//       inset: (x: 6pt, y: 2.5pt),
//       body,
//     )
//     let bnd(body) = box(
//       fill: cb,
//       stroke: 0.5pt,
//       width: W,
//       inset: (x: 4pt, y: 4pt),
//       align(center, body),
//     )
//     let sbox(body) = box(stroke: 0.7pt, body)
//     let slbl(body) = pad(left: 8pt, body)

//     // Full execution trace (18 rows; 7 memory, 2 Keccak, 2 Poseidon)
//     let full = stack(
//       dir: ttb,
//       spacing: 0pt,
//       row(ca)[+], // seg 1
//       row(ca)[-],
//       row(ca)[Exp],
//       row(cm)[$"Read"(x)$],
//       row(cm)[$"Write"(x)$],
//       row(cm)[$"Read"(z)$],
//       row(cm)[$"Read"(y)$], // seg 2
//       row(ck)[Keccak],
//       row(cm)[$"Write"(y)$],
//       row(cp)[Poseidon],
//       row(ca)[=],
//       row(cp)[Poseidon],
//       row(ck)[Keccak], // seg 3
//       row(cm)[$"Read"(w)$],
//       row(ca)[>>],
//       row(cm)[$"Write"(w)$],
//       row(ca)[=],
//       row(white)[Return],
//     )

//     // Main chip: 3 segments of 6 rows each
//     let s1 = sbox(stack(
//       dir: ttb,
//       spacing: 0pt,
//       row(ca)[+],
//       row(ca)[-],
//       row(ca)[Exp],
//       row(cm)[$"Read"(x)$],
//       row(cm)[$"Write"(x)$],
//       row(cm)[$"Read"(z)$],
//     ))
//     let s2 = sbox(stack(
//       dir: ttb,
//       spacing: 0pt,
//       row(cm)[$"Read"(y)$],
//       row(ck)[Keccak],
//       row(cm)[$"Write"(y)$],
//       row(cp)[Poseidon],
//       row(ca)[=],
//       row(cp)[Poseidon],
//     ))
//     let s3 = sbox(stack(
//       dir: ttb,
//       spacing: 0pt,
//       row(ck)[Keccak],
//       row(cm)[$"Read"(w)$],
//       row(ca)[>>],
//       row(cm)[$"Write"(w)$],
//       row(ca)[=],
//       row(white)[Return],
//     ))

//     let main_seg = grid(
//       columns: (auto, auto),
//       align: (left + top, left + horizon),
//       row-gutter: 3pt,
//       bnd[*Program start state*], [],
//       s1, slbl[Segment 1],
//       bnd[$("pc"_1, c_1)$], [],
//       s2, slbl[Segment 2],
//       bnd[$("pc"_2, c_2)$], [],
//       s3, slbl[Segment 3],
//       bnd[*Final state*], [],
//     )

//     // Per-chip on-demand strips
//     let tiny(c) = box(fill: c, stroke: 0.25pt + luma(160), width: 10pt, height: 9pt)
//     // Memory: 7 rows -> 2 segments
//     let mem_strip = stack(dir: ltr, spacing: 0pt, tiny(cm), tiny(cm), tiny(cm), tiny(cm), tiny(cm), tiny(cm), tiny(cm))
//     // Keccak: 2 rows -> 1 segment
//     let kec_strip = stack(dir: ltr, spacing: 0pt, tiny(ck), tiny(ck))
//     // Poseidon: 2 rows -> 1 segment
//     let pos_strip = stack(dir: ltr, spacing: 0pt, tiny(cp), tiny(cp))

//     let chip_lbl(body) = align(right + horizon, text(size: 7.5pt, body))
//     let seg_lbl(body) = align(left + horizon, pad(left: 5pt, text(size: 7pt, fill: luma(80), body)))

//     let chips = grid(
//       columns: (42pt, auto, auto),
//       align: (right + horizon, left + horizon, left + horizon),
//       row-gutter: 5pt,
//       column-gutter: 5pt,
//       chip_lbl[*Memory*], mem_strip, seg_lbl[2 segments],
//       chip_lbl[*Keccak*], kec_strip, seg_lbl[1 segment],
//       chip_lbl[*Poseidon*], pos_strip, seg_lbl[1 segment],
//     )

//     let li(c, body) = grid(
//       columns: (auto, auto),
//       align: left + horizon,
//       column-gutter: 4pt,
//       box(fill: c, width: 10pt, height: 9pt, stroke: 0.3pt), body,
//     )

//     let legend = stack(dir: ttb, spacing: 3pt, li(ca)[Arithmetic], li(cm)[Memory], li(ck)[Keccak], li(cp)[Poseidon])

//     let right = stack(
//       dir: ttb,
//       spacing: 10pt,
//       text(size: 8pt)[*After segmentation*],
//       stack(dir: ttb, spacing: 4pt, text(size: 7.5pt, fill: luma(80))[_Main chip (3 segments):_], main_seg),
//       stack(dir: ttb, spacing: 5pt, text(size: 7.5pt, fill: luma(80))[_Other chips (activated on demand):_], chips),
//     )

//     grid(
//       columns: (auto, 40pt, auto),
//       align: (center + top, center + horizon, center + top),
//       stack(dir: ttb, spacing: 8pt, strong[Execution trace], full, v(6pt), legend), text(size: 20pt)[→], right,
//     )
//   },
//   caption: [
//     Segmentation of the execution trace.
//   ],
// ) <fig:segmentation>

== The Continuation Bus <sec:continuation-bus>

The _continuation bus_ carries cross-segment state for each chip that requires it. Each segment instance receives, as a message on the bus, the boundary payload $B^"in"$ it starts from, and, unless it ends a chain without terminus, sends the boundary payload $B^"out"$ it ends with. The AIR constraints tie $B^"in"$ to the first row of the segment and $B^"out"$ to its last row. Bus balancing (@sec:interactions) ensures the chain is globally consistent: every sent message is received exactly once with matching content, so gaps, duplications, and reorderings are all ruled out. _Anchors_ ---global terms contributed once per proof rather than by any segment--- open and, where needed, close each chain: the _genesis_ anchor sends the payload the first segment must start from, and the _terminus_ anchor, when the chain has one, receives the payload the last segment must end with. Continuation messages are built from AIR values, so each segment contributes exactly one received and at most one sent message per continuation bus.

The payload is chip-specific, and every chip with state that must survive a segment boundary defines its own continuation bus. Every message carries the segment index, so that the chain can only be assembled in order: the message sent by segment $j$ carries index $j + 1$ and can only be received by the segment with index $j + 1$ (the last Main segment is the exception, see below).

*Main.* The payload is the control state $("pc", c)$ of the guest (@sec:execution_model): the program counter of the next instruction and the output of the last one. Messages have the form $(j, "last", "pc", c_0, c_1)$. Segment $j$ receives $(j, 0, "pc"^"in"_j, c^"in"_j)$, where $"pc"^"in"_j$ is the program counter of its first row and $c^"in"_j$ is the value that its first row reads through the source `C`. It sends $((j + 1)(1 - "last"_j), "last"_j, "pc"^"out"_j, c^"out"_j)$, where $"pc"^"out"_j$ is the next program counter computed by its last row and $c^"out"_j$ is the output of its last row, and where $"last"_j$ is the last-segment flag. The genesis anchor sends $(0, 0, "pc"_"BOOT", 0, 0)$ and the terminus anchor receives $(0, 1, "pc"_"END", 0, 0)$. With $m$ Main segments, balancing therefore enforces the boundary equations
$
  ("pc"^"in"_0, c^"in"_0) = ("pc"_"BOOT", 0), quad ("pc"^"out"_j, c^"out"_j) = ("pc"^"in"_(j+1), c^"in"_(j+1)) "for" j < m - 1, quad ("pc"^"out"_(m-1), c^"out"_(m-1)) = ("pc"_"END", 0).
$
Since segment $j$ covers the steps $[j N, (j + 1) N)$, the middle equation states that the control state at step $(j + 1) N$ is the same whether it is computed by segment $j$ or assumed by segment $j + 1$, and the outer ones are the initial and terminal conditions of @sec:execution_model. Since segments always receive with $"last" = 0$, the final handoff, which carries $"last" = 1$, can only be received by the terminus, so the last segment's output cannot be re-consumed as the input of a further segment; setting its index to $0$ lets the terminus, a global term that does not know $m$, match it.

The rest of the guest state needs no payload of its own. The registers are carried across the boundary by the register argument of @sec:registers, which re-emits every register at the last memory step of each segment but the last. The memory contents are never carried across a boundary: they are determined by the sorted access trace of each memory region, which spans the whole execution.

*Memory AIRs.* The payload is the last row $("addr", t_"mem", v_0, v_1)$ of the segment's slice of the sorted access trace (@sec:memory-chip), so that the order and value checks continue across the boundary. Messages have the form $("base", j, "addr", t_"mem", v_0, v_1)$, where the region's base address separates the chains of the three regions. Segment $j$ receives $("base", j, B^"in"_j)$, which plays the role of the row preceding its first row, and, unless it is the last segment, sends $("base", j + 1, B^"out"_j)$ with $B^"out"_j$ its last row. The genesis anchor sends $("base", 0, "base" \/ 8, 0, 0, 0)$: the first row of the region is compared against a fictitious access just below the base address, at memory step $0$, with value $0$, so that its address is always new. There is no terminus: the last segment simply sends nothing, and its last address is checked against the end of the region instead. The boundary equations are
$
  B^"in"_0 = ("base" \/ 8, 0, 0, 0), quad B^"out"_j = B^"in"_(j+1) "for" j < m - 1.
$
The genesis anchor of the RAM region is unconditional; those of the ROM data and input data regions are switched on by proof-level boolean flags, so that a program that never touches one of these regions needs no segment of its AIR.

*DMA.* The aligned and unaligned DMA workers (@tbl:chip-inventory) may split a single bulk operation across a segment boundary. Their payload is the operation in flight ---source and destination addresses, remaining byte count, main step, and for unaligned copies the bytes read ahead--- together with a flag indicating whether an operation is in flight at all; their genesis anchors send the payload "no operation in flight". The messages follow the same pattern as above, on a continuation bus of their own.

*Other chips.* The remaining chips ---the Rom and the table chips, the base-operation chips, the hash and arithmetic precompiles, the MemAlign chips and the DMA chips other than the workers--- have no cross-segment state and use no continuation bus.

#figure(
  {
    set text(size: 8.5pt)

    let seg(body) = box(stroke: 0.5pt, inset: (x: 8pt, y: 5pt), radius: 1pt, body)
    let anc(body) = text(style: "italic", size: 8.5pt, body)
    let lbl(body) = text(fill: luma(130), size: 6.5pt, body)

    let arr(msg) = pad(
      x: 5pt,
      stack(
        dir: ttb,
        spacing: 3pt,
        align(center, lbl[#msg]),
        align(center, text(size: 9.5pt)[$arrow.r$]),
      ),
    )

    grid(
      columns: (auto, auto, auto, auto, auto, auto, auto, auto, auto),
      align: horizon,
      anc[genesis],
      arr[$("pc"_"BOOT", 0)$],
      seg[Segment $0$],
      arr[$("pc"_N, c_N)$],
      seg[Segment $1$],
      pad(x: 8pt, lbl[$dots.c$]),
      seg[Segment $m - 1$],
      arr[$("pc"_"END", 0)$],
      anc[terminus],
    )
  },
  caption: [
    Continuation bus for the Main chip. The genesis anchor injects the boot
    program counter; the terminus anchor receives the final handoff at the
    designated end program counter.
  ],
) <fig:main-continuation>

== Parallel Proving and Recursive Aggregation

Because each segment instance is proved independently, all segments across all chips can be proved in parallel. Each individual proof establishes only _local consistency_: it certifies that the segment's own constraints are satisfied and records its contribution to the shared bus interactions as a partial sum. Two global checks remain outstanding.

First, the continuation buses must balance globally. Every cross-segment state message sent by a segment instance must be received exactly once by the next, with matching content. No individual segment proof can verify this ---it requires aggregating the partial sums from all instances of a chip across all of its segments.

Second, the cross-chip buses must balance globally. The partial sums recording interactions between the Main chip and the Memory or other specialized chips must cancel to zero when combined. This is the cross-chip consistency problem introduced earlier, and it likewise cannot be enforced locally.

Both checks reduce to a single global field equation: the sum of all partial sums across all instances and all chips, together with the contribution $s_"glob"$ of the global messages (@sec:zisk-statement), must equal zero. The recursive aggregation layer (@sec:recursion) accumulates these partial sums up an aggregation tree and enforces this equation at the root, binding the independent segment proofs into a single, globally valid argument for the full unbounded execution.
