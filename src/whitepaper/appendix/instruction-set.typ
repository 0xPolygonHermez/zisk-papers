// Looser spacing than the body text: the entries are dense in math with
// sub- and superscripts, which collide under the default leading.
#set par(leading: 0.8em)
#set terms(tight: false, spacing: 0.9em)

This appendix lists every opcode of the ZisK ISA, grouped by the chip that proves it (@tbl:chip-inventory). It transcribes the reference implementation #link("https://github.com/0xPolygonHermez/zisk/blob/v0.16.1/core/src/zisk_ops.rs")[zisk_ops.rs] and is the normative definition of the operation $(c, "flag") = "op"(a, b)$ used by the step semantics of @sec:execution_model.

We write $a_(32) = a mod 2^(32)$ for the low word of $a$; $"sext"_k (x)$ for the sign extension of a $k$-bit value $x$ to 64 bits; $scripts(<)_u, scripts(<=)_u$ and $scripts(<)_s, scripts(<=)_s$ for unsigned and signed (two's complement) comparison; and $[phi] in {0, 1}$ for the indicator of $phi$. Arithmetic on 64-bit words is modulo $2^(64)$ and on 32-bit words modulo $2^(32)$, unless stated otherwise. Each entry reads "mnemonic (code): $c$; flag", with $"flag" = 0$ when omitted. The 32-bit (`_w`) opcodes depend only on the low 32 bits of their operands. Opcodes marked $dagger$ are part of the ISA but are not emitted by the transpiler of @sec:transpilation.

== Internal Opcodes (Main)

/ `flag` (`0x00`): $c = 0$; $"flag" = 1$. Used for unconditional jumps.
/ `copyb` (`0x01`): $c = b$.
/ `halt` (`0xff`): the invalid-instruction sentinel (@sec:transpilation); it cannot appear in a valid execution.

== Binary Opcodes (Binary, BinaryAdd)

64-bit:

/ `minu` (`0x02`), `min` (`0x03`): $c = a$ if $a scripts(<)_u b$ (resp. $a scripts(<)_s b$), and $c = b$ otherwise.
/ `maxu` (`0x04`), `max` (`0x05`): $c = a$ if $b scripts(<)_u a$ (resp. $b scripts(<)_s a$), and $c = b$ otherwise.
/ `ltu` (`0x06`), `lt` (`0x07`): $c = [a scripts(<)_u b]$, resp. $[a scripts(<)_s b]$; $"flag" = c$.
/ `eq` (`0x09`): $c = [a = b]$; $"flag" = c$.
/ `add` (`0x0a`): $c = a + b$. Proved by Binary or by the dedicated BinaryAdd chip.
/ `sub` (`0x0b`): $c = a - b$.
/ `leu`$dagger$ (`0x0c`), `le`$dagger$ (`0x0d`): $c = [a scripts(<=)_u b]$, resp. $[a scripts(<=)_s b]$; $"flag" = c$.
/ `and` (`0x0e`), `or` (`0x0f`), `xor` (`0x10`): bitwise conjunction, disjunction and exclusive disjunction of $a$ and $b$.

32-bit:

/ `minu_w` (`0x12`), `min_w` (`0x13`): $c = "sext"_(32)(a_(32))$ if $a_(32) scripts(<)_u b_(32)$ (resp. $scripts(<)_s$), and $c = "sext"_(32)(b_(32))$ otherwise.
/ `maxu_w` (`0x14`), `max_w` (`0x15`): $c = "sext"_(32)(a_(32))$ if $b_(32) scripts(<)_u a_(32)$ (resp. $scripts(<)_s$), and $c = "sext"_(32)(b_(32))$ otherwise.
/ `ltu_w`$dagger$ (`0x16`), `lt_w`$dagger$ (`0x17`): $c = [a_(32) scripts(<)_u b_(32)]$, resp. $[a_(32) scripts(<)_s b_(32)]$; $"flag" = c$.
/ `eq_w`$dagger$ (`0x19`): $c = [a_(32) = b_(32)]$; $"flag" = c$.
/ `add_w` (`0x1a`), `sub_w` (`0x1b`): $c = "sext"_(32)((a_(32) + b_(32)) mod 2^(32))$, resp. $"sext"_(32)((a_(32) - b_(32)) mod 2^(32))$.
/ `leu_w`$dagger$ (`0x1c`), `le_w`$dagger$ (`0x1d`): $c = [a_(32) scripts(<=)_u b_(32)]$, resp. $[a_(32) scripts(<=)_s b_(32)]$; $"flag" = c$.

== Binary Extension Opcodes (BinaryExtension)

/ `sll` (`0x21`), `srl` (`0x22`), `sra` (`0x23`): $a$ shifted by $b mod 64$ bits: left, logical right, and arithmetic right, respectively.
/ `sll_w` (`0x24`), `srl_w` (`0x25`), `sra_w` (`0x26`): $c = "sext"_(32)$ of $a_(32)$ shifted by $b mod 32$ bits: left, logical right, and arithmetic right, respectively.
/ `signextend_b` (`0x27`), `signextend_h` (`0x28`), `signextend_w` (`0x29`): $c = "sext"_8 (b mod 2^8)$, $"sext"_(16)(b mod 2^(16))$, resp. $"sext"_(32)(b_(32))$; $a$ is ignored.

== Arithmetic Opcodes (Arith)

/ `mul` (`0xb4`), `mulu`$dagger$ (`0xb0`): $c = a dot b mod 2^(64)$ (the result is the same for the signed and unsigned readings).
/ `muluh` (`0xb1`), `mulsuh` (`0xb3`), `mulh` (`0xb5`): $c$ = the high 64 bits of the 128-bit product $a dot b$, reading $a$ and $b$ as unsigned and unsigned, signed and unsigned, and signed and signed, respectively.
/ `mul_w` (`0xb6`): $c = "sext"_(32)(a_(32) dot b_(32) mod 2^(32))$.
/ `divu` (`0xb8`), `remu` (`0xb9`): $c = floor(a \/ b)$, resp. $a mod b$, unsigned. If $b = 0$: $c = 2^(64) - 1$, resp. $c = a$, and $"flag" = 1$.
/ `div` (`0xba`), `rem` (`0xbb`): signed quotient rounded toward zero, resp. remainder with the sign of $a$. If $b = 0$: $c = 2^(64) - 1$, resp. $c = a$, and $"flag" = 1$. The overflow case $-2^(63) \/ -1$ gives $c = -2^(63)$, resp. $c = 0$.
/ `divu_w` (`0xbc`), `remu_w` (`0xbd`): $c = "sext"_(32)$ of the unsigned 32-bit quotient, resp. remainder, of $a_(32)$ and $b_(32)$. If $b_(32) = 0$: $c = 2^(64) - 1$, resp. $c = "sext"_(32)(a_(32))$, and $"flag" = 1$.
// TODO: zisk_ops.rs (op_div_w, v0.16.1) returns 0x0000_0000_8000_0000 for
// (-2^31) / (-1), i.e. not sign-extended, whereas RISC-V DIVW gives
// sext_32(-2^31). Check what the Arith AIR proves and state it here.
/ `div_w` (`0xbe`), `rem_w` (`0xbf`): $c = "sext"_(32)$ of the signed 32-bit quotient rounded toward zero, resp. remainder with the sign of $a_(32)$, of $a_(32)$ and $b_(32)$. If $b_(32) = 0$: $c = 2^(64) - 1$, resp. $c = "sext"_(32)(a_(32))$, and $"flag" = 1$.

== Public Output and Hint Opcodes (Main)

/ `pubout` (`0x30`): $c = b$. Declares the public output with index $a in [0, 32)$ to be $b$ (@sec:public-outputs). Dispatched by Main on the Operation Bus, where it is matched against the public statement (@sec:zisk-statement).
/ `fcall_param` (`0xf6`): $c = b$. Appends to the parameters of the next host call either the value $b$ (if $a = 1$) or the $a$ words stored at address $b$.
/ `fcall` (`0xf7`): $c = b$. Requests the host computation identified by $a$ on the parameters passed so far; its result becomes the hint stream.
/ `fcall_get` (`0xf8`): $c = b$, where $b$ is the value read from the free-input port, i.e. the next word of the hint stream.

The three hint opcodes only affect the host state, and Main proves them as `copyb` (@sec:phantom).

== Precompile Opcodes

For every precompile, $b$ is the address $q$ of an 8-byte-aligned parameter block and $a = 0$; $c = 0$ and $"flag" = 0$ unless stated otherwise. All multi-word values are sequences of 64-bit words in little-endian order (least significant word first) and every pointer in a parameter block is 8-byte aligned. The memory effect of each opcode is described below; $"mem"[x, x + n)$ denotes the $n$ bytes at address $x$, and $q_i := "mem"[q + 8 i]_8$ the $i$-th word of the parameter block.

/ `keccak` (`0xf1`, Keccakf): $"mem"[q, q + 200)$ is replaced by its image under the Keccak-f[1600] permutation.
/ `sha256` (`0xf9`, Sha256f): the 256-bit state at $q_0$ is replaced by its SHA-256 compression with the 512-bit block at $q_1$.
/ `poseidon2` (`0xe1`, Poseidon2): the 16 words at $q$, read as Goldilocks elements, are replaced by their image under the Poseidon2 permutation of width 16.
/ `blake2` (`0xea`, Blake2br): one BLAKE2b round, with round index $q_0$, on the 16-word state at $q_1$ and the 16-word message block at $q_2$; the state is updated in place.
/ `add256` (`0xf0`, Add256): with operands at $q_0$, $q_1$, a carry in $q_2 in {0, 1}$ and result pointer $q_3$, writes $(x + y + q_2) mod 2^(256)$ at $q_3$ and returns the carry out in $c in {0, 1}$.
/ `arith256` (`0xf2`, ArithEq): with 256-bit operands $x, y, z$ at $q_0, q_1, q_2$, writes the low and high 256-bit halves of $x dot y + z$ at $q_3$ and $q_4$.
/ `arith256_mod` (`0xf3`, ArithEq): with 256-bit operands $x, y, z, m$ at $q_0, dots, q_3$, writes $(x dot y + z) mod m$ at $q_4$.
/ `arith384_mod` (`0xe2`, ArithEq384): as `arith256_mod`, with 384-bit operands.
/ `secp256k1_add` (`0xf4`), `secp256r1_add` (`0xe8`), `bn254_curve_add` (`0xfa`) (ArithEq): with affine points $p_1, p_2$ at $q_0, q_1$, replaces $p_1$ by $p_1 + p_2$ on the named curve, computed with the chord formula.
/ `secp256k1_dbl` (`0xf5`), `secp256r1_dbl` (`0xe9`), `bn254_curve_dbl` (`0xfb`) (ArithEq): the affine point $p$ at $q$ itself is replaced by $2 p$, computed with the tangent formula.
/ `bn254_complex_add` (`0xfc`), `bn254_complex_sub` (`0xfd`), `bn254_complex_mul` (`0xfe`) (ArithEq): with elements $f_1, f_2$ of the quadratic extension of the BN254 base field at $q_0, q_1$, replaces $f_1$ by $f_1 + f_2$, $f_1 - f_2$, resp. $f_1 dot f_2$.
/ `bls12_381_curve_add` (`0xe3`), `bls12_381_curve_dbl` (`0xe4`) (ArithEq384): as the 256-bit curve operations, on BLS12-381 with 384-bit coordinates.
/ `bls12_381_complex_add` (`0xe5`), `bls12_381_complex_sub` (`0xe6`), `bls12_381_complex_mul` (`0xe7`) (ArithEq384): as the BN254 extension-field operations, over the BLS12-381 base field.

== DMA Opcodes (DMA chips)

Unlike the other precompiles, the DMA opcodes take $a$ and $b$ as plain values. The byte count $n$ is the word at the fixed system address `0xA000_0F00` for `dma_memcpy` and `dma_memcmp`, and the extended argument of the instruction (its `j1` field) for `dma_xmemcpy` and `dma_xmemcmp`; `dma_xmemset` takes the count in $b$ and the fill byte in the extended argument. $"flag" = 0$ always.

/ `dma_memcpy` (`0xd0`), `dma_xmemcpy` (`0xd6`): $"mem"[a, a + n) <- "mem"[b, b + n)$, with the semantics of a copy through a temporary buffer when the ranges overlap; $c = a$.
/ `dma_memcmp` (`0xd1`), `dma_xmemcmp` (`0xd7`): $c$ = the difference $"mem"(a + k) - "mem"(b + k)$, as a signed 64-bit value, at the first offset $k < n$ where the two ranges differ, and $c = 0$ if they are equal; memory is unchanged.
/ `dma_xmemset` (`0xd9`): $"mem"[a, a + b)$ is filled with the byte given by the extended argument; $c = a$.
/ `dma_inputcpy` (`0xd2`): copies the next $b \/ 8$ words of the hint stream to $"mem"[a, a + b)$, where $b$ is a multiple of $8$; $c = a$.

The opcodes `0xda`, `0xdb`, `0xdc` and `0xdd` are internal to the DMA chips: they label the aligned, unaligned, head and tail phases into which a bulk operation is decomposed, and never appear in a program.
