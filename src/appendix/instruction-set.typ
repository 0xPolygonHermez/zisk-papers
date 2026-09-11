This appendix lists every opcode of the ZisK ISA at v0.16.1, grouped by the chip that proves it (@sec:chip-design). It is a transcription of #link("https://github.com/0xPolygonHermez/zisk/blob/v0.16.1/core/src/zisk_ops.rs")[zisk_ops.rs] at that version and is the normative definition of the operation $(c, "flag") = "op"(a, b)$ used by the step predicate of @sec:execution_model.

We write $a_(32) = a mod 2^(32)$ for the low word of $a$, $"sext"_k (x)$ for the sign extension of a $k$-bit value to 64 bits, $<_u, <_s$ (resp. $<=_u, <=_s$) for unsigned and signed comparison, and $[phi] in {0, 1}$ for the indicator of $phi$. All arithmetic on 64-bit words is modulo $2^(64)$ and on 32-bit words modulo $2^(32)$ unless stated otherwise. Each entry reads "mnemonic (code): $c$; flag", with $"flag" = 0$ when omitted. Every `_w` opcode depends only on the low 32 bits of its operands.

== Internal Opcodes (Main)

/ `flag` (`0x00`): $c = 0$; $"flag" = 1$. Used for unconditional jumps.
/ `copyb` (`0x01`): $c = b$.
/ `halt` (`0xff`): the invalid-instruction sentinel; it sets an error and cannot appear in a valid execution trace.

== Binary Opcodes (Binary and BinaryAdd)

_64-bit:_

/ `minu` (`0x02`), `min` (`0x03`): $c = min_u (a, b)$, resp. $min_s (a, b)$.
/ `maxu` (`0x04`), `max` (`0x05`): $c = max_u (a, b)$, resp. $max_s (a, b)$.
/ `ltu` (`0x06`), `lt` (`0x07`): $c = [a <_u b]$, resp. $[a <_s b]$; $"flag" = c$.
/ `eq` (`0x09`): $c = [a = b]$; $"flag" = c$.
/ `add` (`0x0a`): $c = a + b$ (BinaryAdd chip).
/ `sub` (`0x0b`): $c = a - b$.
/ `leu` (`0x0c`), `le` (`0x0d`): $c = [a <=_u b]$, resp. $[a <=_s b]$; $"flag" = c$.
/ `and` (`0x0e`), `or` (`0x0f`), `xor` (`0x10`): bitwise $a and b$, $a or b$, $a xor b$.

_32-bit (results sign-extended from bit 31):_

/ `minu_w` (`0x12`), `min_w` (`0x13`): $c = "sext"_(32)(min_u (a_(32), b_(32)))$, resp. with $min_s$.
/ `maxu_w` (`0x14`), `max_w` (`0x15`): $c = "sext"_(32)(max_u (a_(32), b_(32)))$, resp. with $max_s$.
/ `ltu_w` (`0x16`), `lt_w` (`0x17`): $c = [a_(32) <_u b_(32)]$, resp. $[a_(32) <_s b_(32)]$; $"flag" = c$.
/ `eq_w` (`0x19`): $c = [a_(32) = b_(32)]$; $"flag" = c$.
/ `add_w` (`0x1a`), `sub_w` (`0x1b`): $c = "sext"_(32)((a_(32) plus.minus b_(32)) mod 2^(32))$.
/ `leu_w` (`0x1c`), `le_w` (`0x1d`): $c = [a_(32) <=_u b_(32)]$, resp. $[a_(32) <=_s b_(32)]$; $"flag" = c$.

== Binary Extension Opcodes (BinaryExtension)

/ `sll` (`0x21`), `srl` (`0x22`), `sra` (`0x23`): $c = a << (b mod 64)$, logical $a >> (b mod 64)$, arithmetic $a >> (b mod 64)$.
/ `sll_w` (`0x24`), `srl_w` (`0x25`), `sra_w` (`0x26`): $c = "sext"_(32)$ of the corresponding 32-bit shift of $a_(32)$ by $b mod 32$.
/ `signextend_b` (`0x27`), `signextend_h` (`0x28`), `signextend_w` (`0x29`): $c = "sext"_8 (b)$, $"sext"_(16)(b)$, $"sext"_(32)(b)$; $a$ is ignored.

== Arithmetic Opcodes (Arith)

/ `mulu` (`0xb0`), `mul` (`0xb4`): $c = a dot b mod 2^(64)$ (identical for the unsigned and signed readings).
/ `muluh` (`0xb1`), `mulsuh` (`0xb3`), `mulh` (`0xb5`): $c$ = the high 64 bits of the 128-bit product of $a$ and $b$ read as unsigned$times$unsigned, signed$times$unsigned, signed$times$signed.
/ `mul_w` (`0xb6`): $c = "sext"_(32)(a_(32) dot b_(32) mod 2^(32))$.
/ `divu` (`0xb8`), `remu` (`0xb9`): unsigned $c = floor(a \/ b)$, resp. $a mod b$; if $b = 0$ then $c = 2^(64) - 1$, resp. $c = a$, and $"flag" = 1$.
/ `div` (`0xba`), `rem` (`0xbb`): signed quotient rounded toward zero, resp. remainder with the sign of $a$; if $b = 0$ then $c = 2^(64) - 1$, resp. $c = a$, and $"flag" = 1$; the overflow case $(-2^(63)) \/ (-1)$ yields $-2^(63)$, resp. $0$.
/ `divu_w` (`0xbc`), `remu_w` (`0xbd`): $c = "sext"_(32)$ of the 32-bit unsigned quotient, resp. remainder, of $a_(32)$ and $b_(32)$; if $b_(32) = 0$ then $c = 2^(64) - 1$, resp. $c = "sext"_(32)(a_(32))$, and $"flag" = 1$.
/ `div_w` (`0xbe`), `rem_w` (`0xbf`): $c = "sext"_(32)$ of the 32-bit signed quotient, resp. remainder, with the same zero-divisor and overflow conventions.

== Public Output and Hint Opcodes (Main)

/ `pubout` (`0x30`): $c = b$; declares public output word $a in [0, 32)$ to be $b$ (@sec:statement). Bound globally on the Operation Bus.
/ `fcall_param` (`0xf6`), `fcall` (`0xf7`), `fcall_get` (`0xf8`): $c = b$; host-side hint bookkeeping only (@sec:inputs_and_hints). The hint value itself is obtained by a subsequent load from the free-input port.

== Precompile Opcodes

For every precompile, $a = 0$ (immediate) and $b$ is the address of an 8-byte-aligned parameter block, unless stated otherwise; $c = 0$ and $"flag" = 0$ unless stated otherwise. The memory effect $"Eff"_"op"$ of @sec:execution_model is the update described for each entry; all pointers are read from the parameter block at $"mem"[b + 8 i]_8$.

/ `keccak` (`0xf1`, Keccakf chip): $"mem"[b, b + 200) <- "Keccak-f"[1600]("mem"[b, b + 200))$, the state read and written in place.
/ `sha256` (`0xf9`, Sha256f chip): parameter block $("state_ptr", "input_ptr")$; the 256-bit state at $"state_ptr"$ is replaced by one SHA-256 compression of the 512-bit block at $"input_ptr"$.
/ `poseidon2` (`0xe1`, Poseidon2 chip): $"mem"[b, b + 128)$, read as 16 field elements, is replaced by its Poseidon2 permutation of width 16.
/ `blake2` (`0xea`, Blake2br chip): parameter block $("index", "state_ptr", "input_ptr")$ with $"index"$ a direct value; one BLAKE2b round on the 16-word state at $"state_ptr"$ with the 16-word message block at $"input_ptr"$.
/ `add256` (`0xf0`, Add256 chip): parameter block $(x_"ptr", y_"ptr", "cin", z_"ptr")$ with $"cin"$ direct; $"mem"[z_"ptr", z_"ptr" + 32) <- x + y + "cin" mod 2^(256)$ and $c$ = the carry out $in {0, 1}$.
/ `arith256` (`0xf2`, ArithEq chip): parameter block $(x, y, z, d_l, d_h)$ of pointers to 256-bit values; $d_h dot 2^(256) + d_l <- x dot y + z$.
/ `arith256_mod` (`0xf3`, ArithEq chip): parameter block $(x, y, z, m, d)$; $d <- (x dot y + z) mod m$.
/ `secp256k1_add` (`0xf4`), `secp256r1_add` (`0xe8`), `bn254_curve_add` (`0xfa`) (ArithEq chip): parameter block $(p_1, p_2)$ of pointers to affine points; $p_1 <- p_1 + p_2$ on the named curve.
/ `secp256k1_dbl` (`0xf5`), `secp256r1_dbl` (`0xe9`), `bn254_curve_dbl` (`0xfb`) (ArithEq chip): $b$ points directly to an affine point $p$; $p <- 2 p$.
/ `bn254_complex_add` (`0xfc`), `bn254_complex_sub` (`0xfd`), `bn254_complex_mul` (`0xfe`) (ArithEq chip): parameter block $(f_1, f_2)$ of pointers to $FF_(p^2)$ elements over the BN254 base field; $f_1 <- f_1 circle.small f_2$.
/ `arith384_mod` (`0xe2`, ArithEq384 chip): as `arith256_mod` over 384-bit values.
/ `bls12_381_curve_add` (`0xe3`), `bls12_381_curve_dbl` (`0xe4`) (ArithEq384 chip): as the 256-bit curve operations, on BLS12-381 with 384-bit coordinates.
/ `bls12_381_complex_add` (`0xe5`), `bls12_381_complex_sub` (`0xe6`), `bls12_381_complex_mul` (`0xe7`) (ArithEq384 chip): as the BN254 $FF_(p^2)$ operations, over the BLS12-381 base field.

== DMA Opcodes (Dma chips)

Unlike the other precompiles, the DMA opcodes take $a$ and $b$ as plain scalars. The byte count $n$ comes from the word at the fixed system address `EXTRA_PARAMS` for the plain variants and from the extended argument (the `j1` field) for the `x` variants.

/ `dma_memcpy` (`0xd0`), `dma_xmemcpy` (`0xd6`): $"mem"[a, a + n) <- "mem"[b, b + n)$; $c = a$.
/ `dma_memcmp` (`0xd1`), `dma_xmemcmp` (`0xd7`): $c$ = the three-way comparison of $"mem"[a, a + n)$ and $"mem"[b, b + n)$; memory unchanged.
/ `dma_xmemset` (`0xd9`): $"mem"[a, a + b) <-$ the fill byte given by the extended argument; $c = a$.
/ `dma_inputcpy` (`0xd2`): copies $b$ bytes from the input-data region to $a$; $c = a$.
/ `_dma_64_aligned` (`0xda`), `_dma_unaligned` (`0xdb`), `_dma_pre` (`0xdc`), `_dma_post` (`0xdd`): internal opcodes into which the DMA front-end decomposes a bulk operation; they never appear in a program and exist only as Operation Bus messages between the DMA AIRs.
