
In this section, we provide a comprehensive reference of the ZisK instruction set. The instruction set is designed to be minimal yet sufficiently expressive to support a wide range of computations, including general-purpose programming and cryptographic operations. Each instruction is defined by its opcode, input sources, output store, and the operation it performs on its inputs to produce an output and a flag. The instruction set is categorised into three main groups: VM instructions, core CPU operations, and precompile calls. For each instruction, we provide a detailed description of its semantics and intended use cases.

// TODO: Comment that the halt instruction, if executed, cannot be proven!!
// TODO: Add operands and encoding details (immediates, offsets, etc.) once the instruction format is fully finalised.
// TODO: Add opcode to each instruction as well

#let ops = (
  // Internal
  (name: "flag", type: "Internal", desc: "Write the flag register to c; used to materialise a comparison result."),
  (name: "copyb", type: "Internal", desc: "Copy b to c (identity operation on the b operand)."),
  (name: "halt", type: "Internal", desc: "Terminate execution with the exit code in b."),
  // Fcall
  (name: "fcall_param", type: "Fcall", desc: "Pass a 64-bit parameter to a pending precompile call."),
  (name: "fcall", type: "Fcall", desc: "Invoke a precompile function; begins a multi-step precompile call sequence."),
  (name: "fcall_get", type: "Fcall", desc: "Retrieve a 64-bit output value from the last completed precompile call."),
  // Pubout
  (name: "pubout", type: "Pubout", desc: "Emit the value of a as the i-th public output (i encoded in the immediate)."),
  // Binary — 64-bit
  (name: "minu", type: "Binary", desc: "Unsigned minimum: c = min(a, b) treating both as unsigned 64-bit integers."),
  (name: "min", type: "Binary", desc: "Signed minimum: c = min(a, b) treating both as signed 64-bit integers."),
  (name: "maxu", type: "Binary", desc: "Unsigned maximum: c = max(a, b) (unsigned 64-bit)."),
  (name: "max", type: "Binary", desc: "Signed maximum: c = max(a, b) (signed 64-bit)."),
  (name: "ltu", type: "Binary", desc: "Unsigned less-than: flag = (a < b) unsigned; c = 0."),
  (name: "lt", type: "Binary", desc: "Signed less-than: flag = (a < b) signed; c = 0."),
  (name: "eq", type: "Binary", desc: "Equality: flag = (a == b); c = 0."),
  (name: "add", type: "Binary", desc: "64-bit addition: c = a + b (mod 2^64)."),
  (name: "sub", type: "Binary", desc: "64-bit subtraction: c = a - b (mod 2^64)."),
  (name: "leu", type: "Binary", desc: "Unsigned less-than-or-equal: flag = (a <= b) unsigned; c = 0."),
  (name: "le", type: "Binary", desc: "Signed less-than-or-equal: flag = (a <= b) signed; c = 0."),
  (name: "and", type: "Binary", desc: "Bitwise AND: c = a & b."),
  (name: "or", type: "Binary", desc: "Bitwise OR: c = a | b."),
  (name: "xor", type: "Binary", desc: "Bitwise XOR: c = a ^ b."),
  // Binary — 32-bit variants (operate on low 32 bits, sign-extend result to 64 bits)
  (name: "minu_w", type: "Binary", desc: "32-bit unsigned minimum (low 32 bits; result sign-extended to 64 bits)."),
  (name: "min_w", type: "Binary", desc: "32-bit signed minimum (sign-extended result)."),
  (name: "maxu_w", type: "Binary", desc: "32-bit unsigned maximum (sign-extended result)."),
  (name: "max_w", type: "Binary", desc: "32-bit signed maximum (sign-extended result)."),
  (name: "ltu_w", type: "Binary", desc: "32-bit unsigned less-than comparison (flag result)."),
  (name: "lt_w", type: "Binary", desc: "32-bit signed less-than comparison (flag result)."),
  (name: "eq_w", type: "Binary", desc: "32-bit equality comparison (flag result)."),
  (name: "add_w", type: "Binary", desc: "32-bit addition (low 32 bits; result sign-extended to 64 bits)."),
  (name: "sub_w", type: "Binary", desc: "32-bit subtraction (sign-extended result)."),
  (name: "leu_w", type: "Binary", desc: "32-bit unsigned less-than-or-equal comparison (flag result)."),
  (name: "le_w", type: "Binary", desc: "32-bit signed less-than-or-equal comparison (flag result)."),
  // BinaryEx — shifts and sign extension
  (name: "sll", type: "BinaryEx", desc: "Logical left shift: c = a << (b mod 64)."),
  (name: "srl", type: "BinaryEx", desc: "Logical right shift: c = a >> (b mod 64) (zero-fill)."),
  (name: "sra", type: "BinaryEx", desc: "Arithmetic right shift: c = a >> (b mod 64) (sign-fill)."),
  (name: "sll_w", type: "BinaryEx", desc: "32-bit logical left shift (sign-extended result)."),
  (name: "srl_w", type: "BinaryEx", desc: "32-bit logical right shift (sign-extended result)."),
  (name: "sra_w", type: "BinaryEx", desc: "32-bit arithmetic right shift (sign-extended result)."),
  (name: "signextend_b", type: "BinaryEx", desc: "Sign-extend the low 8 bits of a to 64 bits."),
  (name: "signextend_h", type: "BinaryEx", desc: "Sign-extend the low 16 bits of a to 64 bits."),
  (name: "signextend_w", type: "BinaryEx", desc: "Sign-extend the low 32 bits of a to 64 bits."),
  // ArithAm32 — 64-bit multiply and divide
  (name: "mulu", type: "ArithAm32", desc: "Unsigned 64x64 multiply: c = (a * b) mod 2^64 (low 64 bits)."),
  (name: "muluh", type: "ArithAm32", desc: "Unsigned high-half multiply: c = (a * b) >> 64."),
  (name: "mulsuh", type: "ArithAm32", desc: "Signed-unsigned high-half multiply: c = (signed(a) * unsigned(b)) >> 64."),
  (name: "mul", type: "ArithAm32", desc: "Signed 64x64 multiply (low 64 bits, same as mulu)."),
  (name: "mulh", type: "ArithAm32", desc: "Signed high-half multiply: c = (signed(a) * signed(b)) >> 64."),
  (name: "mul_w", type: "ArithAm32", desc: "32-bit signed multiply (sign-extended to 64 bits)."),
  (name: "divu", type: "ArithAm32", desc: "Unsigned 64-bit division: c = a / b (b=0 yields 2^64-1)."),
  (name: "remu", type: "ArithAm32", desc: "Unsigned 64-bit remainder: c = a mod b (b=0 yields a)."),
  (name: "div", type: "ArithAm32", desc: "Signed 64-bit division (truncated toward zero)."),
  (name: "rem", type: "ArithAm32", desc: "Signed 64-bit remainder (sign follows dividend)."),
  // ArithA32 — 32-bit divide and remainder
  (name: "divu_w", type: "ArithA32", desc: "Unsigned 32-bit division (sign-extended result)."),
  (name: "remu_w", type: "ArithA32", desc: "Unsigned 32-bit remainder (sign-extended result)."),
  (name: "div_w", type: "ArithA32", desc: "Signed 32-bit division (sign-extended result)."),
  (name: "rem_w", type: "ArithA32", desc: "Signed 32-bit remainder (sign-extended result)."),
  // DMA — bulk memory operations
  (
    name: "dma_memcpy",
    type: "DMA",
    desc: "Copy a block of bytes from one memory region to another (may overlap handling).",
  ),
  (name: "dma_memcmp", type: "DMA", desc: "Compare two memory regions byte-by-byte; c = 0 if equal."),
  (name: "dma_inputcpy", type: "DMA", desc: "Copy bytes from the input stream into a memory region."),
  (name: "dma_xmemcpy", type: "DMA", desc: "Extended memcpy: handles cross-segment or extra-large copies."),
  (name: "dma_xmemcmp", type: "DMA", desc: "Extended memcmp: handles cross-segment or extra-large comparisons."),
  (name: "dma_xmemset", type: "DMA", desc: "Fill a memory region with a repeated byte value."),
  (name: "_dma_64_aligned", type: "DMA", desc: "Internal: main phase of a DMA copy over 64-bit-aligned blocks."),
  (name: "_dma_unaligned", type: "DMA", desc: "Internal: handle a DMA copy where source or destination is unaligned."),
  (
    name: "_dma_pre",
    type: "DMA",
    desc: "Internal: alignment pre-phase (partial leading bytes before the aligned block).",
  ),
  (
    name: "_dma_post",
    type: "DMA",
    desc: "Internal: alignment post-phase (partial trailing bytes after the aligned block).",
  ),
  // ArithEq384 — 384-bit / BLS12-381
  (
    name: "arith384_mod",
    type: "ArithEq384",
    desc: "384-bit modular arithmetic (add, sub, or mul mod a 384-bit prime).",
  ),
  (name: "bls12_381_curve_add", type: "ArithEq384", desc: "Point addition on the BLS12-381 G1 elliptic curve."),
  (name: "bls12_381_curve_dbl", type: "ArithEq384", desc: "Point doubling on the BLS12-381 G1 elliptic curve."),
  (name: "bls12_381_complex_add", type: "ArithEq384", desc: "Addition in the BLS12-381 extension field Fp2."),
  (name: "bls12_381_complex_sub", type: "ArithEq384", desc: "Subtraction in the BLS12-381 extension field Fp2."),
  (name: "bls12_381_complex_mul", type: "ArithEq384", desc: "Multiplication in the BLS12-381 extension field Fp2."),
  // BigInt
  (
    name: "add256",
    type: "BigInt",
    desc: "256-bit integer addition: add two 256-bit values (stored in 4x64-bit limbs).",
  ),
  // Keccak
  (name: "keccak", type: "Keccak", desc: "Compute Keccak-256 (full permutation Keccak-f[1600]) over a memory buffer."),
  // ArithEq — 256-bit / secp256k1, secp256r1, BN254
  (
    name: "arith256",
    type: "ArithEq",
    desc: "256-bit modular arithmetic (generic): compute a*b + c*d mod p for configurable p.",
  ),
  (name: "arith256_mod", type: "ArithEq", desc: "256-bit modular reduction: c = a mod p."),
  (name: "secp256k1_add", type: "ArithEq", desc: "Point addition on the secp256k1 elliptic curve."),
  (name: "secp256k1_dbl", type: "ArithEq", desc: "Point doubling on the secp256k1 elliptic curve."),
  (name: "secp256r1_add", type: "ArithEq", desc: "Point addition on the secp256r1 (NIST P-256) elliptic curve."),
  (name: "secp256r1_dbl", type: "ArithEq", desc: "Point doubling on the secp256r1 elliptic curve."),
  (name: "bn254_curve_add", type: "ArithEq", desc: "Point addition on the BN254 (alt-bn128) elliptic curve."),
  (name: "bn254_curve_dbl", type: "ArithEq", desc: "Point doubling on the BN254 elliptic curve."),
  (name: "bn254_complex_add", type: "ArithEq", desc: "Addition in the BN254 extension field Fp2."),
  (name: "bn254_complex_sub", type: "ArithEq", desc: "Subtraction in the BN254 extension field Fp2."),
  (name: "bn254_complex_mul", type: "ArithEq", desc: "Multiplication in the BN254 extension field Fp2."),
  // Blake2
  (name: "blake2", type: "Blake2", desc: "Compute BLAKE2b (one round of the BLAKE2b compression function)."),
  // Sha256
  (
    name: "sha256",
    type: "Sha256",
    desc: "Compute one SHA-256 compression (sha256f): apply 64-round compression to state and message block.",
  ),
  // Poseidon2
  (
    name: "poseidon2",
    type: "Poseidon2",
    desc: "Compute Poseidon2 hash (ZK-friendly sponge hash over the Goldilocks field).",
  ),
)

// Group ops by type and render one table per group
#let types = ops.map(op => op.type).dedup()

#for type in types {
  let group = ops.filter(op => op.type == type)

  [*#type*]

  table(
    stroke: 0.3pt,
    columns: (1fr, 1fr),
    table.header([*Name*], [*Description*]),

    ..group
      .map(op => (
        [#op.name],
        [#op.desc],
      ))
      .flatten(),
  )

  v(1em)
}

// Group ops by type manually
#let types = ops.map(op => op.type).dedup()

#for type in types {
  let group = ops.filter(op => op.type == type)

  [*#type*]

  table(
    stroke: 0.3pt,
    columns: (1fr, 1fr),
    table.header([*Name*], [*Description*]),

    ..group
      .map(op => (
        [#op.name],
        [#op.desc],
      ))
      .flatten(),
  )

  v(1em)
}
