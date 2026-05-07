// Source: pil/zisk.pil (airgroup Zisk declaration, lines 71–154)

The table below lists every AIR instance declared in the `airgroup Zisk` in `pil/zisk.pil`.
The _N_ column gives the trace height (number of rows per segment);
the _PIL file_ column gives the source file defining the AIR template;
the _Role_ column summarises what the AIR constrains;
the _Buses_ column lists the bus identifiers (from `pil/opids.pil`) that the AIR participates in.

#table(
  stroke: 0.3pt,
  columns: (auto, auto, 2fr, 1fr),
  table.header([*AIR (alias)*], [*N*], [*Role*], [*Buses*]),

  // ── Main / ROM ──────────────────────────────────────────────────────
  [`Main`],
  [$2^(22)$],
  [CPU — fetches instructions, decodes source/store, routes operations via the operation bus, updates PC and registers],
  [`ROM_BUS_ID`, `OPERATION_BUS_ID`, `MEMORY_ID`, `MAIN_CONTINUATION_ID`],

  [`Rom`], [$2^(22)$], [Program ROM lookup table; provides instruction data for the program bus], [`ROM_BUS_ID`],

  // ── Memory ───────────────────────────────────────────────────────────
  [`Mem` (registers + RAM)],
  [$2^(22)$],
  [Read/write memory (base `0xA000_0000`, 512 MB, with dual-mem and large-mem); implements offline memory checking],
  [`MEMORY_ID`, `MEMORY_CONTINUATION_ID`],

  [`RomData`],
  [$2^(21)$],
  [Immutable program data segment (`0x8000_0000`, 128 MB); enabled by `enable_rom_data`],
  [`MEMORY_ID`],

  [`InputData`],
  [$2^(21)$],
  [Free-input memory region (`0x4000_0000`, 1 GB); provides input/hint data; enabled by `enable_input_data`],
  [`MEMORY_ID`],

  [`MemAlign`],
  [$2^(21)$],
  [Decomposes unaligned 64-bit memory accesses into byte-aligned operations],
  [`MEMORY_ALIGN_ROM_ID`, `MEMORY_ID`],

  [`MemAlignByte` (R+W)], [$2^(22)$], [Byte-level memory alignment for both reads and writes], [`DUAL_RANGE_BYTE_ID`],

  [`MemAlignReadByte`], [$2^(22)$], [Byte-level memory alignment for reads only], [`DUAL_RANGE_BYTE_ID`],

  [`MemAlignWriteByte`], [$2^(22)$], [Byte-level memory alignment for writes only], [`DUAL_RANGE_BYTE_ID`],

  // ── Standard arithmetic / logic ──────────────────────────────────────
  [`Arith`],
  [$2^(21)$],
  [64-bit and 32-bit multiplication and division (all `ArithAm32` / `ArithA32` opcodes); uses 16-bit chunk decomposition],
  [`OPERATION_BUS_ID`, `ARITH_TABLE_ID`],

  [`Binary`],
  [$2^(22)$],
  [64/32-bit bitwise and comparison operations (`Binary` opcode group); byte-level carry chain],
  [`OPERATION_BUS_ID`, `BINARY_TABLE_ID`],

  [`BinaryAdd`], [$2^(22)$], [Addition carry-chain helper used by the Binary AIR], [`BINARY_TABLE_ID`],

  [`BinaryExtension`],
  [$2^(22)$],
  [Shift and sign-extension operations (`BinaryEx` opcode group)],
  [`OPERATION_BUS_ID`, `BINARY_EXTENSION_TABLE_ID`],

  // ── Big-integer precompile ────────────────────────────────────────────
  [`Add256` (BigIntAdd)],
  [$2^(20)$],
  [256-bit integer addition (`add256` opcode, `OP_ADD256 = 0xF0`)],
  [`OPERATION_BUS_ID`],

  // ── Elliptic-curve / modular arithmetic (256-bit) ─────────────────────
  [`ArithEq`],
  [$2^(20)$],
  [256-bit modular arithmetic and EC point operations for secp256k1, secp256r1, BN254 (opcodes `0xF2`--`0xF5`, `0xF9`--`0xFE`)],
  [`OPERATION_BUS_ID`, `ARITH_EQ_LT_TABLE_ID`],

  // ── Elliptic-curve / modular arithmetic (384-bit) ─────────────────────
  [`ArithEq384`],
  [$2^(20)$],
  [384-bit modular arithmetic and EC point operations for BLS12-381 (opcodes `0xE2`--`0xE7`)],
  [`OPERATION_BUS_ID`],

  // ── Hash precompiles ─────────────────────────────────────────────────
  [`Keccakf`],
  [$2^(17)$],
  [Keccak-f[1600] permutation (`keccak`, `OP_KECCAKF = 0xF1`); 25 parallel memory operations per call],
  [`OPERATION_BUS_ID`, `KECCAKF_TABLE_ID`, `MEMORY_ID`],

  [`Sha256f`],
  [$2^(18)$],
  [SHA-256 compression function (`sha256`, `OP_SHA256F = 0xF9`)],
  [`OPERATION_BUS_ID`, `MEMORY_ID`],

  [`Poseidon2`],
  [$2^(17)$],
  [Poseidon2 ZK-friendly hash (`poseidon2`, `OP_POSEIDON2 = 0xE1`)],
  [`OPERATION_BUS_ID`, `MEMORY_ID`],

  [`Blake2br`],
  [$2^(18)$],
  [BLAKE2b round function (`blake2`, `OP_BLAKE2BR = 0xEA`)],
  [`OPERATION_BUS_ID`, `BLAKE2BR_PERMUTATION_ID`, `MEMORY_ID`],

  // ── DMA precompiles ───────────────────────────────────────────────────
  [`Dma`],
  [—],
  [DMA dispatch: routes `dma_memcpy` / `dma_memcmp` / `dma_inputcpy` to the appropriate sub-AIR],
  [`DMA_BUS_ID`, `OPERATION_BUS_ID`],

  [`Dma64Aligned` variants],
  [—],
  [Main phase of 64-bit-aligned DMA copies; separate aliases for memcpy, inputcpy, memset],
  [`DMA_BUS_ID`, `MEMORY_ID`],

  [`DmaUnaligned`], [—], [Handles DMA copies where the source is not 64-bit aligned], [`DMA_BUS_ID`, `MEMORY_ID`],

  [`DmaPrePost` variants],
  [—],
  [Pre- and post-alignment phases of a DMA operation (partial leading/trailing bytes)],
  [`DMA_BUS_ID`, `DMA_PRE_POST_TABLE_ID`, `MEMORY_ID`],

  // ── Virtual / lookup tables ───────────────────────────────────────────
  [`DualRange7Bits` (virtual)],
  [$2^(14)$],
  [Range check table for pairs of 7-bit values (0--127)],
  [`DUAL_RANGE_7_BITS_ID`],

  [`DualByte` (virtual)], [$2^(16)$], [Range check table for pairs of 8-bit values (0--255)], [`DUAL_RANGE_BYTE_ID`],

  [`BinaryTable` (virtual)],
  [$2^(20)$],
  [Precomputed truth table for byte-level binary operations],
  [`BINARY_TABLE_ID`],

  [`BinaryExtensionTable` (virtual)],
  [$2^(20)$],
  [Precomputed table for shift and sign-extension byte operations],
  [`BINARY_EXTENSION_TABLE_ID`],

  [`ArithTable` (virtual)], [$2^(20)$], [Precomputed table for 16-bit arithmetic chunk operations], [`ARITH_TABLE_ID`],

  [`ArithRangeTable` (virtual)],
  [$2^(20)$],
  [Range table used by the arithmetic state machine for carry verification],
  [`ARITH_RANGE_TABLE_ID`],

  [`MemAlignRom` (virtual)],
  [—],
  [Precomputed byte-mask table for memory alignment operations],
  [`MEMORY_ALIGN_ROM_ID`],

  [`KeccakfTable` (virtual)], [—], [Precomputed Keccak-f round constants and S-box table], [`KECCAKF_TABLE_ID`],

  [`DmaRom` (virtual)], [—], [ROM table for DMA operation sequencing], [`DMA_ROM_ID`],

  [`DmaPrePostTable` (virtual)],
  [—],
  [Lookup table for DMA pre/post alignment byte patterns],
  [`DMA_PRE_POST_TABLE_ID`],

  [`ArithEqLtTable` (virtual)],
  [—],
  [Less-than comparison table used by the ArithEq state machine],
  [`ARITH_EQ_LT_TABLE_ID`],

  // ── Frequent-operations caches ────────────────────────────────────────
  [`ArithFrops` (FrequentOps)],
  [2 085 944],
  [Cache of the most common arithmetic operation inputs/outputs; resolved from `arith_frops_fixed.bin`],
  [`ARITH_FROPS_TABLE_ID`],

  [`BinaryBasicFrops` (FrequentOps)],
  [13 084 068],
  [Cache of frequent binary-basic operation inputs/outputs; from `binary_basic_frops_fixed.bin`],
  [`BINARY_FROPS_TABLE_ID`],

  [`BinaryExtensionFrops` (FrequentOps)],
  [1 607 204],
  [Cache of frequent shift/sign-extension inputs/outputs; from `binary_extension_frops_fixed.bin`],
  [`BINARY_EXTENSION_FROPS_TABLE_ID`],
)
