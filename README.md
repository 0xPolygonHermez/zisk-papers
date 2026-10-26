# ZisK Papers

This repository contains two [Typst](https://typst.app/) papers describing ZisK.

- **ZisK Whitepaper** ([PDF](src/whitepaper/main.pdf)): a specification of the ZisK zkVM. It covers the instruction set and its execution model, the arithmetization framework, the chips and buses of the circuit, continuations, the recursive aggregation, and the proving backend with its parameters.
- **ZisK's Recursion** ([PDF](src/security/main.pdf)): a security analysis of the recursive aggregation layer. It states the relations attested by every node of the aggregation tree and proves that an accepting final proof yields a bounded collection of locally satisfying, bus-balanced AIR witnesses (correct-witness extractability), listing the assumptions and the obligations left for a complete proof.

## Build

To refresh the committed PDFs, use the build script, which compiles both papers deterministically:
```sh
./scripts/build.sh
```

To watch for changes and recompile automatically while drafting:
```sh
typst watch --root src src/whitepaper/main.typ src/whitepaper/main.pdf
typst watch --root src src/security/main.typ src/security/main.pdf
```
