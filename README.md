# ZisK Papers

This repository contains the [Typst](https://typst.app/) documents describing ZisK.

- **ZisK Whitepaper** ([PDF](src/whitepaper/main.pdf)): the specification of the ZisK zkVM. It covers the instruction set and its execution model, the arithmetization framework, the chips and buses, continuations, the recursive aggregation, and the proving backend with its parameters.
- **Security of ZisK** ([PDF](src/security/main.pdf)): the security analysis of ZisK's proof system, in four parts: the proving system (knowledge soundness of every argument), the recursive aggregation (an accepting final proof yields a bounded collection of locally satisfying, bus-balanced AIR witnesses), the semantics (such a collection encodes a successful execution of the committed program; stated, and partly proved), and their composition into the main theorem, with a ledger of its assumptions and limitations.
- **Secure Challenge Derivation in ZisK** ([PDF](src/lthash/main.pdf)): a short note on the lattice-based multiset hash (LtHash) behind ZisK's distributed challenge derivation.

## Layout

```
src/
├── whitepaper/   main.typ, contents/, appendix/
├── security/     main.typ, contents/ (one directory per part)
├── lthash/       main.typ
└── shared/       used by every document
    ├── style.typ             templates (`paper`, `note`), environments, code blocks, references
    ├── lib.typ               environments (definition, lemma, remark, …) and math notation
    ├── refs.bib              the bibliography of all the documents
    └── references.csl        the citation style (alphabetic labels)
```

## Build

To refresh the committed PDFs, use the build script, which compiles every document deterministically:
```sh
./scripts/build.sh
```

To watch for changes and recompile automatically while drafting:
```sh
typst watch --root src src/whitepaper/main.typ src/whitepaper/main.pdf
typst watch --root src src/security/main.typ src/security/main.pdf
typst watch --root src src/lthash/main.typ src/lthash/main.pdf
```

The documents use the Typst packages `fletcher`, `codly` and `codly-languages`, which Typst downloads on the first build.
