#!/usr/bin/env bash

# Build script for the papers.
# Always use this (not `typst compile` directly) to keep the pdfs deterministic.

set -euo pipefail

cd "$(dirname "$0")/.."

SOURCE_DATE_EPOCH=0 typst compile --root src/ src/whitepaper/main.typ src/whitepaper/main.pdf
SOURCE_DATE_EPOCH=0 typst compile --root src/ src/security/main.typ src/security/main.pdf
SOURCE_DATE_EPOCH=0 typst compile --root src/ src/proving-system/main.typ src/proving-system/main.pdf
