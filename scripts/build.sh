#!/usr/bin/env bash

# Build script for the ZisK whitepaper.
# Always use this (not `typst compile` directly) to keep src/main.pdf deterministic.

set -euo pipefail

cd "$(dirname "$0")/.."

SOURCE_DATE_EPOCH=0 typst compile src/main.typ src/main.pdf
