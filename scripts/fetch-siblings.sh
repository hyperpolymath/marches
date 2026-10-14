#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Fetch the sibling proof repositories marches cites, each at a pinned
# commit, into _build/dependencies (pattern: choreographic-types,
# residual-evidence-types). Nothing here is imported into the Lean build:
# the siblings are read, never re-declared. Re-pin deliberately, one
# commit per pin, and update docs/kcut-correspondence.adoc to match.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

CHOREOGRAPHIC_TYPES_COMMIT="${CHOREOGRAPHIC_TYPES_COMMIT:-edb784a7d26c276c2abfa8399b773d346dbb101e}"
RESOURCE_ALGEBRA_COMMIT="${RESOURCE_ALGEBRA_COMMIT:-cf9235c532712a783a404c359a1055f40134794a}"
TROPICAL_TYPES_COMMIT="${TROPICAL_TYPES_COMMIT:-e172f8abefd50fc40def4368fa60a155d130ff47}"

fetch() {
  local name="$1" commit="$2" dir="_build/dependencies/$1"
  if [ ! -d "$dir" ]; then
    git clone --quiet "https://github.com/hyperpolymath/$name.git" "$dir"
  fi
  git -C "$dir" fetch --quiet origin
  git -C "$dir" checkout --quiet "$commit"
  echo "$name at $(git -C "$dir" rev-parse --short HEAD)"
}

mkdir -p _build/dependencies
fetch choreographic-types "$CHOREOGRAPHIC_TYPES_COMMIT"
fetch resource-algebra "$RESOURCE_ALGEBRA_COMMIT"
fetch tropical-types "$TROPICAL_TYPES_COMMIT"
