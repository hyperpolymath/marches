#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Fetch the sibling proof repositories marches cites, each at a pinned
# commit, into _build/dependencies (pattern: choreographic-types,
# residual-evidence-types). The siblings are read, never re-declared. One is
# also imported: tropical-types is a lake `require` in lakefile.toml at the
# SAME commit as TROPICAL_TYPES_COMMIT below (rung 3d), and
# .github/workflows/track-siblings.yml moves both pins together. Re-pin
# deliberately, one commit per pin, and update docs/kcut-correspondence.adoc
# to match.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

CHOREOGRAPHIC_TYPES_COMMIT="${CHOREOGRAPHIC_TYPES_COMMIT:-233b07bc7d2ea2da9fff89e0c57570e84a550ef9}"
RESOURCE_ALGEBRA_COMMIT="${RESOURCE_ALGEBRA_COMMIT:-f0818f2b108e273c47a52dda6b9406381071bcbb}"
TROPICAL_TYPES_COMMIT="${TROPICAL_TYPES_COMMIT:-f2e465c966d14d4986dfc492875cc54653d9751e}"
ECHO_TYPES_COMMIT="${ECHO_TYPES_COMMIT:-b0982c44f36133acd2d0e1d4e03cf031fff7a470}"

# Fetch a sibling repository and check out its pinned commit.
# Arguments: $1 is the repository name under hyperpolymath; $2 is the commit.
# Clone into _build/dependencies/$1 if absent, refresh origin, then check out
# the commit and print the repository name and short HEAD. Git failures cause
# the script to exit via set -e.
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
fetch echo-types "$ECHO_TYPES_COMMIT"
