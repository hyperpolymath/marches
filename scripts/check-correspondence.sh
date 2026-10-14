#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Mechanical check on docs/kcut-correspondence.adoc. It checks NAMES, not
# meanings:
#   1. every Lean identifier the table cites (`Marches.…`) exists in this
#      build (`#check` under `lake env lean`);
#   2. every sibling identifier it cites (`repo:path` or `repo:path:name`)
#      exists in that repository at the commit pinned in
#      scripts/fetch-siblings.sh;
#   3. every pinned commit appears in the table, so prose and pin agree.
# Negative control: one fabricated Lean name and one fabricated Agda name
# are run through the same checks and must be refused, or the run fails.
# Whether the paired names MEAN the same thing is falsifier F6, and no
# script decides it.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"

doc=docs/kcut-correspondence.adoc
deps=_build/dependencies
scripts/fetch-siblings.sh
lake build >/dev/null

tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

lean_exists() {
  printf 'import Marches\n#check @%s\n' "$1" > "$tmp/Check.lean"
  lake env lean "$tmp/Check.lean" >/dev/null 2>&1
}

# `repo:path` names a file; `repo:path:name` needs a line of that file, at
# the pinned commit, that begins with the name and a space (after any
# indentation and an optional data/record/field keyword). That is where
# Agda declares a name; it is a name check, not a type check.
sibling_exists() {
  local repo="${1%%:*}" rest="${1#*:}" path name
  case "$rest" in
    *:*) path="${rest%%:*}"; name="${rest#*:}" ;;
    *)   path="$rest"; name="" ;;
  esac
  [ -d "$deps/$repo" ] || return 1
  git -C "$deps/$repo" cat-file -e "HEAD:$path" 2>/dev/null || return 1
  [ -z "$name" ] && return 0
  git -C "$deps/$repo" show "HEAD:$path" | awk -v n="$name" '
      { sub(/^[ \t]+/, ""); sub(/^(data|record|field)[ \t]+/, "") }
      index($0, n " ") == 1 { found = 1 }
      END { exit found ? 0 : 1 }'
}

fail=0
nlean=0; nsib=0

while IFS= read -r name; do
  nlean=$((nlean + 1))
  if ! lean_exists "$name"; then echo "MISSING (Lean): $name"; fail=1; fi
done < <(grep -oE '`Marches\.[A-Za-z0-9_.'"'"']+`' "$doc" | tr -d '`' | sort -u)

# shellcheck disable=SC2016  # the backticks are literal AsciiDoc markup
while IFS= read -r ref; do
  nsib=$((nsib + 1))
  if ! sibling_exists "$ref"; then echo "MISSING (sibling): $ref"; fail=1; fi
done < <(grep -oE '`(choreographic-types|resource-algebra|tropical-types):[^`]+`' "$doc" \
           | tr -d '`' | sort -u)

while IFS= read -r pin; do
  if ! grep -qF "$pin" "$doc"; then echo "PIN NOT IN TABLE: $pin"; fail=1; fi
done < <(grep -oE '_COMMIT:-[0-9a-f]{40}' scripts/fetch-siblings.sh | cut -d- -f2)

# Negative control: the checks must refuse names that do not exist.
if lean_exists "Marches.Cut.no_such_lemma_negative_control"; then
  echo "NEGATIVE CONTROL FAILED: a fabricated Lean name was accepted"; fail=1
fi
if sibling_exists "choreographic-types:src/Choreographic/KCut.agda:no-such-lemma-negative-control"; then
  echo "NEGATIVE CONTROL FAILED: a fabricated Agda name was accepted"; fail=1
fi

if [ "$fail" -ne 0 ]; then
  echo "FAIL: docs/kcut-correspondence.adoc cites a name or pin that does not check"
  exit 1
fi
echo "PASS: $nlean Lean names and $nsib sibling names exist at the pins; both negative controls refused"
