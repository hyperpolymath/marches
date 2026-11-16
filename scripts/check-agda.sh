#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
# Agda gate for proofs/agda (hyperpolymath/standards PROOF-POLICY §2.1, §8.4).
# Adapted from hyperpolymath/januskey scripts/check-agda.sh at b5034884.
#
#   1. The graded root proofs/agda/All.agda checks cold under the §2.1
#      canonical invocation, with the pinned compiler.
#   2. Its import cone, as Agda reports it, is scanned for postulates: none in
#      this repository's modules; in the modules shipped with Agda, exactly
#      Agda.Primitive's four level primitives, each bound by its BUILTIN.
#   3. Controls show each part can fail: the scanner finds planted postulates
#      and ignores commented ones; the command line refuses a postulate in a
#      file with no OPTIONS pragma; every fixture under tests/reject-agda is
#      refused, for the reason its `-- expect:` line names.
#   4. The receipt fields of §8.2 are printed: checker, invocation, import cone
#      and the §8.5.1 inputs manifest and digest at HEAD.
#
# Run scripts/setup-agda.sh first (or put the pinned agda on PATH).
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"
prover="${AGDA:-agda}"

pin="$(sed -n 's/^AGDA_VERSION=//p' scripts/setup-agda.sh)"
version="$("$prover" --version)"
[ "$version" = "Agda version $pin" ] || {
  echo "ERROR: expected Agda version $pin (scripts/setup-agda.sh), got '$version'" >&2; exit 1; }

# §2.1 canonical flags. --no-libraries: there is no library dependency, so no
# .agda-lib or libraries file is read. --ignore-interfaces: every run is cold.
canonical=(--safe --without-K --cubical-compatible)
flags=("${canonical[@]}" --no-libraries --ignore-interfaces -i proofs/agda)
root=proofs/agda/All.agda

work="$(mktemp -d)"
trap 'rm -rf -- "$work"' EXIT

"$prover" "${flags[@]}" --dependency-graph="$work/cone.dot" "$root"

# PROOF-POLICY §8.4: the import cone is the module set Agda reports for the
# root, prover-supplied modules included. Each module is resolved to a source
# file; an unresolved one fails.
agda_prim="$("$prover" --print-agda-dir)/lib/prim"
own=(); prover_lib=(); cone=()
while IFS= read -r name; do
  cone+=("$name")
  if   [ -f "proofs/agda/${name//.//}.agda" ]; then own+=("proofs/agda/${name//.//}.agda")
  elif [ -f "$agda_prim/${name//.//}.agda" ]; then prover_lib+=("$agda_prim/${name//.//}.agda")
  else echo "ERROR: cannot resolve module $name of the import cone to a source file" >&2; exit 1
  fi
done < <(sed -n 's/.*label="\([^"]*\)".*/\1/p' "$work/cone.dot" | LC_ALL=C sort -u)
[ "${#own[@]}" -gt 0 ] || { echo "ERROR: Agda reported no first-party module in the import cone" >&2; exit 1; }
echo "import cone: ${#own[@]} first-party modules, ${#prover_lib[@]} supplied with the prover"

# This repository's modules: no postulate at all.
bash scripts/scan-postulates.sh "${own[@]}"

# Modules supplied with the prover are its trusted base. The only postulates
# allowed there are Agda.Primitive's level primitives: exactly Level, lzero,
# lsuc and _⊔_, each bound by its BUILTIN pragma. The names and bindings are
# checked, not the file name, so a prover pin that adds a postulate fails here.
prim="$agda_prim/Agda/Primitive.agda"
status=0; bash scripts/scan-postulates.sh "${prover_lib[@]}" >"$work/prover.log" 2>&1 || status=$?
[ "$status" -le 1 ] || { cat "$work/prover.log"; exit 1; }
grep -E '^[^ ]+:[0-9]+: ' "$work/prover.log" >"$work/prover.hits" || true
if grep -vqE -- "^$prim:[0-9]+: postulate[[:space:]]*\$" "$work/prover.hits"; then
  cat "$work/prover.log"; echo "ERROR: a prover-supplied postulate outside the Agda.Primitive level blocks" >&2; exit 1
fi
declared="$(LC_ALL=C awk '
  { sub(/--.*/, "") }
  /^postulate[ \t]*$/ { inblock = 1; next }
  inblock && /^[ \t]*$/ { next }
  inblock && /^[ \t]/ { split($0, lhs, ":"); n = split(lhs[1], names, /[ \t]+/)
                        for (k = 1; k <= n; k++) if (names[k] != "") print names[k]; next }
  { inblock = 0 }
' "$prim" | LC_ALL=C sort | tr '\n' ' ')"
expected="Level _⊔_ lsuc lzero "
[ "$declared" = "$expected" ] || {
  echo "ERROR: Agda.Primitive postulates '$declared', expected exactly '$expected'" >&2; exit 1; }
for binding in "LEVEL Level" "LEVELZERO lzero" "LEVELSUC lsuc" "LEVELMAX _⊔_"; do
  LC_ALL=C grep -qE -- "^\{-#[[:space:]]+BUILTIN[[:space:]]+${binding% *}[[:space:]]+${binding#* }[[:space:]]+#-\}" "$prim" || {
    echo "ERROR: Agda.Primitive does not bind ${binding#* } with BUILTIN ${binding% *}" >&2; exit 1; }
done
echo "prover-supplied: Agda.Primitive postulates exactly ${expected% }, each bound by its BUILTIN pragma; no other postulate"

# Scanner controls, written at run time so no file in the tree carries a real
# postulate for another scanner to count (as in januskey).
printf '%s\n' 'module CommentsOnly where' '-- postulate in a line comment' \
  '--postulate postulate: no space after the dashes' \
  '{- postulate {- nested postulate -} postulate -}' \
  'x--postulate : Set₁' 'x--postulate = Set' \
  's : String' 's = "a postulate in a string \" still the string"' \
  '{-# FOREIGN GHC postulate = () #-}' "c = 'x'-- postulate after a character literal" \
  > "$work/CommentsOnly.agda"
printf '%s\n' 'module Planted where' '{- c -} postulate X : Set' \
  $'\302\240postulate\302\240Y : Set' 'postulate{- c -}Z : Set' \
  '{-# FOREIGN GHC {- {- #-} postulate W : Set' > "$work/Planted.agda"
status=0; bash scripts/scan-postulates.sh "$work/CommentsOnly.agda" >"$work/neg.log" 2>&1 || status=$?
[ "$status" -eq 0 ] || { cat "$work/neg.log"; echo "ERROR: the comments-only control did not exit 0 (got $status)" >&2; exit 1; }
status=0; bash scripts/scan-postulates.sh "$work/Planted.agda" >"$work/pos.log" 2>&1 || status=$?
missed=""
for line in 2 3 4 5; do grep -qF -- "Planted.agda:$line:" "$work/pos.log" || missed="$missed $line"; done
if [ "$status" -ne 1 ] || [ -n "$missed" ]; then
  cat "$work/pos.log"; echo "ERROR: the planted control did not exit 1 naming lines 2-5 (got $status; missed:${missed:- none})" >&2; exit 1
fi
echo "[PASS] postulate scan: cone clean, both controls behave"

# --safe on the command line: a postulate in a file with no OPTIONS pragma.
printf '%s\n' 'module SafeFlag where' 'postulate X : Set' > "$work/SafeFlag.agda"
if "$prover" "${flags[@]}" -i "$work" "$work/SafeFlag.agda" >"$work/safe.log" 2>&1 \
   || ! grep -qF 'Cannot postulate X with safe flag' "$work/safe.log"; then
  cat "$work/safe.log"; echo "ERROR: the command line did not refuse a postulate under --safe" >&2; exit 1
fi
echo "[PASS] refused as expected: a postulate, by the command-line --safe"

# Fixtures: each must be refused for the reason its `-- expect:` line names.
# One refused for another reason (a broken import, a parse error) has stopped
# testing its claim, so it fails the gate too.
shopt -s nullglob
rejects=(tests/reject-agda/*.agda)
shopt -u nullglob
[ "${#rejects[@]}" -gt 0 ] || { echo "ERROR: no fixtures under tests/reject-agda" >&2; exit 1; }
for file in "${rejects[@]}"; do
  want="$(sed -n 's/^-- expect: //p' "$file" | head -1)"
  [ -n "$want" ] || { echo "ERROR: $file has no '-- expect: <text>' line" >&2; exit 1; }
  log="$work/$(basename -- "$file" .agda).log"
  if "$prover" "${flags[@]}" -i tests/reject-agda "$file" >"$log" 2>&1; then
    cat "$log"; echo "ERROR: $file was accepted but must be refused" >&2; exit 1
  fi
  # Agda wraps its messages at the terminal width: compare with line breaks
  # and runs of spaces folded to one space.
  tr -s ' \n' '  ' <"$log" | grep -qF -- "$want" || { cat "$log"; echo "ERROR: $file was refused, but not with '$want'" >&2; exit 1; }
  echo "[PASS] refused as expected: $file ($want)"
done

# Receipt fields (PROOF-POLICY §8.2, §8.5.1). The input set is the
# first-party modules of the cone; no .agda-lib or libraries file is read.
# The manifest is taken from the git blobs at HEAD, so it describes a commit.
commit="$(git rev-parse HEAD)"
clean=1; manifest=""
while IFS= read -r f; do
  # A file not committed, or changed since, has no blob at HEAD to digest.
  if ! git cat-file -e "HEAD:$f" 2>/dev/null || ! git diff --quiet HEAD -- "$f"; then clean=0; break; fi
  manifest+="$(git cat-file blob "HEAD:$f" | sha256sum | cut -d" " -f1)  $f"$'\n'
done < <(printf '%s\n' "${own[@]}" | LC_ALL=C sort)
echo "--- receipt ---"
echo "checker: $version"
echo "invocation: agda ${flags[*]} $root"
echo "import cone: ${cone[*]}"
echo "commit: $commit"
if [ "$clean" -eq 1 ]; then
  echo "inputs-manifest:"; printf '%s' "$manifest" | sed 's/^/  /'
  echo "inputs-sha256: $(printf '%s' "$manifest" | sha256sum | cut -d" " -f1)"
else
  echo "inputs-sha256: none (the working tree differs from HEAD in the input set)"
fi
echo "axioms: none (no postulate outside the prover's trusted base)"
echo "[check-agda] OK"
