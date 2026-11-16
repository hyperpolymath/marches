#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
# Linux x86-64 Agda toolchain for scripts/check-agda.sh. The release archive
# is accepted only at the checked-in checksum, and a version mismatch fails
# before any proof is checked. Pinned as in hyperpolymath/echo-types
# scripts/setup-agda.sh (5549185), the estate's checksum-pinned Agda 2.7.0.1.
# marches needs no Agda library: no standard library is fetched.
#
# CI: RUNNER_TEMP is set and the toolchain is put on PATH for later steps.
# Locally: AGDA_TOOLS_DIR=<dir> bash scripts/setup-agda.sh, then
# source <dir>/env.sh. AGDA_ARCHIVE_PATH reuses an archive already fetched.
set -euo pipefail

AGDA_VERSION=2.7.0.1
AGDA_SHA256=975b515a14877ab6bce5bfc641e16c4a3ee52ca5d7f846577dee80aa2145db8a

test "$(uname -s)-$(uname -m)" = Linux-x86_64
tool_dir="${AGDA_TOOLS_DIR:-${RUNNER_TEMP:?RUNNER_TEMP or AGDA_TOOLS_DIR is required}/marches-agda}"
mkdir -p "$tool_dir"
tool_dir="$(cd "$tool_dir" && pwd)"
archive="${AGDA_ARCHIVE_PATH:-$tool_dir/Agda-v$AGDA_VERSION-linux.tar.xz}"
if [ ! -f "$archive" ]; then
  curl --fail --location --retry 3 --proto '=https' --tlsv1.2 \
    --output "$archive" \
    "https://github.com/agda/agda/releases/download/v$AGDA_VERSION/Agda-v$AGDA_VERSION-linux.tar.xz"
fi
printf '%s  %s\n' "$AGDA_SHA256" "$archive" | sha256sum --check --strict -
tar -xf "$archive" -C "$tool_dir"
agda_root="$tool_dir/Agda-v$AGDA_VERSION"
export Agda_datadir="$agda_root/data"
actual_version="$("$agda_root/bin/agda" --version)"
if [ "$actual_version" != "Agda version $AGDA_VERSION" ]; then
  printf 'Compiler mismatch: expected Agda version %s, got %s\n' "$AGDA_VERSION" "$actual_version" >&2
  exit 1
fi

{
  printf 'export AGDA=%q\n' "$agda_root/bin/agda"
  printf 'export Agda_datadir=%q\n' "$Agda_datadir"
  printf 'export PATH=%q:"$PATH"\n' "$agda_root/bin"
} > "$tool_dir/env.sh"
if [ -n "${GITHUB_PATH:-}" ]; then
  printf '%s\n' "$agda_root/bin" >> "$GITHUB_PATH"
fi
if [ -n "${GITHUB_ENV:-}" ]; then
  printf 'AGDA=%s\nAgda_datadir=%s\n' "$agda_root/bin/agda" "$Agda_datadir" >> "$GITHUB_ENV"
fi
printf '%s\ncompiler-sha256=%s\n' "$actual_version" "$AGDA_SHA256"
