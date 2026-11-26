#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/../../lean"
lake build PEqualNP.Defs
tmp=$(mktemp -d)
trap 'rm -f "$tmp/Exact20897.olean"; rmdir "$tmp"' EXIT
lake env lean --root="$here" -o "$tmp/Exact20897.olean" "$here/Exact20897.lean"
lake env env LEAN_PATH="$tmp:$(lake env printenv LEAN_PATH)" leanchecker -v Exact20897
