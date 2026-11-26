#!/usr/bin/env bash
set -euo pipefail

source_dir=$(cd "$(dirname "$0")" && pwd)
build_dir=$(mktemp -d)
trap 'rm -f -- "$build_dir"/*.olean; rmdir -- "$build_dir"' EXIT
export LEAN_PATH="$build_dir:${LEAN_PATH:-}"
export source_dir build_dir

verify_lower() {
    local source=$1
    local module=${source##*/}
    module=${module%.lean}
    lean -R "$source_dir/lower" -o "$build_dir/$module.olean" "$source"
    leanchecker -v "$module"
    printf 'Checked %s\n' "$module"
}
export -f verify_lower

printf '%s\0' "$source_dir"/lower/Exact*.lean |
    xargs -0 -n 1 -P "${JOBS:-1}" bash -euo pipefail -c 'verify_lower "$1"' _
lean -R "$source_dir" -o "$build_dir/Upper.olean" "$source_dir/Upper.lean"
leanchecker -v Upper
printf 'Checked all six-gate witnesses\n'
