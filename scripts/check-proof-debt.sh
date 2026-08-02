#!/usr/bin/env bash
set -euo pipefail

pattern='^[[:space:]]*(sorry|admit)[[:space:]]*$|:=[[:space:]]*(by[[:space:]]*)?(sorry|admit)([[:space:]]|$)|^[[:space:]]*axiom[[:space:]]|^[[:space:]]*unsafe[[:space:]]+(def|theorem)|(^|[^[:alnum:]_])native_decide([^[:alnum:]_]|$)'
mapfile -t matches < <(grep -RInE --include='*.lean' "$pattern" Lean4LeanModel Lean4LeanModel.lean || true)

unexpected=()
for match in "${matches[@]}"; do
  case "$match" in
    Lean4LeanModel/Consistency.lean:*':  sorry') ;;
    *) unexpected+=("$match") ;;
  esac
done

if ((${#unexpected[@]})); then
  echo 'Unexpected local proof debt:' >&2
  printf '  %s\n' "${unexpected[@]}" >&2
  exit 1
fi
