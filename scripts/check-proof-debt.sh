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

# Keep reliance on upstream unique typing and its sorried inversion dependency auditable.
mapfile -t boundary_leaks < <(
  grep -RInE --include='*.lean' '\.uniq(U)?([[:space:](]|$)|IsDefEqU\.sort_inv|\.weakN_iff([[:space:](]|$)|\.skips(_iff)?([[:space:](]|$)|OnCtx\.weakN_inv|addInduct_WF|forallE_inv_stratified|sort_forallE_inv' \
    Lean4LeanModel --exclude='Upstream.lean' || true
)

if ((${#boundary_leaks[@]})); then
  echo 'Upstream metatheory escaped Lean4LeanModel/Upstream.lean:' >&2
  printf '  %s\n' "${boundary_leaks[@]}" >&2
  exit 1
fi
