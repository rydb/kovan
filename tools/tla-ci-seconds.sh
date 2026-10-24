#!/usr/bin/env bash
# Write proofs/tla/ci-seconds.txt, the seconds every TLA+ configuration took on a CI runner, from
# the share jobs of one run of the TLA+ workflow (the latest on master when no run id is given).
# proofs/tla/run_tlc.sh deals CI's shares by these seconds.
#   bash tools/tla-ci-seconds.sh [run-id]
set -euo pipefail

repo=$(gh repo view --json nameWithOwner -q .nameWithOwner)
run=${1:-$(gh run list --workflow TLA+ --branch master --status success --limit 1 --json databaseId -q '.[0].databaseId')}
[ -n "$run" ] || { echo "no successful TLA+ run on master to read" >&2; exit 1; }
out=$(git rev-parse --show-toplevel)/proofs/tla/ci-seconds.txt
tmp=$(mktemp)
for job in $(gh run view "$run" --json jobs -q '.jobs[] | select(.name | startswith("TLA+ share")) | .databaseId'); do
  # A share prints one row per configuration: name, states, distinct states, seconds, ...
  gh api "repos/$repo/actions/jobs/$job/logs" --allow-escape-sequences \
    | sed 's/\x1b\[[0-9;]*m//g; s/^[0-9TZ:.-]* //' \
    | awk '$1 ~ /^[A-Z]+_[A-Za-z0-9_]+$/ && $2 ~ /^[0-9]+$/ && $3 ~ /^[0-9]+$/ && $4 ~ /^[0-9]+$/ {print $1, $4}' >> "$tmp"
done
[ -s "$tmp" ] || { echo "run $run has no configuration rows" >&2; exit 1; }
{
  echo "# Seconds each TLA+ configuration took on a CI runner, in TLA+ run $run."
  echo "# Written by tools/tla-ci-seconds.sh, not by hand; run_tlc.sh deals CI's shares by them."
  sort -u "$tmp" | sort -k1,1
} > "$out"
rm -f "$tmp"
echo "wrote $(grep -vc '^#' "$out") configurations to $out"
