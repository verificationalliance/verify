#!/usr/bin/env bash
# Builds a release at the commit to release, HEAD: checks the commit, then builds vacheck.pyz with
# scripts/build.sh, which prints its sha256.
# Usage: scripts/release.sh [output folder, dist by default]
#
# It refuses a release whose lean.yml runs another check action than the release commit's own.
# lean.yml names the action in full, pinned by commit, as a called workflow must, and a commit
# cannot name itself: the pin is an earlier commit. So that commit must be in HEAD's history, and
# its .github/actions/check the same as HEAD's, file for file. The check needs the whole history,
# so tests/test_workflows.py tests it in a repository of its own, and test_cli builds with build.sh.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)

refuse() {
  echo "release.sh: $1" >&2
  exit 1
}
[[ -z $(git -C "$root" status --porcelain -- .github/workflows/lean.yml .github/actions/check) ]] \
  || refuse "lean.yml or .github/actions/check is not as the release commit has it: commit it first."
mapfile -t uses < <(git -C "$root" show HEAD:.github/workflows/lean.yml \
  | grep -E '^[[:space:]]*(- )?uses:.*\.github/actions/' || [[ $? -eq 1 ]])
pinned='^ *(- )?uses: verificationalliance/verify/\.github/actions/check@([0-9a-f]{40}) # [^ ]+$'
(( ${#uses[@]} == 1 )) && [[ ${uses[0]} =~ $pinned ]] \
  || refuse "lean.yml must run the check action once, as verificationalliance/verify/.github/actions/check@<full SHA> # <release>."
pin=${BASH_REMATCH[2]}
git -C "$root" cat-file -e "$pin^{commit}" 2> /dev/null \
  || refuse "lean.yml pins the check action at $pin, which is not a commit here."
git -C "$root" merge-base --is-ancestor "$pin" HEAD \
  || refuse "lean.yml pins the check action at $pin, which is not in the release commit's history."
theirs=$(git -C "$root" rev-parse -q --verify "$pin:.github/actions/check" || true)
mine=$(git -C "$root" rev-parse -q --verify "HEAD:.github/actions/check" || true)
[[ -n $mine && $theirs == "$mine" ]] \
  || refuse "lean.yml pins the check action at $pin, whose .github/actions/check is not the release commit's."
echo "lean.yml runs the check action of $pin, the same as the release commit's." >&2
exec bash "$root/scripts/build.sh" "$@"
