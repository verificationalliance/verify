#!/usr/bin/env bash
# Builds vacheck.pyz, the zipapp the workflow runs as `python3 -I vacheck.pyz`, and prints its sha256.
# Usage: scripts/build.sh [output folder, dist by default]
# scripts/release.sh builds a release with it, once it has checked the release commit.
#
# The same source gives the same bytes, so anyone can rebuild a release and compare the sha256:
# every file in the archive has the same time and mode, and the entry point is a file of its own
# (`zipapp -m` would write one stamped with the time of the build).
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
out=${1:-$root/dist}
stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT

mkdir -p "$stage/app/vacheck" "$out"
cp "$root"/vacheck/*.py "$root"/vacheck/*.json "$stage/app/vacheck/"
# What `python3 -m zipapp ... -m vacheck.__main__:main` writes.
printf '# -*- coding: utf-8 -*-\nimport vacheck.__main__\nvacheck.__main__.main()\n' > "$stage/app/__main__.py"
find "$stage/app" -type d -exec chmod 755 {} +
find "$stage/app" -type f -exec chmod 644 {} +
find "$stage/app" -exec touch -d '1980-01-01T00:00:00Z' {} +
TZ=UTC python3 -I -m zipapp "$stage/app" -o "$out/vacheck.pyz"
sha256sum "$out/vacheck.pyz"
