"""The Lean toolchains the check supports: each one's linux x86_64 release tarball, pinned by sha256."""
import json
import pkgutil
from typing import NamedTuple, Optional


class Toolchain(NamedTuple):
    version: str
    url: str
    sha256: str


def _table():
    # pkgutil reads the file through the module's loader, so this works from inside a zip too.
    return json.loads(pkgutil.get_data(__name__, 'toolchains.json').decode('utf-8'))


def lookup(version) -> Optional[Toolchain]:
    """The toolchain for a version written as in toolchains.json (`v4.36.0`); None if unsupported."""
    if not isinstance(version, str):
        return None
    entry = _table().get(version)
    if entry is None:
        return None
    return Toolchain(version, entry['url'], entry['sha256'])
