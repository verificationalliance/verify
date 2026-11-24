"""Parser for .verificationalliance.json. Plain text only; unknown fields rejected."""
import json
import re
from dataclasses import dataclass
from typing import Literal, Tuple

MAX_BYTES = 32 * 1024
MAX_CLAIMS = 20
MAX_MODULES = 20
MAX_SHIPS = 10
MAX_SAYS = 200

_STRIP = re.compile('[\u0000-\u001f\u007f-\u009f\u200e\u200f\u202a-\u202e\u2066-\u2069]')
_URL = re.compile(r'https?://', re.IGNORECASE)
_IDENT = re.compile(r"[^\W\d][\w'!?]*")
_GUILLEMET = re.compile('«[^»]+»')


class ManifestError(Exception):
    pass


@dataclass(frozen=True)
class Claim:
    says: str
    theorem: str
    about: Literal['code', 'model']


@dataclass(frozen=True)
class Manifest:
    project: str
    modules: Tuple[str, ...]
    ships: Tuple[str, ...]
    claims: Tuple[Claim, ...]


def _text(value, what):
    if not isinstance(value, str):
        raise ManifestError(what + ' must be a string')
    return _STRIP.sub('', value)


def _valid_name(name):
    if not name:
        return False
    rest = name
    while True:
        m = _GUILLEMET.match(rest)
        if m:
            comp_end = m.end()
        else:
            comp = rest.split('.', 1)[0]
            if not _IDENT.fullmatch(comp):
                return False
            comp_end = len(comp)
        rest = rest[comp_end:]
        if not rest:
            return True
        if rest[0] != '.':
            return False
        rest = rest[1:]


def _name(value, what):
    value = _text(value, what)
    if not _valid_name(value):
        raise ManifestError(what + ' is not a valid Lean name')
    return value


def _fields(obj, allowed, what):
    if not isinstance(obj, dict):
        raise ManifestError(what + ' must be an object')
    extra = set(obj) - allowed
    if extra:
        raise ManifestError('unknown field in %s: %s' % (what, sorted(extra)[0]))


def _names(value, what, lo, hi):
    if not isinstance(value, list) or not lo <= len(value) <= hi:
        raise ManifestError('%s must hold %d to %d names' % (what, lo, hi))
    return tuple(_name(v, what) for v in value)


def parse_manifest(raw):
    if not isinstance(raw, bytes):
        raise ManifestError('manifest must be bytes')
    if len(raw) > MAX_BYTES:
        raise ManifestError('manifest is larger than 32 KB')
    try:
        text = raw.decode('utf-8')
    except UnicodeDecodeError:
        raise ManifestError('manifest is not UTF-8')
    try:
        obj = json.loads(text)
    except (ValueError, RecursionError):
        raise ManifestError('manifest is not valid JSON')
    _fields(obj, {'version', 'project', 'modules', 'ships', 'claims'}, 'manifest')
    version = obj.get('version')
    if version != 1 or isinstance(version, bool):
        raise ManifestError('version must be 1')
    project = _text(obj.get('project', '.'), 'project')
    if (not project or project.startswith('/') or '\\' in project
            or '..' in project.split('/')):
        raise ManifestError('project must be a relative path inside the repository')
    modules = _names(obj.get('modules'), 'modules', 1, MAX_MODULES)
    ships = _names(obj.get('ships', []), 'ships', 0, MAX_SHIPS)
    raw_claims = obj.get('claims')
    if not isinstance(raw_claims, list) or not 1 <= len(raw_claims) <= MAX_CLAIMS:
        raise ManifestError('claims must hold 1 to 20 entries')
    claims = []
    seen = set()
    for c in raw_claims:
        _fields(c, {'says', 'theorem', 'about'}, 'claim')
        if set(c) != {'says', 'theorem', 'about'}:
            raise ManifestError('claim needs says, theorem and about')
        says = _text(c['says'], 'says').strip()
        if not says or len(says) > MAX_SAYS:
            raise ManifestError('says must be 1 to 200 characters')
        if _URL.search(says) or '<' in says or '>' in says:
            raise ManifestError('says must be plain text: no URLs and no markup')
        theorem = _name(c['theorem'], 'theorem')
        if theorem in seen:
            raise ManifestError('duplicate theorem')
        seen.add(theorem)
        if c['about'] not in ('code', 'model'):
            raise ManifestError("about must be 'code' or 'model'")
        claims.append(Claim(says, theorem, c['about']))
    return Manifest(project, modules, ships, tuple(claims))
