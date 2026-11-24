"""The result.json contract between the checker and the signing job."""
import json
import re

SCHEMA = 'https://verificationalliance.org/attestations/proof-check/v1'
ALLOWED_AXIOMS = frozenset({'propext', 'Quot.sound', 'Classical.choice'})
MAX_BYTES = 1024 * 1024

_REPO = re.compile(r'^github\.com/[A-Za-z0-9-]{1,39}/[A-Za-z0-9._-]{1,100}$')
_SHA1 = re.compile(r'^[0-9a-f]{40}$')
_SHA256 = re.compile(r'^[0-9a-f]{64}$')


class ResultError(Exception):
    pass


def _fail(msg):
    raise ResultError(msg)


def _keys(obj, keys, what):
    if not isinstance(obj, dict):
        _fail(what + ' must be an object')
    if set(obj) != set(keys):
        _fail(what + ' has the wrong keys')


def _str(v, what, max_len=None):
    if not isinstance(v, str):
        _fail(what + ' must be a string')
    if max_len is not None and len(v) > max_len:
        _fail(what + ' is too long')
    return v


def _int(v, what):
    if not isinstance(v, int) or isinstance(v, bool):
        _fail(what + ' must be an integer')
    return v


def _list(v, what, lo, hi):
    if not isinstance(v, list) or not lo <= len(v) <= hi:
        _fail('%s must hold %d to %d entries' % (what, lo, hi))
    return v


def _path(v, what):
    _str(v, what)
    if not v or v.startswith('/') or '\\' in v or '..' in v.split('/'):
        _fail(what + ' must be a relative path without ..')


def _claim(c):
    _keys(c, ('says', 'theorem', 'about', 'statement', 'defs', 'axioms', 'source'), 'claim')
    _str(c['says'], 'says', 200)
    _str(c['theorem'], 'theorem')
    if c['about'] not in ('code', 'model'):
        _fail('about must be code or model')
    _str(c['statement'], 'statement', 4000)
    for d in _list(c['defs'], 'defs', 0, 20):
        _keys(d, ('name', 'text'), 'def')
        _str(d['name'], 'def name')
        _str(d['text'], 'def text', 4000)
    for a in _list(c['axioms'], 'axioms', 0, 3):
        if a not in ALLOWED_AXIOMS:
            _fail('axiom not allowed')
    src = c['source']
    if src is not None:
        _keys(src, ('path', 'line'), 'source')
        _path(src['path'], 'source path')
        if _int(src['line'], 'source line') < 1:
            _fail('source line must be at least 1')


def validate_result(obj):
    _keys(obj, ('schema', 'repo', 'commit', 'toolchain', 'checker', 'project', 'build_digest',
                'claims', 'evidence', 'kernels'), 'result')
    if obj['schema'] != SCHEMA:
        _fail('wrong schema')
    if not isinstance(obj['repo'], str) or not _REPO.match(obj['repo']):
        _fail('bad repo')
    if not isinstance(obj['commit'], str) or not _SHA1.match(obj['commit']):
        _fail('bad commit')
    if not isinstance(obj['build_digest'], str) or not _SHA256.match(obj['build_digest']):
        _fail('bad build_digest')
    _str(obj['toolchain'], 'toolchain', 64)
    _str(obj['checker'], 'checker', 64)
    _str(obj['project'], 'project', 4096)
    for c in _list(obj['claims'], 'claims', 1, 20):
        _claim(c)
    ev = obj['evidence']
    _keys(ev, ('ships', 'replaced'), 'evidence')
    for s in _list(ev['ships'], 'ships', 0, 10):
        _str(s, 'ship')
    for r in _list(ev['replaced'], 'replaced', 0, 200):
        _keys(r, ('path', 'line', 'text'), 'replaced entry')
        _str(r['path'], 'replaced path')
        _int(r['line'], 'replaced line')
        _str(r['text'], 'replaced text', 160)
    for k in _list(obj['kernels'], 'kernels', 0, 10):
        _str(k, 'kernel')
    try:
        size = len(json.dumps(obj, ensure_ascii=False).encode('utf-8'))
    except (UnicodeEncodeError, RecursionError, ValueError):
        _fail('result is not serialisable')
    if size > MAX_BYTES:
        _fail('result is larger than 1 MB')
