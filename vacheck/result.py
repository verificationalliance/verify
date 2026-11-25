"""The result.json contract between the checker and the signing job."""
import json
import re
import unicodedata

from .sanity import CHECKS, MAX_NAME, MAX_WARNINGS

SCHEMA = 'https://verificationalliance.org/attestations/proof-check/v2'
# Whether the sanity helper ran to the end ('complete': its verdicts are in the warnings) or the check
# job stopped it, or it crashed ('stopped': every pair was skipped). Two honest checks of one export
# give the same value but for a stop, which this records rather than hides.
SANITY = ('complete', 'stopped')
ALLOWED_AXIOMS = frozenset({'propext', 'Quot.sound', 'Classical.choice'})
# The most the workflow can carry from job check to job sign, as canonical JSON (sorted keys, no
# spaces, UTF-8): job sign reads it from an environment variable, which Linux caps at 128 KiB, in
# base64.
MAX_BYTES = 96000
# Characters a report cannot show as they are: control and format characters (line breaks,
# zero-width and bidi characters among them), line and paragraph separators, and surrogates. A
# line break is allowed only in a statement and a definition's text.
_HIDDEN = frozenset(('Cc', 'Cf', 'Zl', 'Zp', 'Cs'))

# Matched with fullmatch: `$` would also accept a final line break.
_REPO = re.compile(r'github\.com/[A-Za-z0-9-]{1,39}/[A-Za-z0-9._-]{1,100}')
_SHA1 = re.compile(r'[0-9a-f]{40}')
_SHA256 = re.compile(r'[0-9a-f]{64}')


class ResultError(Exception):
    pass


def _fail(msg):
    raise ResultError(msg)


def _keys(obj, keys, what):
    if not isinstance(obj, dict):
        _fail(what + ' must be an object')
    if set(obj) != set(keys):
        _fail(what + ' has the wrong keys')


def hidden_character(text, newlines=False):
    """The first character of text that a report cannot show, or None."""
    for c in text:
        if unicodedata.category(c) in _HIDDEN and not (newlines and c == '\n'):
            return c
    return None


def describe(c):
    """A character as a message names it, without the character itself: U+200B."""
    return 'U+%04X' % ord(c)


def _str(v, what, max_len=None, newlines=False):
    if not isinstance(v, str):
        _fail(what + ' must be a string')
    if max_len is not None and len(v) > max_len:
        _fail(what + ' is too long')
    c = hidden_character(v, newlines)
    if c is not None:
        _fail('%s holds the character %s, which a report cannot show' % (what, describe(c)))
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
    _keys(c, ('says', 'theorem', 'about', 'statement', 'defs', 'axioms', 'source', 'warnings', 'template'), 'claim')
    _str(c['says'], 'says', 200)
    _str(c['theorem'], 'theorem')
    if c['about'] not in ('code', 'model'):
        _fail('about must be code or model')
    _str(c['statement'], 'statement', 4000, newlines=True)
    for d in _list(c['defs'], 'defs', 0, 20):
        _keys(d, ('name', 'text', 'source', 'term'), 'def')
        _str(d['name'], 'def name')
        _str(d['text'], 'def text', 4000, newlines=True)
        _source(d['source'], 'def source')
        if d['term'] is not None:  # the checked term, when the text shows less of it
            _str(d['term'], 'def term', 4000, newlines=True)
    for a in _list(c['axioms'], 'axioms', 0, 3):
        if a not in ALLOWED_AXIOMS:
            _fail('axiom not allowed')
    _source(c['source'], 'source')
    _warnings(c['warnings'])
    if c['template'] is not None:  # claim templates come in a later version
        _fail('template must be null')


def _warnings(ws):
    """A claim's warnings: 0 to MAX_WARNINGS {check, name, arg}, in the order of CHECKS. A definition's
    name (holds-for-any, always-true, ignores-argument) is a string as long as defs allows; a binder's
    (an unused assumption's name, an ignored argument) is a string of at most MAX_NAME characters, or
    null when the report does not show it; no-project-definition names nothing."""
    last = 0
    for w in _list(ws, 'warnings', 0, MAX_WARNINGS):
        _keys(w, ('check', 'name', 'arg'), 'warning')
        check = w['check']
        if not isinstance(check, str) or check not in CHECKS:
            _fail('unknown warning check')
        if CHECKS.index(check) < last:
            _fail('warnings out of order')
        last = CHECKS.index(check)
        if check == 'no-project-definition':
            if w['name'] is not None:
                _fail('no-project-definition names nothing')
        elif check == 'unused-assumption':
            _binder_name(w['name'], 'warning name')
        else:
            _str(w['name'], 'warning name')
        if check == 'ignores-argument':
            _binder_name(w['arg'], 'warning arg')
        elif w['arg'] is not None:
            _fail('only ignores-argument has an arg')


def _binder_name(v, what):
    if v is not None:
        _str(v, what, MAX_NAME)


def _source(src, what):
    """Where the source declares a name: None, or {path, line}."""
    if src is not None:
        _keys(src, ('path', 'line'), what)
        _path(src['path'], what + ' path')
        if _int(src['line'], what + ' line') < 1:
            _fail(what + ' line must be at least 1')


def validate_result(obj):
    _keys(obj, ('schema', 'repo', 'commit', 'toolchain', 'checker', 'project', 'build_digest',
                'claims', 'evidence', 'kernels', 'sanity'), 'result')
    if obj['schema'] != SCHEMA:
        _fail('wrong schema')
    if not isinstance(obj['sanity'], str) or obj['sanity'] not in SANITY:
        _fail('sanity must be complete or stopped')
    if not isinstance(obj['repo'], str) or not _REPO.fullmatch(obj['repo']):
        _fail('bad repo')
    if not isinstance(obj['commit'], str) or not _SHA1.fullmatch(obj['commit']):
        _fail('bad commit')
    if not isinstance(obj['build_digest'], str) or not _SHA256.fullmatch(obj['build_digest']):
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
        size = len(json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode('utf-8'))
    except (UnicodeEncodeError, RecursionError, ValueError):
        _fail('result is not serialisable')
    if size > MAX_BYTES:
        _fail('result is larger than %d bytes, the most the workflow can pass to job sign' % MAX_BYTES)
