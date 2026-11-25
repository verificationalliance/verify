import copy
import hashlib
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from vacheck.manifest import ManifestError, parse_manifest  # noqa: E402
from vacheck.result import SCHEMA, ResultError, validate_result  # noqa: E402

failures = []
count = 0


def check(name, cond):
    global count
    count += 1
    if cond:
        print('ok    ' + name)
    else:
        print('FAIL  ' + name)
        failures.append(name)


def man(**over):
    d = {'version': 1, 'modules': ['A'],
         'claims': [{'says': 'x', 'theorem': 'A.t', 'about': 'model'}]}
    d.update(over)
    return json.dumps(d).encode()


def man_rejected(raw):
    try:
        parse_manifest(raw)
    except ManifestError:
        return True
    return False


def claim(**over):
    c = {'says': 'x', 'theorem': 'A.t', 'about': 'model'}
    c.update(over)
    return c


m = parse_manifest(b'{"version":1,"modules":["A"],"claims":[{"says":"x","theorem":"A.t","about":"model"}]}')
check('manifest minimal ok', m.project == '.' and m.ships == () and m.modules == ('A',)
      and m.claims[0].about == 'model')

ok = parse_manifest(man(claims=[claim(theorem='Site.«key never leaves»'), claim(theorem="Nat.foo'"),
                                claim(theorem='Ünïcode.ok')]))
check('guillemet and unicode names accepted', len(ok.claims) == 3)

check('unknown field rejected', man_rejected(man(extra=1)))
check('unknown claim field rejected', man_rejected(man(claims=[claim(extra=1)])))
check('21 claims rejected', man_rejected(man(claims=[claim(theorem='A.t%d' % i) for i in range(21)])))
check('20 claims accepted', len(parse_manifest(man(claims=[claim(theorem='A.t%d' % i) for i in range(20)])).claims) == 20)
check('says 201 chars rejected', man_rejected(man(claims=[claim(says='a' * 201)])))
check('says 200 chars accepted', parse_manifest(man(claims=[claim(says='a' * 200)])).claims[0].says == 'a' * 200)
for bad in ('see http://x', 'see https://x', 'a <b> c'):
    check('says %r rejected' % bad, man_rejected(man(claims=[claim(says=bad)])))
check('project ../x rejected', man_rejected(man(project='../x')))
check('project /abs rejected', man_rejected(man(project='/abs')))
check('project backslash rejected', man_rejected(man(project='a\\b')))
check('project nested accepted', parse_manifest(man(project='core/sub')).project == 'core/sub')
check('theorem A..b rejected', man_rejected(man(claims=[claim(theorem='A..b')])))
check('theorem digit start rejected', man_rejected(man(claims=[claim(theorem='A.1b')])))
check('theorem unclosed guillemet rejected', man_rejected(man(claims=[claim(theorem='A.«b')])))
check('duplicate theorem rejected', man_rejected(man(claims=[claim(), claim()])))
big = man(claims=[claim(says='a' * 100)])
check('raw 32 KB + 1 rejected', man_rejected(big + b' ' * (32 * 1024 + 1 - len(big))))
check('raw 32 KB accepted', parse_manifest(big + b' ' * (32 * 1024 - len(big))).project == '.')
check('non-UTF-8 rejected', man_rejected(b'{"version":1,"modules":["A"],"claims":[],"x":"\xff"}'))
check('about both rejected', man_rejected(man(claims=[claim(about='both')])))
check('version 2 rejected', man_rejected(man(version=2)))
check('not json rejected', man_rejected(b'nope'))
check('modules empty rejected', man_rejected(man(modules=[])))
check('ships 11 rejected', man_rejected(man(ships=['S%d' % i for i in range(11)])))
check('ships valid accepted', parse_manifest(man(ships=['OSVACore'])).ships == ('OSVACore',))
check('bad module name rejected', man_rejected(man(modules=['a b'])))
check('bidi and control characters stripped',
      parse_manifest(man(claims=[claim(says='a\u202eb\x07c')])).claims[0].says == 'abc')
check('says empty after strip rejected', man_rejected(man(claims=[claim(says='\x07')])))

res = {
    'schema': SCHEMA, 'repo': 'github.com/acme/proj', 'commit': 'a' * 40, 'toolchain': 'v4.36.0',
    'checker': '1.0.0', 'project': 'core', 'build_digest': 'b' * 64,
    'claims': [{'says': 'x', 'theorem': 'OSVA.affectedIn_sound', 'about': 'code', 'statement': 'st',
                'defs': [{'name': 'OSVA.affectedIn', 'text': 'def', 'source': {'path': 'core/OSVACore/Ranges.lean', 'line': 40},
                          'term': 'def OSVA.affectedIn :=\n  x'}],
                'axioms': ['propext'],
                'source': {'path': 'core/OSVACore/Ranges.lean', 'line': 56}, 'warnings': [], 'template': None}],
    'evidence': {'ships': ['OSVACore'], 'replaced': [{'path': 'p', 'line': 3, 'text': '@[extern "x"]'}]},
    'kernels': ['lean', 'nanoda', 'lean4lean'],
}


def result_rejected(mut):
    r = copy.deepcopy(res)
    mut(r)
    try:
        validate_result(r)
    except ResultError:
        return True
    return False


try:
    validate_result(res)
    good = True
except ResultError:
    good = False
check('result round-trip', good)
r2 = copy.deepcopy(res)
r2['claims'][0]['source'] = None
try:
    validate_result(r2)
    good = True
except ResultError:
    good = False
check('result null source accepted', good)
r2['claims'][0]['defs'][0]['source'] = None
check('result null def source accepted', not result_rejected(lambda r: r.update(r2)))
check('result def without its source rejected', result_rejected(lambda r: r['claims'][0]['defs'][0].pop('source')))
check('result def source .. rejected',
      result_rejected(lambda r: r['claims'][0]['defs'][0]['source'].update(path='a/../b')))
check('result def source line 0 rejected', result_rejected(lambda r: r['claims'][0]['defs'][0]['source'].update(line=0)))
check('result def without its term rejected', result_rejected(lambda r: r['claims'][0]['defs'][0].pop('term')))
check('result def term null accepted', not result_rejected(lambda r: r['claims'][0]['defs'][0].update(term=None)))
check('result def term 4001 rejected, 4000 with line breaks accepted',
      result_rejected(lambda r: r['claims'][0]['defs'][0].update(term='a' * 4001))
      and not result_rejected(lambda r: r['claims'][0]['defs'][0].update(term='a\n' * 2000)))
check('result def term not a string rejected', result_rejected(lambda r: r['claims'][0]['defs'][0].update(term=7)))

check('result extra key rejected', result_rejected(lambda r: r.update(extra=1)))
check('result claim extra key rejected', result_rejected(lambda r: r['claims'][0].update(extra=1)))
check('result evidence extra key rejected', result_rejected(lambda r: r['evidence'].update(extra=1)))
check('result missing key rejected', result_rejected(lambda r: r.pop('kernels')))
check('result sorryAx rejected', result_rejected(lambda r: r['claims'][0].update(axioms=['sorryAx'])))
check('result commit 39 rejected', result_rejected(lambda r: r.update(commit='a' * 39)))
check('result commit uppercase rejected', result_rejected(lambda r: r.update(commit='A' * 40)))
check('result digest 63 rejected', result_rejected(lambda r: r.update(build_digest='b' * 63)))
check('result repo bad rejected', result_rejected(lambda r: r.update(repo='gitlab.com/a/b')))
check('result source .. rejected', result_rejected(lambda r: r['claims'][0]['source'].update(path='a/../b')))
check('result source absolute rejected', result_rejected(lambda r: r['claims'][0]['source'].update(path='/a')))
check('result source line 0 rejected', result_rejected(lambda r: r['claims'][0]['source'].update(line=0)))
check('result statement 4001 rejected', result_rejected(lambda r: r['claims'][0].update(statement='a' * 4001)))
check('result def text 4001 rejected',
      result_rejected(lambda r: r['claims'][0]['defs'][0].update(text='a' * 4001)))
check('result 21 defs rejected',
      result_rejected(lambda r: r['claims'][0].update(defs=[{'name': 'n', 'text': 't', 'source': None, 'term': None}] * 21)))
check('result 0 claims rejected', result_rejected(lambda r: r.update(claims=[])))
check('result 21 claims rejected', result_rejected(lambda r: r.update(claims=[r['claims'][0]] * 21)))
check('result 201 replaced rejected',
      result_rejected(lambda r: r['evidence'].update(replaced=[{'path': 'p', 'line': 1, 'text': 't'}] * 201)))
check('result replaced text 161 rejected',
      result_rejected(lambda r: r['evidence']['replaced'][0].update(text='a' * 161)))
check('result bad schema rejected', result_rejected(lambda r: r.update(schema='x')))
check('result about both rejected', result_rejected(lambda r: r['claims'][0].update(about='both')))
check('result bool line rejected', result_rejected(lambda r: r['claims'][0]['source'].update(line=True)))
check('result over 1 MB rejected', result_rejected(
    lambda r: r.update(claims=[dict(r['claims'][0], defs=[{'name': 'n', 'text': 'a' * 4000, 'source': None, 'term': None}] * 20)] * 20)))
try:
    validate_result([])
    good = False
except ResultError:
    good = True
check('result non-object rejected', good)

check('deeply nested manifest raises ManifestError', man_rejected(b'[' * 20000))
check('lone surrogate in result raises ResultError',
      result_rejected(lambda r: r['claims'][0].update(statement='\ud800')))

# Result v2: each claim's warnings, {check, name, arg}, in the order of the checks, and a template,
# null until claim templates exist. A definition's name is as long as defs allows; a binder's, at most 200.
EVERY = [{'check': 'holds-for-any', 'name': 'OSVA.affectedIn', 'arg': None},
         {'check': 'always-true', 'name': 'OSVA.affectedIn', 'arg': None},
         {'check': 'ignores-argument', 'name': 'OSVA.affectedIn', 'arg': 'v'},
         {'check': 'ignores-argument', 'name': 'OSVA.affectedIn', 'arg': None},
         {'check': 'unused-assumption', 'name': 'h', 'arg': None},
         {'check': 'unused-assumption', 'name': None, 'arg': None}]
NO_DEF = {'check': 'no-project-definition', 'name': None, 'arg': None}
H_W = {'check': 'unused-assumption', 'name': 'h', 'arg': None}


def warned(*ws):
    return lambda r: r['claims'][0].update(warnings=list(ws))


check('result v2: the schema', SCHEMA == 'https://verificationalliance.org/attestations/proof-check/v2')
check('result v2: every kind of warning accepted',
      not result_rejected(warned(*EVERY)) and not result_rejected(warned(NO_DEF)) and not result_rejected(warned()))
check('result v2: a claim without warnings rejected', result_rejected(lambda r: r['claims'][0].pop('warnings')))
check('result v2: a claim without template rejected', result_rejected(lambda r: r['claims'][0].pop('template')))
check('result v2: a template rejected in 2.0.0',
      result_rejected(lambda r: r['claims'][0].update(template={'id': 'x/1', 'fills': {}})))
check('result v2: an unknown check rejected', result_rejected(warned(dict(H_W, check='maybe'))))
check('result v2: 11 warnings rejected, and 10 accepted',
      result_rejected(warned(*[H_W] * 11)) and not result_rejected(warned(*[H_W] * 10)))
check('result v2: holds-for-any without a name rejected', result_rejected(warned(dict(EVERY[0], name=None))))
check('result v2: no-project-definition with a name rejected', result_rejected(warned(dict(NO_DEF, name='D'))))
check('result v2: arg on unused-assumption rejected', result_rejected(warned(dict(H_W, arg='x'))))
check('result v2: arg on holds-for-any rejected', result_rejected(warned(dict(EVERY[0], arg='x'))))
check('result v2: warnings out of order rejected', result_rejected(warned(EVERY[1], EVERY[0])))
check('result v2: a warning name with U+202E rejected',
      result_rejected(warned(dict(H_W, name='a\u202eb'))) and result_rejected(warned(dict(EVERY[2], arg='a\u202eb')))
      and result_rejected(warned(dict(EVERY[0], name='D\u202e'))))
check('result v2: a warning with another key, or not an object, rejected',
      result_rejected(warned(dict(H_W, extra=1)))
      and result_rejected(warned({'check': 'unused-assumption', 'name': 'h'}))
      and result_rejected(warned('unused-assumption'))
      and result_rejected(lambda r: r['claims'][0].update(warnings={})))
check('result v2: a binder name over 200 characters rejected; a definition name of any length accepted',
      result_rejected(warned(dict(H_W, name='a' * 201))) and result_rejected(warned(dict(EVERY[2], arg='a' * 201)))
      and not result_rejected(warned(dict(H_W, name='a' * 200), dict(H_W, name=None)))
      and not result_rejected(warned(dict(EVERY[0], name='D.' + 'a' * 300))))
check('result v2: a name that is not a string rejected',
      result_rejected(warned(dict(H_W, name=7))) and result_rejected(warned(dict(EVERY[0], name=['D']))))

# What a report cannot show is rejected in every text field the result publishes, so the checker
# and the server agree: control and format characters (zero-width, bidi, soft hyphen, BOM, tab),
# line and paragraph separators and surrogates. A line break only in a statement or a def's text.
HIDDEN = ('​', '‮', '\x07', '\t', '\r', ' ', ' ', '﻿', '­', '\ud800', '\x85')
TEXT_FIELDS = {
    'says': lambda r, v: r['claims'][0].update(says='a' + v),
    'theorem': lambda r, v: r['claims'][0].update(theorem='a' + v),
    'statement': lambda r, v: r['claims'][0].update(statement='a' + v),
    'def name': lambda r, v: r['claims'][0]['defs'][0].update(name='a' + v),
    'def text': lambda r, v: r['claims'][0]['defs'][0].update(text='a' + v),
    'def term': lambda r, v: r['claims'][0]['defs'][0].update(term='a' + v),
    'source path': lambda r, v: r['claims'][0]['source'].update(path='a' + v),
    'def source path': lambda r, v: r['claims'][0]['defs'][0]['source'].update(path='a' + v),
    'replaced path': lambda r, v: r['evidence']['replaced'][0].update(path='a' + v),
    'replaced text': lambda r, v: r['evidence']['replaced'][0].update(text='a' + v),
    'ship': lambda r, v: r['evidence'].update(ships=['a' + v]),
    'kernel': lambda r, v: r.update(kernels=['a' + v]),
    'project': lambda r, v: r.update(project='a' + v),
    'toolchain': lambda r, v: r.update(toolchain='a' + v),
    'checker': lambda r, v: r.update(checker='a' + v),
}
check('a hidden character in any published text field rejected',
      [(f, ascii(v)) for f, mut in TEXT_FIELDS.items() for v in HIDDEN
       if not result_rejected(lambda r, mut=mut, v=v: mut(r, v))] == [])
check('a line break rejected outside statements and def texts',
      [f for f, mut in TEXT_FIELDS.items()
       if f not in ('statement', 'def text', 'def term') and not result_rejected(lambda r, mut=mut: mut(r, '\nb'))] == [])
check('a line break accepted in a statement and a def text',
      not result_rejected(lambda r: TEXT_FIELDS['statement'](r, '\nb'))
      and not result_rejected(lambda r: TEXT_FIELDS['def text'](r, '\nb')))


def result_message(mut):
    r = copy.deepcopy(res)
    mut(r)
    try:
        validate_result(r)
    except ResultError as e:
        return str(e)
    return None


check('a final line break after repo, commit or build_digest rejected',
      [k for k, v in (('repo', 'github.com/acme/proj'), ('commit', 'a' * 40), ('build_digest', 'b' * 64))
       if not result_rejected(lambda r, k=k, v=v: r.update({k: v + '\n'}))] == [])
check('a hidden character is named by its code point, never written',
      result_message(lambda r: TEXT_FIELDS['says'](r, '​'))
      == 'says holds the character U+200B, which a report cannot show')


def canonical_size(r):
    return len(json.dumps(r, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode('utf-8'))


def of_size(n):
    """res grown with def texts until its canonical JSON is exactly n bytes."""
    r = copy.deepcopy(res)
    while canonical_size(r) < n:
        if len(r['claims'][-1]['defs']) == 20:
            r['claims'].append(dict(copy.deepcopy(res['claims'][0]), defs=[]))
            continue
        r['claims'][-1]['defs'].append({'name': 'n', 'text': '', 'source': None, 'term': None})
        d = r['claims'][-1]['defs'][-1]
        d['text'] = 'a' * max(0, min(4000, n - canonical_size(r)))
    return r


import re  # noqa: E402
from vacheck import result as vr  # noqa: E402
at_cap, over_cap = of_size(vr.MAX_BYTES), of_size(vr.MAX_BYTES + 1)
check('result of exactly MAX_BYTES canonical bytes accepted, one more rejected',
      canonical_size(at_cap) == vr.MAX_BYTES and canonical_size(over_cap) == vr.MAX_BYTES + 1
      and not result_rejected(lambda r: r.update(at_cap)) and result_rejected(lambda r: r.update(over_cap)))
check('the size message says why the result is too large',
      'the most the workflow can pass to job sign' in (result_message(lambda r: r.update(over_cap)) or ''))
# Job sign reads the result, base64, from an environment variable: Linux caps one (NAME=value) at
# 131,072 bytes with its NUL, and lean.yml checks the base64 against MAX_RESULT_B64.
B64_CAP = 4 * -(-vr.MAX_BYTES // 3)
with open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                       '.github', 'workflows', 'lean.yml'), encoding='utf-8') as f:
    lean_yml = f.read()
check("result's cap is lean.yml's, and fits in an environment variable",
      vr.MAX_BYTES == 96000 and B64_CAP == 128000 and len('RESULT=') + B64_CAP + 1 <= 131072
      and re.search(r'^  MAX_RESULT_B64: "%d"' % B64_CAP, lean_yml, re.MULTILINE) is not None)
import typing  # noqa: E402
from vacheck.manifest import Claim, Manifest  # noqa: E402
_mh = typing.get_type_hints(Manifest)
_ch = typing.get_type_hints(Claim)
check('Manifest and Claim field types match the interface',
      _mh['modules'] == typing.Tuple[str, ...] and _mh['ships'] == typing.Tuple[str, ...]
      and _mh['claims'] == typing.Tuple[Claim, ...] and _ch['about'] == typing.Literal['code', 'model'])

# Lean exports. tests/make_fixtures.sh writes the fixtures from the Lake projects in tests/fixtures.
import re  # noqa: E402
import shutil  # noqa: E402
import tempfile  # noqa: E402
import time  # noqa: E402

try:
    from vacheck import export as vx  # noqa: E402
except ImportError as e:
    print('      cannot import vacheck.export: %s' % e)
    vx = None

FIXTURES = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fixtures')
STANDARD = frozenset({'propext', 'Quot.sound', 'Classical.choice'})
META = ('{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},'
        '"lean":{"githash":"611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9","version":"4.36.0"}}}')
TMP = tempfile.mkdtemp()


def attempt(fn):
    """Runs fn. An exception is a failed check, not a crash that hides the checks after it."""
    try:
        return fn()
    except Exception as e:
        print('      %s: %s' % (type(e).__name__, e))
        return None


def is_sha256(d):
    return isinstance(d, str) and re.fullmatch('[0-9a-f]{64}', d) is not None


def export_file(lines):
    path = os.path.join(TMP, 'export.ndjson')
    with open(path, 'wb') as f:
        for line in lines:
            f.write((line if isinstance(line, bytes) else line.encode()) + b'\n')
    return path


def export_rejected(lines, then=lambda env: None):
    """True if loading the lines, then running `then` on the result, raises ExportError and nothing else."""
    try:
        then(vx.load_export(export_file(lines)))
    except Exception as e:
        if vx is not None and isinstance(e, vx.ExportError):
            return True
        print('      %s: %s' % (type(e).__name__, e))
    return False


def raw_records(case):
    """The fixture's declarations as raw records, read with json alone: name -> (kind, record)."""
    names = {0: None}
    out = {}
    with open(os.path.join(FIXTURES, case + '.ndjson'), encoding='utf-8') as f:
        for line in f:
            o = json.loads(line)
            if 'in' in o:
                part = o['str'] if 'str' in o else o['num']
                comp = part['str'] if 'str' in o else str(part['i'])
                pre = names[part['pre']]
                names[o['in']] = comp if pre is None else pre + '.' + comp
            for k in ('axiom', 'def', 'thm', 'opaque', 'quot'):
                if k in o:
                    out[names[o[k]['name']]] = (k, o[k])
            if 'inductive' in o:
                for k in ('types', 'ctors', 'recs'):
                    for r in o['inductive'][k]:
                        out[names[r['name']]] = (k, r)
    return out


envs = {case: attempt(lambda case=case: vx.load_export(os.path.join(FIXTURES, case + '.ndjson')))
        for case in ('good', 'sorry', 'axiom', 'native', 'fakeeq', 'replaced')}
good = envs['good']

ax = attempt(lambda: vx.axioms_of(good, 'Good.t1'))
check('good axioms standard', ax is not None and ax <= STANDARD)
check('good axioms reached through the library', ax == STANDARD)
check('good guillemet theorem uses no axioms',
      attempt(lambda: vx.axioms_of(good, 'Good.«key never leaves»')) == set())
check('sorry found', 'sorryAx' in (attempt(lambda: vx.axioms_of(envs['sorry'], 'Sorry.t')) or ()))
check('axiom found', 'Axiom.magic' in (attempt(lambda: vx.axioms_of(envs['axiom'], 'Axiom.t')) or ()))
# Lean v4.35.0 and later have no Lean.ofReduceBool: native_decide declares an axiom of its own instead.
check('native found', attempt(lambda: vx.axioms_of(envs['native'], 'Native.t'))
      == {'Native.t._native.native_decide.ax_1_1'})

d_fake = attempt(lambda: vx.digest(envs['fakeeq'], 'Eq'))
d_real = attempt(lambda: vx.digest(good, 'Eq'))
check('fakeeq differs', is_sha256(d_fake) and is_sha256(d_real) and d_fake != d_real)
raw_good = raw_records('good')['Nat.add'][1]
raw_replaced = raw_records('replaced')['Nat.add'][1]
check('Nat.add has different ids in good and replaced',
      all(raw_good[k] != raw_replaced[k] for k in ('name', 'type', 'value')))
d_add = attempt(lambda: vx.digest(good, 'Nat.add'))
check('digest stable', is_sha256(d_add) and d_add == attempt(lambda: vx.digest(envs['replaced'], 'Nat.add')))


def digest_disagreements():
    """Declarations two fixtures share, but with different digests. The exporter shares one id
    between alpha-equivalent expressions, so binder names depend on what it exported first."""
    out = []
    cases = ('good', 'replaced', 'sorry', 'axiom', 'native')
    for i, a in enumerate(cases):
        for b in cases[i + 1:]:
            for n in sorted(envs[a].names() & envs[b].names()):
                if vx.digest(envs[a], n) != vx.digest(envs[b], n):
                    out.append((a, b, n))
    return out


check('digest stable for every declaration two fixtures share', attempt(digest_disagreements) == [])
d_others = [attempt(lambda: vx.digest(good, n)) for n in ('Nat.lt', 'Eq.refl')]
check('digest tells declarations apart', all(map(is_sha256, [d_add, d_real] + d_others))
      and len({d_add, d_real, *d_others}) == 4)

check('kind of theorem', attempt(lambda: good.kind('Good.t1')) == 'theorem'
      and attempt(lambda: good.kind('Good.f')) == 'def')
check('guillemet name found', attempt(lambda: good.kind('Good.«key never leaves»')) == 'theorem')
check('kinds of library declarations', attempt(lambda: [good.kind(n) for n in ('Eq', 'Eq.refl', 'Eq.rec', 'Quot')])
      == ['inductive', 'ctor', 'rec', 'quot'])
check('kind of axiom', attempt(lambda: envs['axiom'].kind('Axiom.magic')) == 'axiom')
check('kind of missing name is None', attempt(lambda: [good.kind(n) for n in ('Good.nope', 'Good', '', 'Good..f')])
      == [None, None, None, None])
check('kind of escaped plain name', attempt(lambda: good.kind('Good.«f»')) == 'def')
names = attempt(lambda: good.names())
check('names lists every declaration', isinstance(names, frozenset) and names == frozenset(raw_records('good'))
      .union({'Good.«key never leaves»'}).difference({'Good.key never leaves'}))
check('constants in type', attempt(lambda: vx.constants_in_type(good, 'Good.t1')) == {
    'Eq', 'Good.f', 'HAdd.hAdd', 'Nat', 'Ne', 'OfNat.ofNat', 'Or', 'instAddNat', 'instHAdd', 'instOfNatNat'})

# Synthetic exports: deep, reaching axioms only indirectly, and hostile.
DEPTH = 100000


def deep_export():
    """One axiom `ax`, an opaque and a theorem whose name, type and value are each DEPTH deep."""
    lines = [META, '{"in":1,"str":{"pre":0,"str":"ax"}}']
    lines += ['{"in":%d,"str":{"pre":%d,"str":"D"}}' % (i, i - 1 if i > 2 else 0) for i in range(2, DEPTH + 2)]
    lines += ['{"il":%d,"succ":%d}' % (i, i - 1) for i in range(1, DEPTH + 1)]
    lines += ['{"ie":0,"sort":%d}' % DEPTH, '{"ie":1,"const":{"name":1,"us":[]}}']
    lines += ['{"ie":%d,"app":{"fn":%d,"arg":%d}}' % (i, i - 1, i - 1) for i in range(2, DEPTH + 2)]
    lines += ['{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}',
              '{"in":%d,"str":{"pre":0,"str":"op"}}' % (DEPTH + 2),
              '{"opaque":{"name":%d,"levelParams":[],"type":0,"value":0,"isUnsafe":false,"all":[%d]}}'
              % (DEPTH + 2, DEPTH + 2),
              '{"thm":{"name":%d,"levelParams":[],"type":%d,"value":%d,"all":[%d]}}'
              % (DEPTH + 1, DEPTH + 1, DEPTH + 1, DEPTH + 1)]
    return lines


deep = attempt(lambda: vx.load_export(export_file(deep_export())))
deep_name = '.'.join(['D'] * DEPTH)
check('deep export read iteratively',
      attempt(lambda: (vx.axioms_of(deep, deep_name), vx.constants_in_type(deep, deep_name),
                       is_sha256(vx.digest(deep, deep_name)), deep.kind(deep_name), deep.kind('op'),
                       deep_name in deep.names()))
      == ({'ax'}, {'ax'}, True, 'theorem', 'opaque', True))


def reach_export():
    """Axioms reached only through a constructor (ax), a recursor rule (rx) and a literal (Nat)."""
    names = ['ax', 'rx', 'Nat', 'I', 'mk', 'rec', 'tI', 'tR', 'tN']
    pre = {'mk': 4, 'rec': 4}
    lines = [META] + ['{"in":%d,"str":{"pre":%d,"str":"%s"}}' % (i + 1, pre.get(n, 0), n) for i, n in enumerate(names)]
    lines += ['{"il":1,"succ":0}', '{"ie":0,"sort":0}', '{"ie":1,"sort":1}', '{"ie":2,"const":{"name":1,"us":[]}}',
              '{"ie":3,"const":{"name":4,"us":[]}}',
              '{"forallE":{"binderInfo":"default","body":3,"name":0,"type":2},"ie":4}',
              '{"ie":5,"const":{"name":2,"us":[]}}', '{"ie":6,"const":{"name":6,"us":[]}}', '{"ie":7,"natVal":"5"}']
    lines += ['{"axiom":{"name":%d,"levelParams":[],"type":%d,"isUnsafe":false}}' % nt
              for nt in ((1, 0), (2, 0), (3, 1))]
    lines.append(json.dumps({'inductive': {
        'types': [{'name': 4, 'levelParams': [], 'type': 0, 'numParams': 0, 'numIndices': 0, 'all': [4], 'ctors': [5],
                   'numNested': 0, 'isRec': False, 'isReflexive': False, 'isUnsafe': False}],
        'ctors': [{'name': 5, 'levelParams': [], 'type': 4, 'induct': 4, 'cidx': 0, 'numParams': 0, 'numFields': 1,
                   'isUnsafe': False}],
        'recs': [{'name': 6, 'levelParams': [], 'type': 0, 'all': [4], 'numParams': 0, 'numIndices': 0,
                  'numMotives': 1, 'numMinors': 1, 'rules': [{'ctor': 5, 'nfields': 1, 'rhs': 5}], 'k': False,
                  'isUnsafe': False}]}}))
    lines += ['{"thm":{"name":%d,"levelParams":[],"type":%d,"value":%d,"all":[%d]}}' % (n, t, v, n)
              for n, t, v in ((7, 3, 3), (8, 0, 6), (9, 0, 7))]
    return lines


reach = attempt(lambda: vx.load_export(export_file(reach_export())))
check('axioms reached through constructors, recursor rules and literals',
      attempt(lambda: [vx.axioms_of(reach, t) for t in ('tI', 'tR', 'tN')]) == [{'ax'}, {'rx'}, {'Nat'}])


def binder_digest(binder, info, level):
    """Digest of `t : ∀ (binder : Sort level), Prop`, with the binder annotated as `info`."""
    return attempt(lambda: vx.digest(vx.load_export(export_file(
        [META, '{"in":1,"str":{"pre":0,"str":"t"}}', '{"in":2,"str":{"pre":0,"str":"%s"}}' % binder,
         '{"il":1,"succ":0}', '{"ie":0,"sort":%d}' % level, '{"ie":1,"sort":0}',
         '{"forallE":{"binderInfo":"%s","body":1,"name":2,"type":0},"ie":2}' % info,
         '{"thm":{"name":1,"levelParams":[],"type":2,"value":2,"all":[1]}}'])), 't'))


d_binder = binder_digest('x', 'default', 0)
check('digest ignores binder names and binder info',
      is_sha256(d_binder) and d_binder == binder_digest('y', 'implicit', 0) != binder_digest('x', 'default', 1))

# What the digest is for: a `prelude` project can declare a library name with the real type and
# another body. Each pair below differs in one thing only, and must not share a digest.
BODIES = [META] + ['{"in":%d,"str":{"pre":0,"str":"%s"}}' % (i + 1, n) for i, n in enumerate('tab')] + [
    '{"il":1,"succ":0}', '{"il":2,"succ":1}',
    '{"ie":0,"const":{"name":2,"us":[]}}', '{"ie":1,"const":{"name":3,"us":[]}}',
    '{"ie":2,"natVal":"5"}', '{"ie":3,"natVal":"6"}', '{"ie":4,"strVal":"x"}', '{"ie":5,"strVal":"y"}',
    '{"bvar":0,"ie":6}', '{"bvar":1,"ie":7}', '{"ie":8,"sort":1}', '{"ie":9,"sort":2}']
A, B, FIVE, SIX, X, Y, BVAR0, BVAR1, SORT1, SORT2 = range(10)


def body_digest(value, record='def', type_=SORT1):
    """Digest of `t : type_ := value`, a def or a theorem, both expressions taken from BODIES."""
    fields = '"name":1,"levelParams":[],"type":%d,"value":%d,"all":[1]' % (type_, value)
    decl = ('{"def":{%s,"hints":"abbrev","safety":"safe"}}' if record == 'def' else '{"thm":{%s}}') % fields
    return attempt(lambda: vx.digest(vx.load_export(export_file(BODIES + [decl])), 't'))


def differ(*pairs):
    return all(is_sha256(d1) and is_sha256(d2) and d1 != d2 for d1, d2 in pairs)


check('digest covers the body', differ((body_digest(A), body_digest(SORT1)),
                                       (body_digest(A, 'thm'), body_digest(SORT1, 'thm'))))
check('digest covers the type', differ((body_digest(A, type_=SORT1), body_digest(A, type_=SORT2))))
check('digest covers which constant is named', differ((body_digest(A), body_digest(B))))
check('digest covers literals', differ((body_digest(FIVE), body_digest(SIX)), (body_digest(X), body_digest(Y))))
check('digest covers bvar indices', differ((body_digest(BVAR0), body_digest(BVAR1))))
check('digest covers universe levels below the top', differ((body_digest(SORT1), body_digest(SORT2))))


def block_digests(mk2_type):
    """Digests of T, T.mk1 and T.rec in a block where only the type of T.mk2 varies: T, or a → T."""
    lines = [META] + ['{"in":%d,"str":{"pre":%d,"str":"%s"}}' % (i + 1, p, n) for i, (p, n) in
                      enumerate([(0, 'T'), (1, 'mk1'), (1, 'mk2'), (1, 'rec'), (0, 'a')])]
    lines += ['{"ie":0,"sort":0}', '{"ie":1,"const":{"name":1,"us":[]}}', '{"ie":2,"const":{"name":5,"us":[]}}',
              '{"forallE":{"binderInfo":"default","body":1,"name":0,"type":2},"ie":3}']
    ctor = {'levelParams': [], 'induct': 1, 'numParams': 0, 'numFields': 0, 'isUnsafe': False}
    lines.append(json.dumps({'inductive': {
        'types': [{'name': 1, 'levelParams': [], 'type': 0, 'numParams': 0, 'numIndices': 0, 'all': [1],
                   'ctors': [2, 3], 'numNested': 0, 'isRec': False, 'isReflexive': False, 'isUnsafe': False}],
        'ctors': [dict(ctor, name=2, type=1, cidx=0), dict(ctor, name=3, type=mk2_type, cidx=1)],
        'recs': [{'name': 4, 'levelParams': [], 'type': 0, 'all': [1], 'numParams': 0, 'numIndices': 0,
                  'numMotives': 1, 'numMinors': 2, 'rules': [], 'k': False, 'isUnsafe': False}]}}))
    env = attempt(lambda: vx.load_export(export_file(lines)))
    return [attempt(lambda: vx.digest(env, n)) for n in ('T', 'T.mk1', 'T.rec')]


check('digest of every block member covers the whole block', differ(*zip(block_digests(1), block_digests(3))))

NAME_X = '{"in":1,"str":{"pre":0,"str":"x"}}'
SORT = '{"ie":0,"sort":0}'
AXIOM_X = '{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}'
REPEATED = [META, NAME_X, '{"in":2,"str":{"pre":0,"str":"x"}}', '{"in":3,"str":{"pre":0,"str":"t"}}', SORT,
            '{"ie":1,"const":{"name":1,"us":[]}}', AXIOM_X.replace('"name":1', '"name":2'),
            '{"thm":{"name":3,"levelParams":[],"type":1,"value":1,"all":[3]}}']
check('export name repeated under another id is the same name',
      attempt(lambda: (lambda env: (env.kind('x'), vx.axioms_of(env, 't')))(vx.load_export(export_file(REPEATED))))
      == ('axiom', {'x'}))
check('export minimal accepted',attempt(lambda: vx.load_export(export_file([META, NAME_X, SORT, AXIOM_X])).kind('x'))
      == 'axiom')
check('export empty rejected', export_rejected([]))
check('export without meta rejected', export_rejected([NAME_X, SORT, AXIOM_X]))
check('export unknown format rejected', export_rejected([META.replace('"format":{"version":"3.1.0"}',
                                                                      '"format":{"version":"9.0.0"}')]))
check('export not json rejected', export_rejected([META, 'nope']))
check('export not UTF-8 rejected', export_rejected([META, b'{"in":1,"str":{"pre":0,"str":"\xff"}}']))
check('export lone surrogate rejected', export_rejected([META, '{"in":1,"str":{"pre":0,"str":"\\ud800"}}']))
check('export deep nesting rejected', export_rejected([META, '[' * 100000]))
check('export huge number rejected', export_rejected([META, '{"in":1%s,"str":{"pre":0,"str":"x"}}' % ('0' * 5000)]))
check('export unknown record rejected', export_rejected([META, '{"foo":1}']))
check('export extra key rejected', export_rejected([META, '{"in":1,"str":{"pre":0,"str":"x"},"x":1}']))
check('export extra field rejected', export_rejected([META, '{"in":1,"str":{"pre":0,"str":"x","x":1}}']))
check('export missing field rejected', export_rejected([META, NAME_X, SORT,
                                                        '{"axiom":{"name":1,"levelParams":[],"type":0}}']))
check('export id out of sequence rejected', export_rejected([META, '{"in":2,"str":{"pre":0,"str":"x"}}']))
check('export forward reference rejected', export_rejected([META, '{"ie":0,"app":{"fn":1,"arg":1}}']))
check('export bool id rejected', export_rejected([META, '{"in":true,"str":{"pre":0,"str":"x"}}']))
check('export anonymous declaration rejected', export_rejected([META, SORT, AXIOM_X.replace('"name":1', '"name":0')]))
check('export duplicate declaration rejected', export_rejected([META, NAME_X, SORT, AXIOM_X, AXIOM_X]))
check('export second meta rejected', export_rejected([META, META]))
check('export dangling constant rejected', export_rejected(
    [META, NAME_X, '{"in":2,"str":{"pre":0,"str":"t"}}', SORT, '{"ie":1,"const":{"name":1,"us":[]}}',
     '{"thm":{"name":2,"levelParams":[],"type":1,"value":1,"all":[2]}}'], lambda env: vx.axioms_of(env, 't')))
check('export unknown name rejected', export_rejected([META, NAME_X, SORT, AXIOM_X], lambda env: vx.digest(env, 'y')))

MAX_LINE = 64 * 1024 * 1024
HEAD, TAIL = b'{"ie":0,"strVal":"', b'"}'
check('export line of 64 MB accepted', attempt(lambda: vx.load_export(export_file(
    [META, HEAD + b'a' * (MAX_LINE - len(HEAD) - len(TAIL)) + TAIL])).names()) == frozenset())
# Cut after 64 MB + 1 bytes, this line would read as two good records.
FIRST = HEAD + b'a' + TAIL
check('export line over 64 MB rejected', export_rejected(
    [META, FIRST + b' ' * (MAX_LINE + 1 - len(FIRST)) + NAME_X.encode()]))

# What the sanity checks read off the export: binders, Prop-valued definitions, constant bodies.
W = attempt(lambda: vx.load_export(os.path.join(FIXTURES, 'weak.ndjson')))
G = good
check('binders: a statement by name, info and use',
      attempt(lambda: vx.binders(W, 'Weak.add_zero_of_valid', 'type')) == [('n', 'default', True), ('h', 'default', False)])
check('binders: the proof of add_zero_of_valid never uses h',
      attempt(lambda: [u for _, _, u in vx.binders(W, 'Weak.add_zero_of_valid', 'value')][:2]) == [True, False])
check('binders: a hygienic binder has no plain name',
      attempt(lambda: vx.binders(W, 'Weak.arrow', 'type')) == [(None, 'default', False)]
      and attempt(lambda: vx.binders(W, 'Weak.sort_length_self', 'value')) == [(None, 'default', True)])
check('binders: a proof that is not a lambda has none',
      attempt(lambda: vx.binders(W, 'Weak.by_lemma', 'value')) == []
      and attempt(lambda: vx.binders(G, 'propext', 'value')) == [])
check('binders: a chain ends at the first binder of another kind (Not is fun a => a → False)',
      attempt(lambda: vx.binders(G, 'Not', 'value')) == [('a', 'default', True)])
ANON = [META, '{"in":1,"str":{"pre":0,"str":"t"}}', SORT, '{"ie":1,"bvar":0}',
        '{"ie":2,"forallE":{"name":0,"type":0,"body":1,"binderInfo":"implicit"}}',
        '{"ie":3,"lam":{"name":0,"type":0,"body":1,"binderInfo":"instImplicit"}}',
        '{"thm":{"name":1,"levelParams":[],"type":2,"value":3,"all":[1]}}']
check('binders: an anonymous binder has no name, and keeps its binder info',
      attempt(lambda: (lambda env: (vx.binders(env, 't', 'type'), vx.binders(env, 't', 'value')))(
          vx.load_export(export_file(ANON)))) == ([(None, 'implicit', True)], [(None, 'instImplicit', True)]))
check('ends_in_prop: Safe and Valid, not sort',
      attempt(lambda: vx.ends_in_prop(W, 'Weak.Safe') and vx.ends_in_prop(W, 'Weak.Valid')
              and not vx.ends_in_prop(W, 'Weak.sort')) is True)
check('ends_in_prop: a type ending in another sort is not Prop (List, Nat)',
      attempt(lambda: vx.ends_in_prop(W, 'List') or vx.ends_in_prop(W, 'Nat')) is False)
check('body_constant: Safe is True, Valid is none',
      attempt(lambda: vx.body_constant(W, 'Weak.Safe') == 'True' and vx.body_constant(W, 'Weak.Valid') is None) is True)
check('universe_params: sort none, List one',
      attempt(lambda: vx.universe_params(W, 'Weak.sort') == 0 and vx.universe_params(W, 'List') == 1) is True)
check('name_components: a guillemet name',
      attempt(lambda: vx.name_components(G, 'Good.«key never leaves»')) == ('Good', 'key never leaves'))

# The sanity checks: a claim's warnings, from its definitions and the kernel helper's verdicts.
try:
    from vacheck import sanity  # noqa: E402
except ImportError as e:
    print('      cannot import vacheck.sanity: %s' % e)
    sanity = None


def raises(fn, exc):
    try:
        fn()
    except exc:
        return True
    return False


# DEFS is each claim's definitions as analyze computes them; ANY is the helper's verdicts (Task 3).
DEFS = {'Weak.prog_safe': ['Weak.Safe', 'Weak.prog'], 'Weak.sort_example': ['Weak.Sorted', 'Weak.sort'],
        'Weak.add_zero_of_valid': ['Weak.Valid'], 'Weak.sort_length_self': ['Weak.sort'],
        'Weak.vacuous': ['Weak.sort'], 'Weak.no_project': [], 'Weak.arrow': ['Weak.Valid'], 'Weak.by_lemma': []}
ANY = {'Weak.prog_safe': {'Weak.prog'}, 'Weak.add_zero_of_valid': {'Weak.Valid'},
       'Weak.sort_length_self': {'Weak.sort'}, 'Weak.vacuous': {'Weak.sort'}, 'Weak.arrow': {'Weak.Valid'}}
WANT = {'Weak.prog_safe': [('holds-for-any', 'Weak.prog', None), ('always-true', 'Weak.Safe', None)],
        'Weak.sort_example': [],
        'Weak.add_zero_of_valid': [('holds-for-any', 'Weak.Valid', None), ('unused-assumption', 'h', None)],
        'Weak.sort_length_self': [('holds-for-any', 'Weak.sort', None)],
        'Weak.vacuous': [('holds-for-any', 'Weak.sort', None)],
        'Weak.no_project': [('no-project-definition', None, None)],
        'Weak.arrow': [('holds-for-any', 'Weak.Valid', None), ('unused-assumption', None, None)],
        'Weak.by_lemma': [('no-project-definition', None, None)]}


def got(t, any_=None, env=None, defs=None, shown=None):
    """The warnings of theorem t as (check, name, arg): weak's, unless env and defs are given."""
    ws = sanity.warnings(W if env is None else env, t, DEFS[t] if defs is None else defs,
                         ANY.get(t, set()) if any_ is None else any_, **({} if shown is None else {'shown': shown}))
    if not all(type(w) is dict and list(w) == ['check', 'name', 'arg'] for w in ws):
        print('      not {check, name, arg}: %r' % ws)
        return None
    return [(w['check'], w['name'], w['arg']) for w in ws]


def weak_warnings():
    out = {t: got(t) for t in WANT}
    for t in WANT:
        if out[t] != WANT[t]:
            print('      %s: %r' % (t, out[t]))
    return out


check('sanity: the warnings of each weak claim', attempt(weak_warnings) == WANT)
check("sanity: no holds-for-any without the kernel's verdict",
      attempt(lambda: got('Weak.prog_safe', set())) == [('always-true', 'Weak.Safe', None)])
check('sanity: a verdict for a definition the statement does not mention is an error',
      attempt(lambda: raises(lambda: sanity.warnings(W, 'Weak.no_project', [], {'Weak.sort'}), sanity.SanityError))
      is True)
check('sanity: targets keep monomorphic defs, in order',
      attempt(lambda: sanity.targets(G, ['Good.anyIn_nil'], {'Good.anyIn_nil': ['Good.Range', 'Good.anyIn']}))
      == [('Good.anyIn_nil', ('Good.anyIn',))])
# The re-check replaces a definition only where the statement names it, so it tries one only when no
# other constant of the statement reaches it: isHigh is made of threshold, and even and odd are one
# mutual block, compiled to helpers that name neither.
R = attempt(lambda: vx.load_export(os.path.join(FIXTURES, 'reach.ndjson')))
check('sanity: targets skip a definition another constant of the statement reaches, and a mutual block',
      attempt(lambda: sanity.targets(R, ['Reach.safe', 'Reach.even_two'],
                                     {'Reach.safe': ['Reach.isHigh', 'Reach.threshold'],
                                      'Reach.even_two': ['Reach.even', 'Reach.odd']}))
      == [('Reach.safe', ('Reach.isHigh',)), ('Reach.even_two', ())])
check('sanity: the weak and good statements reach none of their other definitions',
      attempt(lambda: sanity.targets(W, ['Weak.prog_safe', 'Weak.sort_example'],
                                     {'Weak.prog_safe': ['Weak.Safe', 'Weak.prog'],
                                      'Weak.sort_example': ['Weak.Sorted', 'Weak.sort']}))
      == [('Weak.prog_safe', ('Weak.Safe', 'Weak.prog')), ('Weak.sort_example', ('Weak.Sorted', 'Weak.sort'))]
      and attempt(lambda: sanity.targets(G, ['Good.pick_lowest'], {'Good.pick_lowest': ['Good.lowest', 'Good.pick']}))
      == [('Good.pick_lowest', ('Good.lowest', 'Good.pick'))])


class Build:
    """A synthetic export, written record by record."""

    def __init__(self):
        self.lines, self._names, self._exprs, self._levels = [META], {}, 0, 1

    def name(self, *comps):
        """The id of the name with these components (a str for Name.str, an int for Name.num); 0 for none."""
        pre = 0
        for comp in comps:
            if (pre, comp) not in self._names:
                self._names[pre, comp] = i = len(self._names) + 1
                kind, part = (('num', {'pre': pre, 'i': comp}) if type(comp) is int
                              else ('str', {'pre': pre, 'str': comp}))
                self.lines.append(json.dumps({'in': i, kind: part}))
            pre = self._names[pre, comp]
        return pre

    def param(self, name):
        self.lines.append(json.dumps({'il': self._levels, 'param': self.name(name)}))
        self._levels += 1
        return self._levels - 1

    def expr(self, tag, value):
        self.lines.append(json.dumps({'ie': self._exprs, tag: value}))
        self._exprs += 1
        return self._exprs - 1

    def const(self, *comps):
        return self.expr('const', {'name': self.name(*comps), 'us': []})

    def bind(self, tag, binder, type_, body, info='default'):
        """A lam or forallE whose binder's name has the components `binder`: () for none."""
        return self.expr(tag, {'name': self.name(*binder), 'type': type_, 'body': body, 'binderInfo': info})

    def define(self, name, type_, value, params=()):
        """A definition named `name`, or the components of a tuple `name`."""
        n = self.name(*name) if isinstance(name, tuple) else self.name(name)
        ps = [self.name(p) for p in params]
        self.lines.append(json.dumps({'def': {'name': n, 'levelParams': ps, 'type': type_, 'value': value,
                                              'hints': 'abbrev', 'safety': 'safe', 'all': [n]}}))

    def theorem(self, name, type_, value):
        n = self.name(name)
        self.lines.append(json.dumps({'thm': {'name': n, 'levelParams': [], 'type': type_, 'value': value,
                                              'all': [n]}}))

    def inductive(self, name, type_, ctors):
        """An inductive type without parameters or indices, with constructors (name, type, number of fields)."""
        n, cs = self.name(name), [(self.name(name, c), t, k) for c, t, k in ctors]
        rec = self.name(name, 'rec')
        self.lines.append(json.dumps({'inductive': {
            'types': [{'name': n, 'levelParams': [], 'type': type_, 'numParams': 0, 'numIndices': 0, 'all': [n],
                       'ctors': [c for c, _, _ in cs], 'numNested': 0, 'isRec': False, 'isReflexive': False,
                       'isUnsafe': False}],
            'ctors': [{'name': c, 'levelParams': [], 'type': t, 'induct': n, 'cidx': i, 'numParams': 0,
                       'numFields': k, 'isUnsafe': False} for i, (c, t, k) in enumerate(cs)],
            'recs': [{'name': rec, 'levelParams': [], 'type': type_, 'all': [n], 'numParams': 0, 'numIndices': 0,
                      'numMotives': 1, 'numMinors': len(cs), 'rules': [], 'k': False, 'isUnsafe': False}]}}))

    def env(self):
        return vx.load_export(export_file(self.lines))


def chain(b, tag, binders, body):
    """Binders (components, info), outermost first, around body; every binder's type is Nat."""
    for comps, info in reversed(binders):
        body = b.bind(tag, comps, b.const('Nat'), body, info)
    return body


HYG = ('x', '_@', 'M', '_hyg', 1)  # a name with macro scopes, as `x✝` is
b = Build()
PROP, FALSE, INTRO = b.expr('sort', 0), b.const('False'), b.const('True', 'intro')
# leanexport shares one expression among those equal but for binder names and info, so a definition's
# type may carry another declaration's binder names. P's type is ∀ (n : Nat) (k : Nat) {m : Nat}, Prop;
# its value, fun (m : Nat) (n : Nat) (q : Nat) => m, ignores its second argument, which the type calls k
# and the value n, and its third, which the type makes implicit.
b.define('P', chain(b, 'forallE', [(('n',), 'default'), (('k',), 'default'), (('m',), 'implicit')], PROP),
         chain(b, 'lam', [(('m',), 'default'), (('n',), 'default'), (('q',), 'default')], b.expr('bvar', 2)))
# Q : ∀ (p.q : Nat), Prop := fun p.q => False ignores p.q, a binder name of two components.
b.define('Q', chain(b, 'forallE', [(('p', 'q'), 'default')], PROP), chain(b, 'lam', [(('p', 'q'), 'default')], FALSE))
b.define('U', b.expr('sort', b.param('u')), b.const('True'), params=('u',))  # U.{u} : Sort u
# t (a : Nat) {b : Nat} (c : Nat) (d : Nat) : Q a := fun a b r s => True.intro s. The proof uses only d,
# and the statement only a: c is the one assumption the proof never uses (the proof calls it r).
Q_A = b.expr('app', {'fn': b.const('Q'), 'arg': b.expr('bvar', 3)})
b.theorem('t', chain(b, 'forallE', [(('a',), 'default'), (('b',), 'implicit'), (('c',), 'default'),
                                    (('d',), 'default')], Q_A),
          chain(b, 'lam', [(('a',), 'default'), (('b',), 'default'), (('r',), 'default'), (('s',), 'default')],
                b.expr('app', {'fn': INTRO, 'arg': b.expr('bvar', 0)})))
# names : ∀ (a…a : Nat) (a…a : Nat) (x\u202ey : Nat) (ok : Nat), True := fun _ _ _ _ => True.intro, with names of
# 200 and 201 characters and one holding U+202E: only those a report can show are named.
NAMES = ['a' * 200, 'a' * 201, 'x\u202ey', 'ok']
b.theorem('names', chain(b, 'forallE', [((n,), 'default') for n in NAMES], b.const('True')),
          chain(b, 'lam', [((n,), 'default') for n in NAMES], INTRO))
# big : ∀ (x : Nat), True := fun x => #(2^40): a bound variable whose set of indices would not fit.
b.theorem('big', chain(b, 'forallE', [(('x',), 'default')], b.const('True')),
          chain(b, 'lam', [(('x',), 'default')], b.expr('bvar', 2 ** 40)))
# let_x : ∀ (x : Nat), True := fun x => let y := True.intro; x uses x through the let, and let_y, whose
# body is y, does not.
for name, body in (('let_x', 1), ('let_y', 0)):
    b.theorem(name, chain(b, 'forallE', [(('x',), 'default')], b.const('True')),
              chain(b, 'lam', [(('x',), 'default')], b.expr('letE', {'name': b.name('y'), 'type': b.const('True'),
                                                                     'value': INTRO, 'body': b.expr('bvar', body),
                                                                     'nondep': False})))
shapes = attempt(b.env)
T_WANT = [('holds-for-any', 'P', None), ('ignores-argument', 'Q', 'p.q'), ('ignores-argument', 'P', None),
          ('unused-assumption', 'c', None)]
check('sanity: targets drop a definition with universe parameters, and a name that is not a def',
      attempt(lambda: sanity.targets(shapes, ['t'], {'t': ['Q', 'U', 'P', 'Nat']})) == [('t', ('Q', 'P'))])
# F := F._unary and G := G._mutual, as Lean compiles well-founded recursion: the helper names nothing of
# F, yet it is F's body, so a helper reaches the definition it serves. t and u name both.
hb = Build()
for owner, helper in (('F', '_unary'), ('G', '_mutual')):
    hb.define((owner, helper), hb.const('Nat'), hb.expr('natVal', '0'))
    hb.define(owner, hb.const('Nat'), hb.const(owner, helper))
for thm, owner, helper in (('t', 'F', '_unary'), ('u', 'G', '_mutual')):
    hb.theorem(thm, hb.bind('forallE', ('x',), hb.const(owner), hb.const(owner, helper)), INTRO)
helpers = attempt(hb.env)
check('sanity: a _unary or _mutual helper reaches the definition it serves',
      attempt(lambda: sanity.targets(helpers, ['t', 'u'], {'t': ['F', 'F._unary'], 'u': ['G', 'G._mutual']}))
      == [('t', ()), ('u', ())])
# L : Nat := X, where L is a name of the toolchain's library: analyze has compared the export's L with
# the toolchain's, which cannot name the project's X, so the walk takes no step from L.
lb = Build()
lb.define('X', lb.const('Nat'), lb.expr('natVal', '0'))
lb.define('L', lb.const('Nat'), lb.const('X'))
lb.theorem('t', lb.bind('forallE', ('x',), lb.const('L'), lb.const('X')), INTRO)
lib_env = attempt(lb.env)
check('sanity: targets take no step from a name of the library',
      attempt(lambda: (sanity.targets(lib_env, ['t'], {'t': ['X']}),
                       sanity.targets(lib_env, ['t'], {'t': ['X']}, frozenset({'L', 'Nat'}))))
      == ([('t', ())], [('t', ('X',))]))
# A theorem in a statement is one fact, whatever its proof: lem's proof names D, yet lem takes no step to
# D. The members of an inductive block reach each other: I.a reaches D through I.b : D → I. And a name
# that does not read back as itself (a component holding » and a dot, which Lean leaves as it is)
# reaches anything: what it would reach is not known.
rb = Build()
rb.define('D', rb.expr('sort', 0), rb.const('True'))
rb.theorem('lem', rb.const('True'), rb.const('D'))
rb.inductive('I', rb.expr('sort', 0), [('a', rb.const('I'), 0),
                                       ('b', rb.bind('forallE', ('x',), rb.const('D'), rb.const('I')), 1)])
rb.define('a»b.c', rb.expr('sort', 0), rb.const('True'))
for thm, comps in (('by_lem', ('lem',)), ('by_ctor', ('I', 'a')), ('by_name', ('a»b.c',))):
    rb.theorem(thm, rb.expr('app', {'fn': rb.const(*comps), 'arg': rb.const('D')}), rb.const('True', 'intro'))
reached = attempt(rb.env)
check("sanity: a theorem's proof takes no step, an inductive block's members reach each other, and a name "
      "that does not read back reaches anything",
      attempt(lambda: sanity.targets(reached, ['by_lem', 'by_ctor', 'by_name'],
                                     {t: ['D'] for t in ('by_lem', 'by_ctor', 'by_name')}))
      == [('by_lem', ('D',)), ('by_ctor', ()), ('by_name', ())])
check("sanity: an argument's explicitness comes from the definition's type, its use from the value, its name from both",
      attempt(lambda: got('t', {'P'}, shapes, ['Q', 'U', 'P'])) == T_WANT)
check('sanity: an assumption is judged only when the rest of the statement does not mention it',
      attempt(lambda: [w for w in got('t', set(), shapes, ['Q']) if w[0] == 'unused-assumption'])
      == [('unused-assumption', 'c', None)])
check("sanity: a let's body is under one more binder",
      attempt(lambda: (got('let_x', set(), shapes, []), got('let_y', set(), shapes, [])))
      == ([('no-project-definition', None, None)],
          [('no-project-definition', None, None), ('unused-assumption', 'x', None)]))
asked = []
check("sanity: an assumption's name the page does not show is None, and only those warned of are asked about",
      attempt(lambda: got('t', {'P'}, shapes, ['Q', 'U', 'P'],
                          shown=lambda d, k, n: asked.append((d, k, n)) or n != 'c'))
      == T_WANT[:3] + [('unused-assumption', None, None)] and asked == [('t', 2, 'c')])
asked_names = []
check('sanity: a name over 200 characters, or with a character a report cannot show, is None',
      attempt(lambda: got('names', set(), shapes, [], shown=lambda d, k, n: asked_names.append(n) or True))
      == [('no-project-definition', None, None), ('unused-assumption', 'a' * 200, None),
          ('unused-assumption', None, None), ('unused-assumption', None, None), ('unused-assumption', 'ok', None)]
      and asked_names == ['a' * 200, 'ok'])

# The printed fixture, exported by Lean: leanexport gave P2's and P4's types the binder names of a shared
# expression, (n x✝ : Nat), while nanoda_bin prints their values, fun {α} (m n : Nat) => n > 0. Pos's type
# is printed (n a✝ : Nat), its value fun m n => m > 0.
PR = attempt(lambda: vx.load_export(os.path.join(FIXTURES, 'printed.ndjson')))
check('sanity: an argument whose type and value name it differently is not named (P2, P4, Pos)',
      [attempt(lambda t=t, d=d: got(t, set(), PR, [d])) for t, d in (
          ('Printed.u2', 'Printed.P2'), ('Printed.u4', 'Printed.P4'), ('Printed.pos', 'Printed.Pos'))]
      == [[('ignores-argument', d, None)] for d in ('Printed.P2', 'Printed.P4', 'Printed.Pos')])
check("sanity: an argument whose type and value name it alike is named (Weak.Safe's p)",
      attempt(lambda: [vx.binder_name(W, a) for a in sanity._ignored(W, 'Weak.Safe', vx.Budget())]) == ['p'])


def with_steps(n, fn):
    """fn() with vx.MAX_STEPS set to n."""
    old = vx.MAX_STEPS
    vx.MAX_STEPS = n
    try:
        return fn()
    finally:
        vx.MAX_STEPS = old


check('sanity: binder walks past their budget give no binder warning, and keep the others',
      attempt(lambda: with_steps(5, lambda: got('t', {'P'}, shapes, ['Q', 'U', 'P'])))
      == [('holds-for-any', 'P', None)]
      and attempt(lambda: got('big', set(), shapes, [])) == [('no-project-definition', None, None)]
      # Q's walk ends within the budget, and big's proof runs it out: Q's warning goes too.
      and attempt(lambda: got('big', {'Q'}, shapes, ['Q'])) == [('holds-for-any', 'Q', None)])



def hostile(d, m, in_proof):
    """D binders around a term of M nodes, each under up to M binders: L(0) is a bound variable none of
    them binds, and L(k) is ∀ (_ : L(k-1)), L(k-1). The theorem h is ∀ x0 … x(D-1), L(M), proved by
    fun x0 … => True.intro; or, with the term in the proof only, ∀ x0 …, True := fun x0 … => L(M)."""
    b = Build()
    term = b.expr('bvar', d + m)
    for _ in range(m):
        term = b.bind('forallE', (), term, term)
    stmt, proof = (b.const('True'), term) if in_proof else (term, b.const('True', 'intro'))
    xs = [(('x%d' % i,), 'default') for i in range(d)]
    b.theorem('h', chain(b, 'forallE', xs, stmt), chain(b, 'lam', xs, proof))
    return b.env()


def timed(env):
    t0 = time.monotonic()
    out = got('h', set(), env, [])
    secs = time.monotonic() - t0
    print('      %.2f s' % secs)
    return out, secs < 2


H_WANT = ([('no-project-definition', None, None)] + [('unused-assumption', 'x%d' % i, None) for i in range(9)], True)
check('sanity: 1600 binders over a shared term of 1600 nodes, in the statement, in under 2 s',
      attempt(lambda: timed(hostile(1600, 1600, False))) == H_WANT)
check('sanity: 100 binders over a shared term of 6000 nodes, in the proof only, in under 2 s',
      attempt(lambda: timed(hostile(100, 6000, True))) == H_WANT)


def props_export(n):
    """Definitions d0 ... d(n-1), each `: Prop := True`, and a theorem t whose statement is d0 d1 ... d(n-1)."""
    lines = [META, '{"in":1,"str":{"pre":0,"str":"True"}}', '{"in":2,"str":{"pre":0,"str":"t"}}']
    lines += ['{"in":%d,"str":{"pre":0,"str":"d%d"}}' % (i + 3, i) for i in range(n)]
    lines += [SORT, '{"ie":1,"const":{"name":1,"us":[]}}']
    lines += ['{"ie":%d,"const":{"name":%d,"us":[]}}' % (i + 2, i + 3) for i in range(n)]
    lines += ['{"ie":%d,"app":{"fn":%d,"arg":%d}}' % (n + 1 + i, 2 if i == 1 else n + i, i + 2) for i in range(1, n)]
    lines += ['{"def":{"name":%d,"levelParams":[],"type":0,"value":1,"hints":"abbrev","safety":"safe","all":[%d]}}'
              % (i + 3, i + 3) for i in range(n)]
    lines.append('{"thm":{"name":2,"levelParams":[],"type":%d,"value":1,"all":[2]}}' % (2 * n))
    return lines


props = attempt(lambda: vx.load_export(export_file(props_export(11))))
D11 = ['d%d' % i for i in reversed(range(11))]  # the order of defs, not of the names
check('sanity: at most 10 warnings',
      attempt(lambda: vx.constants_in_type(props, 't') == set(D11) and got('t', set(), props, D11)
              == [('always-true', d, None) for d in D11[:10]]) is True)
check('sanity: the cap keeps the most serious first',
      attempt(lambda: got('t', {'d0'}, props, D11))
      == [('holds-for-any', 'd0', None)] + [('always-true', d, None) for d in D11[:9]])


def given(env, t, defs, any_=frozenset(), shown=None):
    return sanity.warnings(env, t, defs, any_, **({} if shown is None else {'shown': shown}))


def every_list_accepted():
    """validate_result on each list of warnings that the cases above give: warnings never fail a check."""
    lists = [given(W, t, DEFS[t], ANY.get(t, set())) for t in WANT]
    lists += [given(shapes, 't', ['Q', 'U', 'P'], {'P'}),
              given(shapes, 't', ['Q', 'U', 'P'], {'P'}, lambda d, k, n: False),
              given(shapes, 'names', []), given(shapes, 'let_y', []), given(shapes, 'big', ['Q'], {'Q'})]
    lists += [given(PR, t, ds) for t, ds in (('Printed.u2', ['Printed.P2']), ('Printed.u4', ['Printed.P4']),
                                             ('Printed.pos', ['Printed.Pos']), ('Printed.t5', []))]
    lists += [given(props, 't', D11), given(props, 't', D11, {'d0'})]
    rejected = [ws for ws in lists if result_rejected(warned(*ws))]
    for ws in rejected:
        print('      rejected: %r' % ws)
    return len(lists) == 19 and not rejected


check('result v2: every list of warnings that sanity.warnings gives here is accepted',
      attempt(every_list_accepted) is True)

T2 = [('A.t', ('A.f', 'A.g')), ('A.u', ()), ('A.v', ('A.h',))]
check('read_verdicts: one line per pair',
      attempt(lambda: sanity.read_verdicts('0 0 any\n0 1 needed\n2 0 skipped\n', T2))
      == {'A.t': frozenset({'A.f'}), 'A.u': frozenset(), 'A.v': frozenset()})
check('read_verdicts: no pairs, no lines',
      attempt(lambda: sanity.read_verdicts('', [('A.u', ())])) == {'A.u': frozenset()}
      and attempt(lambda: raises(lambda: sanity.read_verdicts('\n', [('A.u', ())]), sanity.SanityError)) is True)
for bad in ('0 0 any\n2 0 any\n', '0 0 any\n0 1 any\n2 0 any\n2 0 any\n', '0 1 any\n0 0 any\n2 0 any\n',
            '0 0 maybe\n0 1 any\n2 0 any\n', '0 0 any\n0 1 any\n2 0 any', '0 0 any\n0 1 any\n2 0 any\n3 0 any\n',
            '00 0 any\n0 1 any\n2 0 any\n', '0 0 any\r\n0 1 any\n2 0 any\n', '0 0 any \n0 1 any\n2 0 any\n',
            '0  0 any\n0 1 any\n2 0 any\n', '٠ 0 any\n0 1 any\n2 0 any\n', '0 0 ANY\n0 1 any\n2 0 any\n',
            b'0 0 any\n0 1 any\n2 0 any\n', '0 0 any\n0 1 any\n', '', '0 0 any\n0 1 any\n2 0 any\nmaybe'):
    check('read_verdicts: rejected %r' % bad,
          attempt(lambda: raises(lambda: sanity.read_verdicts(bad, T2), sanity.SanityError)) is True)

# Supported toolchains.
try:
    from vacheck import toolchain as vt  # noqa: E402
except ImportError as e:
    print('      cannot import vacheck.toolchain: %s' % e)
    vt = None

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RELEASES = 'https://github.com/leanprover/lean4/releases/download/'
T35 = ('v4.35.0', RELEASES + 'v4.35.0/lean-4.35.0-linux.tar.zst',
       '7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d')
T36 = ('v4.36.0', RELEASES + 'v4.36.0/lean-4.36.0-linux.tar.zst',
       '2b7ab1ed8b92d2e6abfaf41344823b510064dbc9c0260cac73eb496ab2dea6eb')
check('toolchain lookup gives the pinned release tarballs',
      attempt(lambda: [tuple(vt.lookup(v)) for v in ('v4.35.0', 'v4.36.0')]) == [T35, T36]
      and attempt(lambda: (lambda t: (t.version, t.url, t.sha256))(vt.lookup('v4.36.0'))) == T36)
check('toolchain lookup of anything else is None',
      attempt(lambda: [vt.lookup(v) for v in ('v4.34.0', '4.36.0', 'v4.36', 'leanprover/lean4:v4.36.0',
                                              'v4.36.0-rc1', 'v4.36.0 ', '', None)]) == [None] * 8)


def toolchain_table():
    """Every entry: v4.35.0 or later, the official linux x86_64 tarball, a sha256; and lookup agrees."""
    with open(os.path.join(ROOT, 'vacheck', 'toolchains.json'), encoding='utf-8') as f:
        table = json.load(f)
    for v, entry in table.items():
        m = re.fullmatch(r'v(\d+)\.(\d+)\.(\d+)', v)
        if not m or tuple(map(int, m.groups())) < (4, 35, 0) or set(entry) != {'url', 'sha256'}:
            return False
        if entry['url'] != RELEASES + '%s/lean-%s-linux.tar.zst' % (v, v[1:]) or not is_sha256(entry['sha256']):
            return False
        if tuple(vt.lookup(v)) != (v, entry['url'], entry['sha256']):
            return False
    return len(table) >= 2


check('toolchain table holds official tarballs from v4.35.0 on', attempt(toolchain_table) is True)


def toolchain_from_zip():
    """The checker ships as a zip: the table must be readable from inside one."""
    import subprocess
    import zipfile
    path = os.path.join(TMP, 'vacheck.zip')
    with zipfile.ZipFile(path, 'w') as z:
        for f in ('__init__.py', 'toolchain.py', 'toolchains.json'):
            z.write(os.path.join(ROOT, 'vacheck', f), 'vacheck/' + f)
    out = subprocess.run([sys.executable, '-I', '-c', 'import sys; sys.path.insert(0, sys.argv[1]); '
                          'from vacheck.toolchain import lookup; print(lookup("v4.36.0").sha256)', path],
                         capture_output=True, text=True, cwd=TMP)
    return out.stdout.strip()


check('toolchain table readable from a zip', attempt(toolchain_from_zip) == T36[2])

# Analysis: an export against the toolchain's reference, the manifest and the source as text.
try:
    from vacheck import analyze as va  # noqa: E402
except ImportError as e:
    print('      cannot import vacheck.analyze: %s' % e)
    va = None
from vacheck import VERSION  # noqa: E402

MODULES = {'good': 'Good', 'sorry': 'Sorry', 'axiom': 'Axiom', 'native': 'Native', 'fakeeq': 'FakeEq',
           'replaced': 'Replaced', 'weak': 'Weak'}
REPO, COMMIT, KERNELS = 'github.com/acme/proj', 'c' * 40, ['lean', 'nanoda']
MB2 = 2 * 1024 * 1024
_serial = iter(range(10 ** 6))


def fresh(name):
    return os.path.join(TMP, '%d-%s' % (next(_serial), name))


def write(path, text, mode='w'):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, mode, encoding='utf-8') as f:
        f.write(text)


def printer(names):
    return {n: '<pp %s>' % n for n in names}


def reference(case, own, change=lambda name, record: False, drop=()):
    """What the toolchain's own export of the fixture's library names gives: the fixture's export
    without its own declarations (those in namespace `own`) and without the names in `drop`.
    `change(name, record)` may alter a declaration's record, and returns True if it did."""
    names = {0: None}
    path = fresh(case + '-reference.ndjson')
    with open(os.path.join(FIXTURES, case + '.ndjson'), encoding='utf-8') as f, \
            open(path, 'w', encoding='utf-8') as out:
        for line in f:
            o = json.loads(line)
            if 'in' in o:
                part = o['str'] if 'str' in o else o['num']
                comp = part['str'] if 'str' in o else str(part['i'])
                pre = names[part['pre']]
                names[o['in']] = comp if pre is None else pre + '.' + comp
            decls = [names[o[k]['name']] for k in ('axiom', 'def', 'thm', 'opaque', 'quot') if k in o]
            if 'inductive' in o:
                decls = [names[r['name']] for k in ('types', 'ctors', 'recs') for r in o['inductive'][k]]
            if any(n == own or n.startswith(own + '.') or n in drop for n in decls):
                continue
            if decls and change(decls[0], o):
                line = json.dumps(o) + '\n'
            out.write(line)
    return vx.load_export(path)


refs = {case: attempt(lambda case=case: reference(case, MODULES[case])) for case in MODULES if case != 'fakeeq'}


def source_tree(case, claims, project='core', ships=()):
    """A checkout: the fixture's Lake project in folder `project`, the manifest at the root.
    `claims` holds (says, theorem, about). Returns (root, manifest)."""
    root = fresh('repo')
    shutil.copytree(os.path.join(FIXTURES, case), os.path.join(root, project),
                    ignore=shutil.ignore_patterns('.lake'), dirs_exist_ok=True)
    raw = json.dumps({'version': 1, 'project': project, 'modules': [MODULES[case]], 'ships': list(ships),
                      'claims': [{'says': s, 'theorem': t, 'about': a} for s, t, a in claims]}).encode()
    with open(os.path.join(root, '.verificationalliance.json'), 'wb') as f:
        f.write(raw)
    return root, parse_manifest(raw)


def skipped(export, ref, manifest):
    """The helper's verdicts as if it skipped every pair it re-checks; '' when the export cannot say."""
    theorems = [c.theorem for c in manifest.claims]
    try:
        pairs = sanity.targets(export, theorems, va.project_constants(
            export, ref if isinstance(ref, (list, tuple)) else [ref], theorems))
    except vx.ExportError:
        return ''
    return ''.join('%d %d skipped\n' % (i, j) for i, (_, ds) in enumerate(pairs) for j in range(len(ds)))


def run(case, theorems=(), tree=None, ref=None, export=None, pp=printer, repo=REPO,
        manifest_path='.verificationalliance.json', verdicts=None):
    """analyze on the fixture's export and its reference, with a new source tree unless `tree` is given,
    and the helper's verdicts: skipped for every pair unless given."""
    root, manifest = tree or source_tree(case, [('x', t, 'model') for t in theorems])
    export = envs[case] if export is None else export
    ref = refs[case] if ref is None else ref
    return va.analyze(export, ref, manifest, root, repo, COMMIT, 'v4.36.0', KERNELS, pp, manifest_path,
                      skipped(export, ref, manifest) if verdicts is None else verdicts)


def analysis_error(fn):
    """The message of the AnalysisError that fn raises; None if it returns or raises anything else."""
    try:
        fn()
    except Exception as e:
        if va is not None and isinstance(e, va.AnalysisError):
            return str(e)
        print('      %s: %s' % (type(e).__name__, e))
        return None
    print('      no AnalysisError')
    return None


def rejected_with(case, theorems, *needles, **kw):
    msg = analysis_error(lambda: run(case, theorems, **kw))
    if msg is not None and not all(n in msg for n in needles):
        print('      message: %s' % msg)
        return False
    return msg is not None


def valid(r):
    try:
        validate_result(r)
    except Exception as e:
        print('      %s: %s' % (type(e).__name__, e))
        return False
    return True


F_DEF = {'name': 'Good.f', 'text': '<pp Good.f>', 'source': {'path': 'core/Good.lean', 'line': 3}, 'term': None}
good_tree = attempt(lambda: source_tree('good', [('Never \u202eleaks\x07.', 'Good.«key never leaves»', 'code'),
                                                 ('f is n + 1, or not.', 'Good.t1', 'model')], ships=['Good']))
good_res = attempt(lambda: run('good', tree=good_tree)) or {}
gc = good_res.get('claims') or [{}, {}]
check('good passes', valid(good_res)
      and [c.get('theorem') for c in gc] == ['Good.«key never leaves»', 'Good.t1']
      and [c.get('source') for c in gc]
      == [{'path': 'core/Good.lean', 'line': 7}, {'path': 'core/Good.lean', 'line': 5}])
check('good statements, defs and axioms',
      [(c.get('statement'), c.get('defs'), c.get('axioms')) for c in gc]
      == [('<pp Good.«key never leaves»>', [F_DEF], []),
          ('<pp Good.t1>', [F_DEF], ['Classical.choice', 'Quot.sound', 'propext'])])
check('good says plain and about as declared',
      [(c.get('says'), c.get('about')) for c in gc] == [('Never leaks.', 'code'), ('f is n + 1, or not.', 'model')])
check('good carries the run and the evidence',
      {k: good_res.get(k)
       for k in ('schema', 'repo', 'commit', 'toolchain', 'checker', 'project', 'kernels', 'evidence')}
      == {'schema': SCHEMA, 'repo': REPO, 'commit': COMMIT, 'toolchain': 'v4.36.0', 'checker': VERSION,
          'project': 'core', 'kernels': KERNELS, 'evidence': {'ships': ['Good'], 'replaced': []}}
      and is_sha256(good_res.get('build_digest')))

check('sorry rejected', rejected_with('sorry', ['Sorry.t'], 'Sorry.t', 'sorryAx'))
check('axiom rejected', rejected_with('axiom', ['Axiom.t'], 'Axiom.t', 'Axiom.magic'))
# Lean v4.35.0 and later have no Lean.ofReduceBool: native_decide declares an axiom of its own instead.
check('native rejected', rejected_with('native', ['Native.t'], 'Native.t._native.native_decide.ax_1_1'))
fake_msg = analysis_error(lambda: run('fakeeq', ['FakeEq.t'], ref=good))
check('fakeeq rejected', fake_msg is not None and re.search(r'(?<![\w.])Eq(?![\w.])', fake_msg) is not None)
check('missing theorem rejected', rejected_with('good', ['Good.nope'], 'Good.nope'))
check('definition claimed as theorem rejected', rejected_with('good', ['Good.f'], 'Good.f'))

# The digest names the constants a declaration uses without covering them, so every name the export
# and the reference share must be compared, not only those a claimed type mentions: instLTNat is the
# same declaration whatever Nat.lt is.
check('the type of Good.«key never leaves» does not mention Nat.lt',
      'Nat.lt' not in (attempt(lambda: vx.constants_in_type(good, 'Good.«key never leaves»')) or {'Nat.lt'}))


def other_nat_lt(name, record):
    if name != 'Nat.lt':
        return False
    record['def']['value'] = record['def']['type']
    return True


check('a mismatch in a declaration no claimed type mentions still rejects',
      rejected_with('good', ['Good.«key never leaves»'], 'Nat.lt',
                    ref=attempt(lambda: reference('good', 'Good', change=other_nat_lt))))
check('an allowed axiom the reference lacks rejected',
      rejected_with('good', ['Good.t1'], 'propext', ref=attempt(lambda: reference('good', 'Good', drop={'propext'}))))

rep = attempt(lambda: run('replaced', ['Replaced.double_eq'])) or {}
check('replaced listed', valid(rep) and rep['evidence']['replaced']
      == [{'path': 'core/Replaced.lean', 'line': 5, 'text': '@[implemented_by doubleImpl]'}])


with open(os.path.join(FIXTURES, 'good', 'Good.lean'), encoding='utf-8') as f:
    GOOD_LINES = f.read().count('\n')


def long_replaced():
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    write(os.path.join(root, 'core', 'Good.lean'), '\n   @[extern "\u2066%s"] opaque g : Nat\n' % ('a' * 300), 'a')
    return run('good', tree=(root, manifest))['evidence']['replaced']


check('replaced lines trimmed to 160 plain characters',
      attempt(long_replaced) == [{'path': 'core/Good.lean', 'line': GOOD_LINES + 2, 'text': ('@[extern "' + 'a' * 300)[:160]}])


def with_file(rel, text):
    """analyze on a new good tree with one more file in it."""
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    write(os.path.join(root, rel), text)
    return run('good', tree=(root, manifest))


check('200 replaced lines listed, 201 rejected',
      len((attempt(lambda: with_file('core/M.lean', '@[extern "x"] opaque y : Nat\n' * 200)) or {})
          .get('evidence', {}).get('replaced', ())) == 200
      and 'implemented_by, extern or csimp' in (
          analysis_error(lambda: with_file('core/M.lean', '@[extern "x"] opaque y : Nat\n' * 201)) or ''))


def many_attributes():
    import time
    start = time.monotonic()
    r = with_file('core/A.lean', '@[a]' * 32 + ' x\n')
    return r['claims'][0]['source'], time.monotonic() - start < 10


check('a line of many attributes is scanned without backtracking',
      attempt(many_attributes) == ({'path': 'core/Good.lean', 'line': 5}, True))


def digests(*edits):
    """The build digest of a new good tree, then again after each edit(root)."""
    tree = source_tree('good', [('x', 'Good.t1', 'model')])
    out = [run('good', tree=tree)['build_digest']]
    for edit in edits:
        edit(tree[0])
        out.append(run('good', tree=tree)['build_digest'])
    return out


def append(rel, text=' '):
    return lambda root: write(os.path.join(root, rel), text, 'a')


ds = attempt(lambda: digests(append('README.md'), append('core/Good.lean', '\n-- x\n')))
check('build digest changes with any file of the checkout, a README outside the project too',
      ds is not None and is_sha256(ds[0]) and len(set(ds)) == 3)
# Every build input in the checkout: every file in the project folder (C sources for an extern_lib,
# scripts and data a lakefile uses), and every .lean and Lake file anywhere: Lake compiles sources
# from outside the project (srcDir := "../src") and from folders named .lake below the project's own.
covered = ('core/lakefile.toml', 'core/lake-manifest.json', 'core/lean-toolchain', '.verificationalliance.json',
           'core/lakefile.lean', 'core/Good/Sub.lean', 'core/Good/.lake/Y.lean', 'Top.lean', 'src/X.lean',
           'other/lakefile.toml', 'other/lake-manifest.json', 'other/lean-toolchain', 'core/.git/Z.lean',
           'core/ffi/shim.c', 'core/include/shim.h', 'core/build.sh', 'core/README.md', 'core/Good.olean',
           'core/.hidden/data.bin', 'core/Good/.lake/build/lib.a',
           # vacheck 1.1.3: every file of the checkout, outside the project too (a lakefile's buildDir or an
           # extern_lib can reach ../ for its sources)
           'other/README.md', 'other/shim.c', 'build/out.o', '.github/workflows/x.yml', 'other/.lake/lib.a')
ds = attempt(lambda: digests(*[append(rel) for rel in covered]))
check('build digest covers every file in the checkout and the manifest',
      ds is not None and len(set(ds)) == len(covered) + 1)
ds = attempt(lambda: digests(append('.git/X.lean'), append('.git/objects/ab/cd')))
check('build digest leaves out the root .git only', ds is not None and len(set(ds)) == 1)


def committed_lake(rel, project='core'):
    """The AnalysisError message of analyze, and of import_roots, on a tree with `rel` added."""
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')], project=project)
    write(os.path.join(root, rel), 'x')
    return (analysis_error(lambda: run('good', tree=(root, manifest))),
            analysis_error(lambda: va.import_roots(root, project)))


LAKE_COMMITTED = '.lake is in the repository: Lake builds there, so it must not be committed (add .lake to .gitignore)'
check("a committed .lake in the project folder rejected, by analyze and by import_roots",
      attempt(lambda: committed_lake('core/.lake/build/X.olean')) == ('core/' + LAKE_COMMITTED,) * 2
      and attempt(lambda: committed_lake('.lake/packages/x', project='.')) == (LAKE_COMMITTED,) * 2)


def lake_symlink():
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    os.symlink(OUTSIDE_DIR, os.path.join(root, 'core', '.lake'))
    return analysis_error(lambda: run('good', tree=(root, manifest)))


OUTSIDE_DIR = fresh('outside-dir')
os.makedirs(OUTSIDE_DIR)
check('a .lake symlink in the project folder rejected too', attempt(lake_symlink) == 'core/' + LAKE_COMMITTED)
check('a .lake folder outside the project folder is no reason to reject',
      is_sha256((attempt(lambda: with_file('other/.lake/X.lean', 'x')) or {}).get('build_digest')))

# A second declaration of Good.t1: read, it makes the source of Good.t1 ambiguous, so null.
BIG = 'namespace Good\ntheorem t1 : True := trivial\n@[extern "x"] opaque y : Nat\n'


def big_file(size):
    """Adds core/A.lean of `size` bytes to a new good tree, then changes its last byte. Returns the
    source of Good.t1 and the replaced lines with the file added, and whether all three digests differ."""
    tree = source_tree('good', [('x', 'Good.t1', 'model')])
    path = os.path.join(tree[0], 'core', 'A.lean')
    before = run('good', tree=tree)['build_digest']
    write(path, BIG + ' ' * (size - len(BIG)))
    r = run('good', tree=tree)
    write(path, BIG + ' ' * (size - len(BIG) - 1) + 'x')
    after = run('good', tree=tree)['build_digest']
    return r['claims'][0]['source'], r['evidence']['replaced'], len({before, r['build_digest'], after}) == 3


NOT_READ = ({'path': 'core/Good.lean', 'line': 5}, [], True)
check('a lean file of 3 MiB changes the digest and is not read as text',
      attempt(lambda: big_file(3 * 1024 * 1024)) == NOT_READ)
check('a lean file over 2 MiB is not read as text', attempt(lambda: big_file(MB2 + 1)) == NOT_READ)
check('a lean file of 2 MiB is read', attempt(lambda: big_file(MB2))
      == (None, [{'path': 'core/A.lean', 'line': 3, 'text': '@[extern "x"] opaque y : Nat'}], True))


def entries_digest():
    """The build digest is the sha256 of the JSON list of typed entries, sorted by path: [path, "file", mode, sha256] with
    the git mode (100755 when executable) and [path, "link", target]; checked against a digest built here."""
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    write(os.path.join(root, 'core', 'ffi', 'shim.c'), 'int x;\n'); write(os.path.join(root, 'core', 'run.sh'), 'echo\n')
    os.chmod(os.path.join(root, 'core', 'run.sh'), 0o755)
    os.makedirs(os.path.join(root, 'app')); os.symlink('../core/ffi/shim.c', os.path.join(root, 'app', 'shim.c'))
    got = run('good', tree=(root, manifest))['build_digest']
    want = []
    for d, _, fs in os.walk(root):
        for f in fs:
            p = os.path.join(d, f); rel = os.path.relpath(p, root).replace(os.sep, '/')
            if os.path.islink(p): want.append([rel, 'link', os.readlink(p)])
            else:
                with open(p, 'rb') as fh: sha = hashlib.sha256(fh.read()).hexdigest()
                want.append([rel, 'file', '100755' if os.stat(p).st_mode & 0o100 else '100644', sha])
    want.sort()
    return got == hashlib.sha256(json.dumps(want, separators=(',', ':')).encode()).hexdigest()


def link_or_file():
    """A symlink and a file holding what the old digest hashed for it no longer give the same digest; nor does a script with
    and without its exec bit."""
    out = []
    for make in ('link', 'file', 'exec'):
        root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
        write(os.path.join(root, 'core', 'ffi', 'shim.c'), 'int x;\n'); os.makedirs(os.path.join(root, 'app'))
        if make == 'link': os.symlink('../core/ffi/shim.c', os.path.join(root, 'app', 'shim.c'))
        else:
            with open(os.path.join(root, 'app', 'shim.c'), 'wb') as f: f.write(b'symlink\0../core/ffi/shim.c')
            if make == 'exec': os.chmod(os.path.join(root, 'app', 'shim.c'), 0o755)
        out.append(run('good', tree=(root, manifest))['build_digest'])
    return len(set(out)) == 3


check('the build digest is the sha256 of typed entries: [path, "file", mode, sha256] and [path, "link", target]',
      attempt(entries_digest) is True)
check('a symlink, a file holding the same bytes, and that file executable give three digests', attempt(link_or_file) is True)


def total_cap(slack):
    """analyze with the cap on the bytes hashed set to the good tree's inputs plus `slack`."""
    tree = source_tree('good', [('x', 'Good.t1', 'model')])
    total = sum(os.path.getsize(os.path.join(d, f)) for d, _, fs in os.walk(os.path.join(tree[0], 'core')) for f in fs)
    total += os.path.getsize(os.path.join(tree[0], '.verificationalliance.json'))
    saved = va.MAX_TOTAL
    va.MAX_TOTAL = total + slack
    try:
        if slack < 0:
            return analysis_error(lambda: run('good', tree=tree))
        return is_sha256(run('good', tree=tree)['build_digest'])
    finally:
        va.MAX_TOTAL = saved


check('build inputs over 512 MiB in total raise', attempt(lambda: va.MAX_TOTAL) == 512 * 1024 * 1024
      and attempt(lambda: total_cap(0)) is True and '512 MiB' in (attempt(lambda: total_cap(-1)) or ''))

OUTSIDE = fresh('outside')
write(os.path.join(OUTSIDE, 'A.lean'), BIG)
SYMLINKS = 'symlinks are not supported in v1: '


def with_symlink(rel, target):
    """The AnalysisError message after making `rel` a symlink to `target` in a new good tree."""
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    path = os.path.join(root, rel)
    if os.path.lexists(path):
        os.remove(path)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    os.symlink(target, path)
    return analysis_error(lambda: run('good', tree=(root, manifest)))


A_LEAN = os.path.join(OUTSIDE, 'A.lean')
check('a symlinked lean file raises', with_symlink('core/A.lean', A_LEAN) == SYMLINKS + 'core/A.lean')
check('a symlink to a lean file in the checkout raises', with_symlink('core/B.lean', 'Good.lean')
      == SYMLINKS + 'core/B.lean')
check('a dangling symlinked lean file raises',
      with_symlink('core/D.lean', A_LEAN + '.gone') == SYMLINKS + 'core/D.lean')
check('a symlinked lean file outside the project raises', with_symlink('src/X.lean', A_LEAN) == SYMLINKS + 'src/X.lean')
check('a symlinked folder raises', with_symlink('core/Ab', OUTSIDE) == SYMLINKS + 'core/Ab')
check('a symlinked folder outside the project, pointing outside the checkout, raises',
      with_symlink('src', OUTSIDE) == 'a symlink points outside the repository: src')
check('a symlinked lake file raises', with_symlink('core/lean-toolchain', A_LEAN) == SYMLINKS + 'core/lean-toolchain')
check('a symlinked manifest file raises',
      with_symlink('.verificationalliance.json', A_LEAN) == SYMLINKS + '.verificationalliance.json')


def inside_symlink():
    """Outside the project, a symlink into the checkout counts by where it points, and is never followed (as
    OSVA Monitor's app/Sources/OSVACore/osva_shim.c -> ../../../core/ffi/osva_shim.c)."""
    tree = source_tree('good', [('x', 'Good.t1', 'model')])
    root = tree[0]
    out = [run('good', tree=tree)['build_digest']]
    write(os.path.join(root, 'core', 'ffi', 'shim.c'), 'int x;\n'); write(os.path.join(root, 'core', 'ffi', 'other.c'), 'int y;\n')
    os.makedirs(os.path.join(root, 'app', 'src'))
    os.symlink('../../core/ffi/shim.c', os.path.join(root, 'app', 'src', 'shim.c'))
    out.append(run('good', tree=tree)['build_digest'])
    os.remove(os.path.join(root, 'app', 'src', 'shim.c')); os.symlink('../../core/ffi/other.c', os.path.join(root, 'app', 'src', 'shim.c'))
    out.append(run('good', tree=tree)['build_digest'])
    return len(set(out)) == 3


check('a symlink outside the project to a file in the checkout counts by its target, never followed', attempt(inside_symlink) is True)


def escape(links, files=(), rel=None):
    """analyze's AnalysisError on a good tree with these symlinks (path -> target) and files added; with `rel`, only
    _link's for that one symlink, checked alone, so each rule is seen without the others."""
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    for f in files: write(os.path.join(root, f), 'int x;\n')
    os.makedirs(os.path.join(root, '.git'), exist_ok=True); write(os.path.join(root, '.git', 'config'), '[core]\n')
    for path, target in links:
        os.makedirs(os.path.dirname(os.path.join(root, path)) or root, exist_ok=True)
        os.symlink(target, os.path.join(root, path))
    if rel is not None:
        return analysis_error(lambda: va._link(root, rel, os.path.join(root, rel), 'core'))
    return analysis_error(lambda: run('good', tree=(root, manifest)))


def fifo_link():
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    os.makedirs(os.path.join(root, 'app')); os.mkfifo(os.path.join(root, 'core', 'pipe'))
    os.symlink('../core/pipe', os.path.join(root, 'app', 'f'))
    return analysis_error(lambda: va._link(root, 'app/f', os.path.join(root, 'app', 'f'), 'core'))


SHIM = 'app/Sources/OSVACore/osva_shim.c'
UP = ('up', '.')
ESCAPE = (SHIM, '../../../up/../core/ffi/osva_shim.c')       # reads as core/ffi/osva_shim.c; is ../core/ffi/osva_shim.c
check("OSVA Monitor's one symlink, a file in the checkout by its real path, passes",
      escape([(SHIM, '../../../core/ffi/osva_shim.c')], files=['core/ffi/osva_shim.c']) is None)
check('a folder symlink outside the project raises (up -> .)', escape([UP]) == 'a symlink to a folder: up')
check('a symlink whose real path leaves the checkout through a folder symlink raises, though its text reads inside',
      escape([UP, ESCAPE], files=['core/ffi/osva_shim.c'], rel=SHIM) == 'a symlink points outside the repository: ' + SHIM
      and escape([UP, ESCAPE], files=['core/ffi/osva_shim.c']) is not None)
check('a symlink into .git through a folder symlink raises (app/g -> up/.git/config)',
      escape([UP, ('app/g', '../up/.git/config')], rel='app/g') == 'a symlink points into .git: app/g'
      and escape([('app/g', '../.git/config')]) == 'a symlink points into .git: app/g')
check('a dangling symlink raises', escape([('app/d', 'missing.c')]) == 'a symlink points at nothing: app/d')
check('a symlink whose real path is in the checkout but not where its text reads raises (through up -> .)',
      escape([UP, ('app/s.c', '../up/core/ffi/osva_shim.c')], files=['core/ffi/osva_shim.c'], rel='app/s.c')
      == 'a symlink points outside the repository: app/s.c')
check('a symlink to a fifo raises', (lambda r: r if r is None else r)(attempt(lambda: fifo_link())) == 'a symlink to something that is not a regular file: app/f')
check('a symlink to a folder in the checkout raises', escape([('app/ffi', '../core')]) == 'a symlink to a folder: app/ffi')
check('a symlink outside the project pointing outside the checkout raises',
      with_symlink('README.md', A_LEAN) == 'a symlink points outside the repository: README.md'
      and with_symlink('docs/x', '../../x') == 'a symlink points outside the repository: docs/x'
      and with_symlink('docs/y', '/etc/passwd') == 'a symlink points outside the repository: docs/y')


def symlinked_project():
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    os.rename(os.path.join(root, 'core'), os.path.join(OUTSIDE, 'core'))
    os.symlink(os.path.join(OUTSIDE, 'core'), os.path.join(root, 'core'))
    return run('good', tree=(root, manifest))


check('a symlinked project folder raises', analysis_error(symlinked_project) == SYMLINKS + 'core')
check('analyze takes manifest_path, with no default',
      attempt(lambda: __import__('inspect').signature(va.analyze).parameters['manifest_path'].default)
      is __import__('inspect').Parameter.empty)
check("analyze takes the sanity helper's verdicts last, with no default",
      attempt(lambda: [(n, p.default) for n, p in __import__('inspect').signature(va.analyze).parameters.items()][-1])
      == ('verdicts', __import__('inspect').Parameter.empty))
check("analyze: each claim has its warnings, from the helper's verdicts, and a null template",
      attempt(lambda: [(c['warnings'], c['template']) for c in run(
          'good', ['Good.t1', 'Good.pick_lowest'], verdicts='0 0 any\n1 0 any\n1 1 needed\n')['claims']])
      == [([{'check': 'holds-for-any', 'name': 'Good.f', 'arg': None}], None),
          ([{'check': 'holds-for-any', 'name': 'Good.lowest', 'arg': None}], None)])
check("analyze: verdicts that cannot be read are rejected, naming them",
      "the sanity helper's verdicts cannot be read" in (
          analysis_error(lambda: run('good', ['Good.t1'], verdicts='0 0 any\n0 1 any\n')) or ''))
check('statement binders: the names nanoda_bin prints before the statement\'s colon, in order, None for none',
      [attempt(lambda t=t: va._statement_binders(t)) for t in (
          'theorem Weak.add_zero_of_valid (n : Nat) (h : Weak.Valid n) : Eq (HAdd.hAdd n (OfNat.ofNat 0)) n',
          'theorem Printed.t5 : forall {α : Type 0} (xs : List α), Ne xs List.nil → Eq (List.length xs) (List.length xs)',
          'theorem «Good.key never leaves» (n : Nat) : LT.lt n (Good.f n)',
          'theorem Weak.vacuous (n : Nat) (h₁ : LT.lt n (OfNat.ofNat 2)) (h₂ : GT.gt n (OfNat.ofNat 5)) :\n  Eq n n',
          'theorem T.x {α : Type 0} [inst : Inhabited α] [Inhabited Nat] (a b : α) ⦃«my c» : α⦄ :\n  P a',
          'theorem Printed.B (h : Printed.V (OfNat.ofNat 1)) :\n  forall {y : Nat}, Printed.V (OfNat.ofNat 2) → P')]
      == [('n', 'h'), (), ('n',), ('n', 'h₁', 'h₂'), ('α', 'inst', None, 'a', 'b', '«my c»'), ('h',)])
check('statement binders: none when where they end is not certain',
      [attempt(lambda t=t: va._statement_binders(t)) for t in (
          'theorem T.s (h : Eq "a : b" "a") : True', 'theorem T.u (h : P :\n  Q', 'theorem T.v (h : P)) : Q',
          'theorem T.w h : P', 'def T.d (h : P) : Prop', 'theorem T.e (h : P)', 'theorem T.m (h : P] : Q')]
      == [()] * 7)


def weak_pp(statement):
    """A printer that prints Weak.add_zero_of_valid as statement."""
    return lambda names: {n: statement if n == 'Weak.add_zero_of_valid' else '<pp %s>' % n for n in names}


check('analyze: an unused assumption is named only when the statement prints its name before its colon, '
      'in its place',
      [attempt(lambda t=t: run('weak', ['Weak.add_zero_of_valid'], export=W, pp=weak_pp(t))['claims'][0]['warnings'])
       for t in ('theorem Weak.add_zero_of_valid (n : Nat) (h : Weak.Valid n) : Eq (HAdd.hAdd n (OfNat.ofNat 0)) n',
                 'theorem Weak.add_zero_of_valid : forall (n : Nat), Weak.Valid n → Eq (HAdd.hAdd n (OfNat.ofNat 0)) n',
                 'theorem Weak.add_zero_of_valid (h : Nat) : forall (n : Weak.Valid h), Eq h h')]
      == [[{'check': 'unused-assumption', 'name': 'h', 'arg': None}]]
      + [[{'check': 'unused-assumption', 'name': None, 'arg': None}]] * 2)


def manifest_elsewhere():
    """The digest hashes the manifest file at manifest_path, and not a file at the default path."""
    tree = source_tree('good', [('x', 'Good.t1', 'model')])
    root = tree[0]
    os.makedirs(os.path.join(root, 'cfg'))
    os.rename(os.path.join(root, '.verificationalliance.json'), os.path.join(root, 'cfg', 'm.json'))
    out = [run('good', tree=tree, manifest_path='cfg/m.json')['build_digest']]
    append('cfg/m.json')(root)
    out.append(run('good', tree=tree, manifest_path='cfg/m.json')['build_digest'])
    write(os.path.join(root, '.verificationalliance.json'), '{}')
    out.append(run('good', tree=tree, manifest_path='cfg/m.json')['build_digest'])
    return out[0] != out[1] != out[2] != out[0]


check('build digest hashes the manifest file it is given, and a file at the default path like any other',
      attempt(manifest_elsewhere) is True)
check('a manifest path outside the checkout rejected',
      analysis_error(lambda: run('good', ['Good.t1'], manifest_path='../m.json')) is not None)


def no_source():
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    os.remove(os.path.join(root, 'core', 'Good.lean'))
    return run('good', tree=(root, manifest))


nosrc = attempt(no_source) or {}
check('source null when no file has the theorem', valid(nosrc) and nosrc['claims'][0]['source'] is None)


def no_manifest_file():
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    os.remove(os.path.join(root, '.verificationalliance.json'))
    return run('good', tree=(root, manifest))


check('a missing manifest file rejected', analysis_error(no_manifest_file) is not None)
check('a printer that leaves out a name rejected',
      analysis_error(lambda: run('good', ['Good.t1'], pp=lambda names: {})) is not None)
check('an invalid result raises AnalysisError',
      analysis_error(lambda: run('good', ['Good.t1'], repo='x/y')) is not None)
dangling = attempt(lambda: vx.load_export(export_file(
    [META, NAME_X, '{"in":2,"str":{"pre":0,"str":"t"}}', SORT, '{"ie":1,"const":{"name":1,"us":[]}}',
     '{"thm":{"name":2,"levelParams":[],"type":1,"value":1,"all":[2]}}'])))
check('an export error raises AnalysisError',
      analysis_error(lambda: run('good', ['t'], export=dangling, ref=dangling)) is not None)

# vacheck 1.1.0. What a report cannot show is rejected with a message naming where it is, so a
# result analyze writes is one the server accepts.
def hidden_in(**kw):
    claims = kw.pop('claims', [('x', 'Good.t1', 'model')])
    return analysis_error(lambda: run('good', tree=source_tree('good', claims, **kw), **kw.pop('run', {})))


def with_pp(extra):
    """A printer that adds `extra` to every text it prints."""
    return lambda names: {n: '<pp %s>%s' % (n, extra) for n in names}


check('a zero-width character in what a claim says rejected, by its code point',
      'what the claim on Good.t1 says holds the character U+200B' in (hidden_in(claims=[('a​b', 'Good.t1', 'model')]) or ''))
check('a line separator in a theorem name rejected',
      'the theorem name Good.' in (analysis_error(lambda: run('good', ['Good.«a b»'])) or '')
      and 'U+2028' in (analysis_error(lambda: run('good', ['Good.«a b»'])) or ''))
check('a zero-width character in a statement rejected',
      'the statement of Good.t1 holds the character U+200B'
      in (analysis_error(lambda: run('good', ['Good.t1'], pp=with_pp('​'))) or ''))
check('a tab in a definition text rejected',
      'the text of Good.f holds the character U+0009'
      in (analysis_error(lambda: run('good', ['Good.t1'], pp=lambda names: {
          n: '<pp %s>' % n + ('\t' if n == 'Good.f' else '') for n in names})) or ''))
check('line breaks kept in statements and definition texts',
      [(c['statement'], c['defs'][0]['text']) for c in (attempt(lambda: run('good', ['Good.t1'], pp=with_pp('\n  x')))
                                                       or {}).get('claims', [])]
      == [('<pp Good.t1>\n  x', '<pp Good.f>\n  x')])
check('a zero-width character in the project folder rejected',
      'the project folder' in (hidden_in(project='co​re') or ''))
check('a zero-width character in a shipped target rejected',
      'the shipped target' in (hidden_in(ships=['«G​ood»']) or ''))
check('a zero-width character in a file name rejected',
      'is not plain text' in (analysis_error(lambda: with_file('core/A​.lean', 'def a := 1\n')) or ''))
check('a replaced line is shown with tabs as spaces and without hidden characters',
      (attempt(lambda: with_file('core/M.lean', '\t@[extern "x​y"]\topaque y : Nat\n')) or {})
      .get('evidence', {}).get('replaced') == [{'path': 'core/M.lean', 'line': 1, 'text': '@[extern "xy"] opaque y : Nat'}])

# Steps 6 and 7 read no file in a folder named .lake or .git, at any depth: there are Lake's builds
# and packages, and git's objects. Step 8 still hashes them. Both files sort before core/Good.lean.
UNREAD_TEXT = 'namespace Good\ntheorem t1 : True := trivial\n@[extern "x"] opaque y : Nat\n'


def unread_folders():
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    before = run('good', tree=(root, manifest))
    for rel in ('core/.git/B.lean', 'core/A/.lake/C.lean'):  # core/.lake itself is rejected
        write(os.path.join(root, rel), UNREAD_TEXT)
    after = run('good', tree=(root, manifest))
    return (after['claims'][0]['source'], after['evidence']['replaced'],
            before['build_digest'] != after['build_digest'])


check('no text read in .lake or .git folders at any depth, which are still hashed',
      attempt(unread_folders) == ({'path': 'core/Good.lean', 'line': 5}, [], True))
check('the same files outside those folders are read',
      (lambda r: r is not None and r['claims'][0]['source'] is None
       and len(r['evidence']['replaced']) == 1)(attempt(lambda: with_file('core/A/C.lean', UNREAD_TEXT))))

# More than one reference: one per library of the toolchain. A name is the library's when any of
# them declares it, and must then be identical to every one that does.
check('two references that agree accepted',
      valid(attempt(lambda: run('good', ['Good.t1'], ref=[refs['good'], refs['good']])) or {}))
check('a second reference whose Eq differs rejects',
      rejected_with('good', ['Good.t1'], "Eq differs from the toolchain's Eq", ref=[refs['good'], envs['fakeeq']]))
check('a name only the second reference declares is compared',
      rejected_with('good', ['Good.«key never leaves»'], 'Nat.lt',
                    ref=attempt(lambda: [reference('good', 'Good', drop={'Nat.lt'}),
                                         reference('good', 'Good', change=other_nat_lt)])))

# The toolchain libraries a project imports, read from its .lean files as text: the workflow
# compares the names of a library beyond Init, Std, Lean and Lake only if the project imports it.
def roots_of(files, project='core'):
    root = fresh('imports')
    for rel, text in files.items():
        write(os.path.join(root, rel), text)
    return va.import_roots(root, project)


check('import roots: plain, dotted, with modifiers, in «», after a comment, across a line break',
      attempt(lambda: roots_of({
          'core/A.lean': 'module\nimport Lean.Data.Json\npublic meta import all «LeanExport».Parse\n'
                         '/- doc -/ import LeanChecker\n  import Good\n',
          'core/sub/B.lean': 'private import\n  LeanIR\n'}))
      == ['Good', 'Lean', 'LeanChecker', 'LeanExport', 'LeanIR'])
check('import roots: a comment line and an import later on a line are not imports',
      attempt(lambda: roots_of({'core/A.lean': '-- import LeanChecker\ndef x := 1 -- import LeanIR\nimported Leanc\n'})) == [])
check('import roots: only the project, never .lake or .git, never a file over 2 MiB',
      attempt(lambda: roots_of({'core/A.lean': 'import Std\n', 'other/B.lean': 'import LeanChecker\n',
                                'core/x/.lake/C.lean': 'import LeanIR\n', 'core/x/.git/D.lean': 'import Leanc\n',
                                'core/Big.lean': 'import LakeMain\n' + ' ' * (2 * 1024 * 1024)})) == ['Std'])
check('import roots: a line that only looks like an import still counts, so more is compared',
      attempt(lambda: roots_of({'core/A.lean': '/-\nimport LeanChecker\n-/\n'})) == ['LeanChecker'])


def symlinked_import():
    root = fresh('imports')
    write(os.path.join(root, 'core', 'A.lean'), 'import Std\n')
    os.symlink(os.path.join(root, 'core', 'A.lean'), os.path.join(root, 'core', 'L.lean'))
    return va.import_roots(root, 'core')


check('import roots: a symlinked .lean file raises', analysis_error(symlinked_import) == SYMLINKS + 'core/L.lean')

# vacheck 1.1.2. A claim's source is where the source declares that theorem by its full name, from
# the namespaces open around it, and so is a definition's; none when no declaration or more than one
# has the name. Comments, strings and character literals do not count.
def source_of(files, names=('Good.t1',)):
    """The sources analyze gives the claim on each of `names` (with the good tree's Good.lean
    replaced by files['core/Good.lean'] when given) and of Good.f, its definition."""
    root, manifest = source_tree('good', [('x', n, 'model') for n in names])
    for rel, text in files.items():
        write(os.path.join(root, rel), text)
    r = run('good', tree=(root, manifest))
    return [c['source'] for c in r['claims']] + [d['source'] for d in r['claims'][0]['defs']]


def at(path, line):
    return {'path': path, 'line': line}


GOOD_SRC = at('core/Good.lean', 5), at('core/Good.lean', 3)
check('a theorem of the same last name in another namespace is not the claim\'s source',
      attempt(lambda: source_of({'core/A.lean': 'namespace Bad\ntheorem t1 : True := trivial\ndef f := 1\nend Bad\n'}))
      == list(GOOD_SRC))
check('nor one at the top level, nor in a namespace whose name ends the same',
      attempt(lambda: source_of({'core/A.lean': 'theorem t1 : True := trivial\nnamespace NotGood\ntheorem t1 : True := trivial\n'
                                                 'end NotGood\ntheorem Bad.Good.t1 : True := trivial\n'})) == list(GOOD_SRC))
check('a second declaration with the full name makes the source null',
      attempt(lambda: source_of({'core/A.lean': 'namespace Good\ntheorem t1 : True := trivial\nend Good\n'})) == [None, GOOD_SRC[1]])
check('the full name from nested namespaces, a dotted namespace, a dotted declaration and _root_',
      attempt(lambda: source_of({'core/Good.lean': 'namespace X\nnamespace Y.Z\ntheorem _root_.Good.t1 : True := trivial\nend Y.Z\n'
                                                     'end X\nnamespace «Good»\ndef «f» := 1\nend Good\n'})) == [at('core/Good.lean', 3), at('core/Good.lean', 7)])
check('a section, a noncomputable section and mutual add nothing to the name',
      attempt(lambda: source_of({'core/Good.lean': 'namespace Good\nsection S\nnoncomputable section\nmutual\n'
                                                     'theorem t1 : True := trivial\nend\nend\nend S\n@[simp] protected def f := 1\nend Good\n'}))
      == [at('core/Good.lean', 5), at('core/Good.lean', 9)])
check('a declaration in a comment, a nested comment, a docstring, a string or after a char literal does not count',
      attempt(lambda: source_of({'core/A.lean': '-- namespace Good\n/- /- -/\nnamespace Good\ntheorem t1 -/\n/-- doc\n'
                                                 'namespace Good\ntheorem t1 : True := trivial -/\ndef s := "\nnamespace Good\ntheorem t1 : True\n"\n'
                                                 "def c := '\"'\ndef r := r#\"\nnamespace Good\ntheorem t1\"#\n"})) == list(GOOD_SRC))
check('a private declaration of the name is not its source (Lean gives it another name)',
      attempt(lambda: source_of({'core/A.lean': 'namespace Good\nprivate theorem t1 : True := trivial\nend Good\n'})) == list(GOOD_SRC))
check('after an end that closes what is not open, nothing more in that file is a source',
      attempt(lambda: source_of({'core/A.lean': 'namespace Bad\nend Worse\nnamespace Good\ntheorem t1 : True := trivial\nend Good\n'}))
      == list(GOOD_SRC))
check('#exit anywhere outside comments and strings ends the file; so does a « with no » on its line',
      [attempt(lambda t=t: va.declarations(t)) for t in (
          'namespace OSVA\nmake_theorem t\nend OSVA #exit\ntheorem OSVA.t : True := trivial\n',
          'example : True := trivial #exit\ntheorem t : True := trivial\n',
          'theorem a : True := trivial\ndef x := «oops\ntheorem t : True := trivial\n',
          'def s := "#exit" -- #exit\ntheorem t : True := trivial\ndef x#exit := 1\ntheorem u : True := trivial\n')]
      == [[], [], [(('a',), 1), (('x',), 2)], [(('s',), 1), (('t',), 2), (('x',), 3)]])
check('#exit at the start of a line ends the file: a decoy after it is no source',
      attempt(lambda: source_of({'core/Good.lean': 'namespace Good\nmy_theorem_macro t1\ndef f := 1\n#exit\ntheorem t1 : True := trivial\n'
                                                     'def g := 2\nend Good\n'})) == [None, at('core/Good.lean', 3)]
      and attempt(lambda: va.declarations('namespace OSVA\nmake_theorem t\n#exit\ntheorem OSVA.t : True := trivial\n')) == []
      and attempt(lambda: va.declarations('-- #exit\n/- \n#exit -/\ndef s := "\n#exit"\ntheorem t : True := trivial\n  #exitx\ntheorem u : True := trivial\n'))
      == [(('s',), 4), (('t',), 6)]
      and attempt(lambda: va.declarations('theorem a : True := trivial\n  #exit\ntheorem b : True := trivial\n')) == [(('a',), 1)])
check('a theorem with universe parameters, t1.{u}, has its source',
      attempt(lambda: source_of({'core/Good.lean': 'namespace Good\ntheorem t1.{u} : True := trivial\ndef f := 1\nend Good\n'}))
      == [at('core/Good.lean', 2), at('core/Good.lean', 3)])
check('a «» name in the manifest matches the source as Lean reads it',
      attempt(lambda: source_of({}, names=('Good.«key never leaves»', 'Good.«t1»'))) == [at('core/Good.lean', 7), GOOD_SRC[0], GOOD_SRC[1]])
def hostile_scan():
    """The slowest of the hostile files, each of 2 MiB, takes under 5 seconds (all take under 1 s here)."""
    import time
    worst = 0
    for text in ('«' * MB2, '/-' * (MB2 // 2), '/- ' * (MB2 // 3), '"' * MB2, 'r#"' * (MB2 // 3), "'" * MB2,
                 'namespace A\n' * (MB2 // 12)):
        start = time.monotonic()
        va.declarations(text)
        worst = max(worst, time.monotonic() - start)
    return worst < 5


check('hostile source text is scanned in linear time', attempt(hostile_scan) is True)

check('components: «» kept whole, a bad name refused',
      [attempt(lambda n=n: va.components(n)) for n in ('A.«b.c».d', 'A..b', 'A.', '«a', 'a«b»')]
      == [('A', 'b.c', 'd'), None, None, None, None])

# vacheck 1.1.2. Definitions are shown as nanoda_bin prints them from the checked export, made
# readable: an inductive type with its constructors, a definition compiled through a recursor or a
# match by its header, and names with macro scopes as Lean shows them.
NANO = {
    'Good.f': 'def Good.f (n : Nat) : Nat := HAdd.hAdd n (OfNat.ofNat 1)',
    'Good.Range': 'inductive Good.Range : Type 0',
    'Good.Range.mk': 'constructor Good.Range.mk : Nat → Nat → Good.Range',
    'Good.anyIn': 'def Good.anyIn (rs : List Good.Range) (x._@.Init.Prelude.1._hygCtx._hyg.10 : Nat) : Bool :=\n  List.any rs\n'
                  '    (fun (x._@.Good.2._hygCtx._hyg.9 : Good.Range) =>\n    Good.Range.contains x._@.Good.2._hygCtx._hyg.9 '
                  'x._@.Init.Prelude.1._hygCtx._hyg.10)',
    'Good.lowest': 'def Good.lowest (a._@._internal._hyg.0 : List Nat) : Nat := List.brecOn a._@._internal._hyg.0 Good.lowest._f',
    'Good.pick': 'def Good.pick (o : Option Nat) : Nat :=\n  Good.pick.match_1 (fun (o._@.Good.3._hygCtx._hyg.8 : Option Nat) => Nat) o\n'
                 '    (fun (_ : Unit) => OfNat.ofNat 0) (fun (n : Nat) => n)',
}


def nano(over=None):
    """A printer that prints as nanoda_bin does, with `over` in place of some of its texts."""
    table = dict(NANO, **(over or {}))
    return lambda names: {n: table.get(n, 'theorem %s : True' % n) for n in names}


def shown(over=None, claims=('Good.anyIn_nil', 'Good.pick_lowest')):
    r = run('good', claims, pp=nano(over))
    return {d['name']: d['text'] for c in r['claims'] for d in c['defs']}


def terms(over=None, claims=('Good.anyIn_nil', 'Good.pick_lowest')):
    r = run('good', claims, pp=nano(over))
    return {d['name']: d['term'] for c in r['claims'] for d in c['defs']}


sh = attempt(shown) or {}
check('a structure is shown with its constructor and the fields, named, of the checked export',
      sh.get('Good.Range') == 'inductive Good.Range : Type 0\nconstructor:\n  Good.Range.mk (lo hi : Nat) : Good.Range')
check('the constructor printer is asked for, and only for inductive types',
      attempt(lambda: (lambda seen: (run('good', ['Good.anyIn_nil', 'Good.t1'], pp=lambda n: seen.extend(n) or nano()(n)), seen)[1])([]))
      == ['Good.anyIn_nil', 'Good.t1', 'Good.Range', 'Good.anyIn', 'Good.f', 'Good.Range.mk'])
check('a definition through structural recursion is shown by its header',
      sh.get('Good.lowest') == 'def Good.lowest (a✝ : List Nat) : Nat\n  ' + va.COMPILED_NOTE
      and va.COMPILED_NOTE == '(body compiled; the checked term is below)')
check('a definition through a match is shown by its header',
      sh.get('Good.pick') == 'def Good.pick (o : Option Nat) : Nat\n  ' + va.COMPILED_NOTE)
check('a definition compiled through nothing is shown whole, its macro-scoped names as Lean shows them',
      sh.get('Good.anyIn') == 'def Good.anyIn (rs : List Good.Range) (x✝ : Nat) : Bool :=\n  List.any rs\n'
      '    (fun (x✝¹ : Good.Range) =>\n    Good.Range.contains x✝¹ x✝)')
check('Good.f is shown whole', (attempt(lambda: run('good', ['Good.t1'], pp=nano())) or {}).get('claims', [{}])[0].get('defs')
      == [{'name': 'Good.f', 'text': NANO['Good.f'], 'source': at('core/Good.lean', 3), 'term': None}])
for why, text in (('a string in it', 'def Good.lowest (s : Foo ":= x") : Nat := List.brecOn s Good.lowest._f'),
                  ('a string with := in it, outside brackets', 'def Good.lowest : Foo "x := y" := List.brecOn s Good.lowest._f'),
                  ('a let in it', 'def Good.lowest (a : let n : Nat := 3; Fin n) : Nat := List.brecOn a Good.lowest._f'),
                  ('a let outside brackets', 'def Good.lowest : let n : Nat := 3; Fin n := List.brecOn a Good.lowest._f'),
                  (':= in a «» name', 'def Good.lowest (a : «A := b») : Nat := List.brecOn a Good.lowest._f'),
                  ('no :=', 'def Good.lowest : Nat')):
    check('a compiled definition with %s in its header is shown whole' % why,
          (attempt(lambda: shown({'Good.lowest': text})) or {}).get('Good.lowest') == va._hygiene(text))
for why, text in (('an extra arrow', 'constructor Good.Range.mk : Nat → (Nat → Nat) → Nat → Good.Range'),
                  ('a forall', 'constructor Good.Range.mk : forall (n : Nat), Nat → Good.Range'),
                  ('binders before the colon', 'constructor Good.Range.mk (lo : Nat) : Nat → Good.Range'),
                  ('a string', 'constructor Good.Range.mk : Foo "→" → Nat → Good.Range'),
                  ('unbalanced brackets', 'constructor Good.Range.mk : (Nat → Nat → Good.Range')):
    check('a constructor printed with %s is shown as nanoda_bin printed it' % why,
          (attempt(lambda: shown({'Good.Range.mk': text})) or {}).get('Good.Range')
          == 'inductive Good.Range : Type 0\nconstructor:\n  ' + text[len('constructor '):])
check('a field of a function type is kept in its brackets, and a long constructor broken per field',
      (attempt(lambda: shown({'Good.Range.mk': 'constructor Good.Range.mk : (Nat → Nat) → List (Option (Prod Nat Nat)) '
                                                 '→\n    Good.Range'})) or {}).get('Good.Range')
      == 'inductive Good.Range : Type 0\nconstructor:\n  Good.Range.mk (lo : Nat → Nat) (hi : List (Option (Prod Nat Nat))) : Good.Range'
      and (attempt(lambda: shown({'Good.Range.mk': 'constructor Good.Range.mk : %s → %s → Good.Range' % ('A' * 50, 'B' * 50)}))
           or {}).get('Good.Range')
      == 'inductive Good.Range : Type 0\nconstructor:\n  Good.Range.mk\n    (lo : %s)\n    (hi : %s) : Good.Range' % ('A' * 50, 'B' * 50))

check('fields: names, binder info and whether a later binder depends on each, after the parameters',
      [attempt(lambda n=n: vx.fields(good, n)) for n in ('Good.Range.mk', 'Exists.intro', 'Nat.le.step')]
      == [[('lo', 'default', False), ('hi', 'default', False)], [('w', 'default', True), ('h', 'default', False)],
          [('m', 'implicit', True), (None, 'default', False)]]
      and attempt(lambda: vx.parameters(good, 'Exists.intro')) == 2)
check('a constructor without parameters is shown with its fields, one with parameters as nanoda_bin printed it',
      [attempt(lambda n=n, t=t: va._constructor(good, n, t)) for n, t in (
          ('Nat.succ', 'constructor Nat.succ : Nat → Nat'),
          ('Option.some', 'constructor Option.some.{u} {α : Type u} : α → Option α'),
          ('Option.some', 'constructor Option.some : α → Option α'),
          ('Exists.intro', 'constructor Exists.intro.{u} {α : Sort u} {p : α → Prop} (w : α) : p w → Exists p'))]
      == ['Nat.succ (n : Nat) : Nat', 'Option.some.{u} {α : Type u} : α → Option α', 'Option.some : α → Option α',
          'Exists.intro.{u} {α : Sort u} {p : α → Prop} (w : α) : p w → Exists p'])
tm = attempt(terms) or {}
check('a compiled definition carries its checked term in full, names shown as Lean shows them; others none',
      tm.get('Good.lowest') == va._hygiene(NANO['Good.lowest']) and tm.get('Good.pick') == va._hygiene(NANO['Good.pick'])
      and tm.get('Good.anyIn') is None and tm.get('Good.Range') is None and 'Good.lowest' in tm)
long_body = NANO['Good.lowest'] + ' ' + 'x' * 5000


def long_term():
    return terms({'Good.lowest': long_body})['Good.lowest']


lt = attempt(long_term) or ''
check('a checked term over 4,000 characters is cut there, saying how many characters are left out',
      len(lt) == 4000 and lt.startswith(va._hygiene(long_body)[:200]) and re.search(r'\n\u2026 (\d+) more characters$', lt) is not None
      and int(re.search(r'(\d+) more characters$', lt).group(1)) == len(va._hygiene(long_body)) - len(lt.rsplit('\n', 1)[0]))
check('the statement of a theorem has no term', all('term' not in c for c in (attempt(lambda: run('good', ['Good.t1'])) or {}).get('claims', [{}])))


def many_constructors():
    printed = dict(NANO, **{'Good.Range.mk': 'constructor Good.Range.mk : ' + 'Nat → ' * 30 + 'Good.Range'})
    text, term = va._definition(good, 'Good.Range', printed, {'Good.Range': ['Good.Range.mk'] * 100})
    assert term is None
    return len(text) <= 4000, text.endswith('\n  … and %d more' % (100 - text.count('\n  Good.Range.mk'))), text.count('\n  Good.Range.mk')


check('an inductive type of many constructors is cut at 4,000 characters, saying how many are left out',
      (lambda r: r is not None and r[0] and r[1] and 10 < r[2] < 100)(attempt(many_constructors)))


def compiled_through(*consts):
    """Good.f shown as if its value mentioned exactly these constants."""
    saved = va.value_constants
    va.value_constants = lambda env, name: frozenset(consts)
    try:
        text, term = va._definition(good, 'Good.f', {'Good.f': 'def Good.f :\n  Nat → Nat :=\n  Nat.succ _'}, {})
        assert term == (None if text == 'def Good.f :\n  Nat → Nat :=\n  Nat.succ _' else 'def Good.f :\n  Nat → Nat :=\n  Nat.succ _')
        return text
    finally:
        va.value_constants = saved


check('a definition through well-founded recursion is shown by its header, on one line when it fits',
      attempt(lambda: compiled_through('WellFounded.fix', 'Nat')) == 'def Good.f : Nat → Nat\n  ' + va.COMPILED_NOTE)
check('each auxiliary of compiled recursion and match counts on its own; other constants do not',
      [attempt(lambda c=c: compiled_through(c)).endswith(va.COMPILED_NOTE) for c in (
          'List.brecOn', 'List.binductionOn', 'List.below', 'Nat.rec', 'Nat.recOn', 'Option.casesOn', 'Good.pick.match_1',
          'Good.lowest._f', 'Good.g._unary', 'Good.g._mutual', 'WellFounded.fixF', 'List.any', 'Good.recorder', 'Good.match_x',
          'Good.my_f')]
      == [True] * 11 + [False] * 4)


def with_fields(fs):
    saved = va.fields
    va.fields = lambda env, ctor, budget=None: fs
    try:
        return va._constructor(good, 'Good.Range.mk', NANO['Good.Range.mk'])
    finally:
        va.fields = saved


check('a constructor whose fields the export says are dependent, implicit or unnamed is shown as printed',
      [attempt(lambda fs=fs: with_fields(fs)) for fs in (
          [('lo', 'default', True), ('hi', 'default', False)], [('lo', 'implicit', False), ('hi', 'default', False)],
          [(None, 'default', False), ('hi', 'default', False)], None)]
      == ['Good.Range.mk : Nat → Nat → Good.Range'] * 4
      and attempt(lambda: with_fields([('lo', 'default', False), ('hi', 'default', False)])) == 'Good.Range.mk (lo hi : Nat) : Good.Range')


def walk_fields(env, ctor):
    """What fields gives, but each field's dependence found by a walk of its own through the rest of the
    constructor's type, at every depth: [(binder info, dependent)], or None."""
    d = env._decls[env._decl(ctor)]
    e, out = d.fields['type'], []
    for i in range(d.fields['numParams'] + d.fields['numFields']):
        node = env._exprs[e]
        if node[0] != 'forallE':
            return None
        if i >= d.fields['numParams']:
            stack, seen, dep = [(node[3], 0)], set(), False
            while stack and not dep:
                x, k = stack.pop()
                if (x, k) in seen:
                    continue
                seen.add((x, k))
                n = env._exprs[x]
                if n[0] == 'bvar':
                    dep = n[1] == k
                elif n[0] in ('lam', 'forallE'):
                    stack += [(n[2], k), (n[3], k + 1)]
                elif n[0] == 'letE':
                    stack += [(n[2], k), (n[3], k), (n[4], k + 1)]
                else:
                    stack += [(n[j], k) for j in vx._EXPR_KIDS[n[0]]]
            out.append((node[4], dep))
        e = node[3]
    return out


def fields_as_walked(env):
    ctors = [env._render(c) for c, d in env._decls.items() if d.kind == 'ctor']
    got_ = [vx.fields(env, c) for c in ctors]
    differ = [c for c, g in zip(ctors, got_)
              if (g if g is None else [(i, dep) for _, i, dep in g]) != walk_fields(env, c)]
    print('      %d constructors, %d differ %s' % (len(ctors), len(differ), differ[:3]))
    return len(ctors) >= 20 and not differ


check('fields: as a walk per field finds them, on every constructor of good and weak',
      attempt(lambda: fields_as_walked(good) and fields_as_walked(W)) is True)


def hostile_ctor(d, m):
    """H.mk, of D fields each of the type L(M) of hostile(); H.big, whose one field's type is a bound
    variable whose set of indices would not fit; and H2.a (x : Nat) and H2.b (y : Bool), small."""
    b = Build()
    term = b.expr('bvar', d + m)
    for _ in range(m):
        term = b.bind('forallE', (), term, term)
    h = b.const('H')
    mk = h
    for i in reversed(range(d)):
        mk = b.bind('forallE', ('f%d' % i,), term, mk)
    big = b.bind('forallE', ('x',), b.expr('bvar', 2 ** 40), h)
    b.inductive('H', b.expr('sort', 0), [('mk', mk, d), ('big', big, 1)])
    h2 = b.const('H2')
    b.inductive('H2', b.expr('sort', 0), [('a', b.bind('forallE', ('x',), b.const('Nat'), h2), 1),
                                          ('b', b.bind('forallE', ('y',), b.const('Bool'), h2), 1)])
    return b.env()


def timed_fields(env, ctor):
    t0 = time.monotonic()
    out = vx.fields(env, ctor)
    secs = time.monotonic() - t0
    print('      %.2f s' % secs)
    return out, secs < 2


hctor = attempt(lambda: hostile_ctor(1600, 1600))
check('fields: 1600 fields over a shared term of 1600 nodes, in under 2 s',
      attempt(lambda: timed_fields(hctor, 'H.mk')) == ([('f%d' % i, 'default', False) for i in range(1600)], True))
H2 = {'H2': 'inductive H2 : Prop', 'H2.a': 'constructor H2.a : Nat → H2', 'H2.b': 'constructor H2.b : Bool → H2'}
check('fields: past its budget None, so the constructor is shown as nanoda_bin printed it',
      attempt(lambda: vx.fields(hctor, 'H.big')) is None
      and attempt(lambda: va._constructor(hctor, 'H.big', 'constructor H.big : x → H')) == 'H.big : x → H'
      # Good.Range.mk's type is 4 expressions: its two foralls, Nat and Good.Range.
      and attempt(lambda: with_steps(3, lambda: (vx.fields(good, 'Good.Range.mk'),
                                                 va._constructor(good, 'Good.Range.mk', NANO['Good.Range.mk']))))
      == (None, 'Good.Range.mk : Nat → Nat → Good.Range'))
# H2.a takes 3 steps (its forall, Nat, H2) and H2.b 2 more (H2 is known): one budget of 4 for the type
# covers the first and not the second.
check("fields: an inductive type's constructors share one budget",
      attempt(lambda: with_steps(4, lambda: va._definition(hctor, 'H2', H2, {'H2': ['H2.a', 'H2.b']})))
      == ('inductive H2 : Prop\nconstructors:\n  H2.a (x : Nat) : H2\n  H2.b : Bool → H2', None)
      and attempt(lambda: va._definition(hctor, 'H2', H2, {'H2': ['H2.a', 'H2.b']}))
      == ('inductive H2 : Prop\nconstructors:\n  H2.a (x : Nat) : H2\n  H2.b (y : Bool) : H2', None))
check('names with macro scopes: one per name, numbered when two differ, constants too, «» names untouched',
      [attempt(lambda t=t: va._hygiene(t)) for t in (
          'f x._@.M._hyg.1 x._@.M._hyg.1', '(x._@.M._hyg.1 : A) (x._@.N._hygCtx._hyg.2 : B) y._@.M._hyg.3',
          'Foo.bar._@.M.1._hygCtx._hyg.4 «x._@.M._hyg.1» x._@.M._hyg.5z', 'plain text')]
      == ['f x✝ x✝', '(x✝ : A) (x✝¹ : B) y✝', 'Foo.bar✝ «x._@.M._hyg.1» x._@.M._hyg.5z',
          'plain text'])
check('a statement is shown with its macro-scoped names as Lean shows them',
      (attempt(lambda: run('good', ['Good.t1'], pp=nano({'Good.t1': 'theorem Good.t1 (x._@.M._hyg.1 : Nat) : True'})))
       or {}).get('claims', [{}])[0].get('statement') == 'theorem Good.t1 (x✝ : Nat) : True')

# Messages go to the developer's log in a job that holds a token. GitHub's runner reads `::command::`
# at the start of a line and the legacy `##[command]` anywhere in one, and may skip invisible
# characters when it looks for them.
try:
    from vacheck.text import log_line  # noqa: E402
except ImportError as e:
    print('      cannot import vacheck.text: %s' % e)
    log_line = None


def log_safe(msg):
    """One line of printable ASCII, with no `::` or `##` left in it."""
    if msg is None or not all(' ' <= c <= '~' for c in msg) or '::' in msg or '##' in msg:
        print('      unsafe message: %s' % ascii(msg))
        return False
    return True


LOG_CASES = ['x\n::error::injected', '##[set-output name=result;]{"forged":1}', '#\u200b#[error]x', '::::',
             '###[', ':\u200b:error::', '\r\n::add-mask::x', 'a\u2028::b', '\ufeff##[stop-commands]x',
             '#\u00ad#[', '\u202e::x', ': :', '#\U000e0001#[', 'a\\b', '\ud800']
check('log_line gives one safe line', attempt(lambda: all(log_safe(log_line(s)) for s in LOG_CASES)) is True)
check('log_line removes control and format characters and escapes the rest visibly',
      attempt(lambda: [log_line(s) for s in ('a\nb\u200bc\u202ed\ufeffe\x07f\u00adg', 'Good.«key»',
                                             'a\u2028b', 'a\\b', 'plain text: ok', '\U0001d4b3')])
      == ['abcdefg', 'Good.\\xabkey\\xbb', 'a\\u2028b', 'a\\\\b', 'plain text: ok', '\\U0001d4b3'])


def axiom_named(name):
    """An export whose theorem t rests on one axiom, called `name`."""
    return vx.load_export(export_file(
        [META, json.dumps({'in': 1, 'str': {'pre': 0, 'str': name}}), '{"in":2,"str":{"pre":0,"str":"t"}}', SORT,
         '{"ie":1,"const":{"name":1,"us":[]}}', '{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}',
         '{"thm":{"name":2,"levelParams":[],"type":1,"value":1,"all":[2]}}']))


probe_msgs = [attempt(lambda p=p: (lambda env: analysis_error(lambda: run('good', ['t'], export=env, ref=env)))(
    axiom_named(p))) for p in ('x\n::error::injected', '##[set-output name=result;]{"forged":1}', '#\u200b#[error]x')]
check('an axiom name cannot inject a workflow command',
      all(log_safe(m) for m in probe_msgs) and 'injected' in probe_msgs[0] and 'forged' in probe_msgs[1])
check('a theorem name cannot inject a workflow command',
      all(log_safe(analysis_error(lambda t=t: run('good', [t])))
          for t in ('Good.«::error::x»', 'Good.«##[set-output name=result;]x»',
                    'Good.«#\u200b#[error]x»', 'Good.«x:»', 'Good.«a\u2028b»')))
shutil.rmtree(TMP)

if failures:
    print('FAILED: ' + ', '.join(failures))
    sys.exit(1)
print('test_vacheck: %d checks' % count)
