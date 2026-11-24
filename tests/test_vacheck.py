import copy
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
      parse_manifest(man(claims=[claim(says='a‮b\x07c')])).claims[0].says == 'abc')
check('says empty after strip rejected', man_rejected(man(claims=[claim(says='\x07')])))

res = {
    'schema': SCHEMA, 'repo': 'github.com/acme/proj', 'commit': 'a' * 40, 'toolchain': 'v4.36.0',
    'checker': '1.0.0', 'project': 'core', 'build_digest': 'b' * 64,
    'claims': [{'says': 'x', 'theorem': 'OSVA.affectedIn_sound', 'about': 'code', 'statement': 'st',
                'defs': [{'name': 'OSVA.affectedIn', 'text': 'def'}], 'axioms': ['propext'],
                'source': {'path': 'core/OSVACore/Ranges.lean', 'line': 56}}],
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
check('result 21 defs rejected', result_rejected(lambda r: r['claims'][0].update(defs=[{'name': 'n', 'text': 't'}] * 21)))
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
    lambda r: r.update(claims=[dict(r['claims'][0], defs=[{'name': 'n', 'text': 'a' * 4000}] * 20)] * 20)))
try:
    validate_result([])
    good = False
except ResultError:
    good = True
check('result non-object rejected', good)

check('deeply nested manifest raises ManifestError', man_rejected(b'[' * 20000))
check('lone surrogate in result raises ResultError',
      result_rejected(lambda r: r['claims'][0].update(statement='\ud800')))
import typing  # noqa: E402
from vacheck.manifest import Claim, Manifest  # noqa: E402
_mh = typing.get_type_hints(Manifest)
_ch = typing.get_type_hints(Claim)
check('Manifest and Claim field types match the interface',
      _mh['modules'] == typing.Tuple[str, ...] and _mh['ships'] == typing.Tuple[str, ...]
      and _mh['claims'] == typing.Tuple[Claim, ...] and _ch['about'] == typing.Literal['code', 'model'])

if failures:
    print('FAILED: ' + ', '.join(failures))
    sys.exit(1)
print('test_vacheck: %d checks' % count)
