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

# Lean exports. tests/make_fixtures.sh writes the fixtures from the Lake projects in tests/fixtures.
import re  # noqa: E402
import shutil  # noqa: E402
import tempfile  # noqa: E402

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
shutil.rmtree(TMP)

if failures:
    print('FAILED: ' + ', '.join(failures))
    sys.exit(1)
print('test_vacheck: %d checks' % count)
