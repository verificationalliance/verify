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
           'replaced': 'Replaced'}
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


def run(case, theorems=(), tree=None, ref=None, export=None, pp=printer, repo=REPO):
    """analyze on the fixture's export and its reference, with a new source tree unless `tree` is given."""
    root, manifest = tree or source_tree(case, [('x', t, 'model') for t in theorems])
    return va.analyze(envs[case] if export is None else export, refs[case] if ref is None else ref,
                      manifest, root, repo, COMMIT, 'v4.36.0', KERNELS, pp)


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


good_tree = attempt(lambda: source_tree('good', [('Never ‮leaks\x07.', 'Good.«key never leaves»', 'code'),
                                                 ('f is n + 1, or not.', 'Good.t1', 'model')], ships=['Good']))
good_res = attempt(lambda: run('good', tree=good_tree)) or {}
gc = good_res.get('claims') or [{}, {}]
check('good passes', valid(good_res)
      and [c.get('theorem') for c in gc] == ['Good.«key never leaves»', 'Good.t1']
      and [c.get('source') for c in gc]
      == [{'path': 'core/Good.lean', 'line': 7}, {'path': 'core/Good.lean', 'line': 5}])
check('good statements, defs and axioms',
      [(c.get('statement'), c.get('defs'), c.get('axioms')) for c in gc]
      == [('<pp Good.«key never leaves»>', [{'name': 'Good.f', 'text': '<pp Good.f>'}], []),
          ('<pp Good.t1>', [{'name': 'Good.f', 'text': '<pp Good.f>'}], ['Classical.choice', 'Quot.sound', 'propext'])])
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


def long_replaced():
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    write(os.path.join(root, 'core', 'Good.lean'), '\n   @[extern "⁦%s"] opaque g : Nat\n' % ('a' * 300), 'a')
    return run('good', tree=(root, manifest))['evidence']['replaced']


check('replaced lines trimmed to 160 plain characters',
      attempt(long_replaced) == [{'path': 'core/Good.lean', 'line': 11, 'text': ('@[extern "' + 'a' * 300)[:160]}])


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


ds = attempt(lambda: digests(append('README.md'), append('core/README.md'), append('core/Good.lean', '\n-- x\n')))
check('build digest changes with a lean file and not with README.md',
      ds is not None and is_sha256(ds[0]) and ds[0] == ds[1] == ds[2] != ds[3])
covered = ('core/lakefile.toml', 'core/lake-manifest.json', 'core/lean-toolchain', '.verificationalliance.json',
           'core/lakefile.lean', 'core/Good/Sub.lean')
ds = attempt(lambda: digests(*[append(rel) for rel in covered]))
check('build digest covers the lake files, the manifest and every lean file',
      ds is not None and len(set(ds)) == len(covered) + 1)
ds = attempt(lambda: digests(append('core/.lake/build/X.lean'), append('core/Good/.lake/Y.lean'),
                             append('core/Good.olean'), append('Top.lean')))
check('build digest leaves out .lake, other files and files outside the project',
      ds is not None and len(set(ds)) == 1)

OUTSIDE = fresh('outside')
write(os.path.join(OUTSIDE, 'A.lean'), 'theorem t1 : True := trivial\n@[extern "x"] opaque y : Nat\n')


def outside_reads(prepare):
    """(source of Good.t1, replaced, digest unchanged) after prepare(project folder)."""
    tree = source_tree('good', [('x', 'Good.t1', 'model')])
    before = run('good', tree=tree)['build_digest']
    prepare(os.path.join(tree[0], 'core'))
    r = run('good', tree=tree)
    return r['claims'][0]['source'], r['evidence']['replaced'], r['build_digest'] == before


UNREAD = ({'path': 'core/Good.lean', 'line': 5}, [], True)
check('a symlinked lean file is not read',
      attempt(lambda: outside_reads(lambda p: os.symlink(os.path.join(OUTSIDE, 'A.lean'), os.path.join(p, 'A.lean'))))
      == UNREAD)
check('a symlinked folder is not followed',
      attempt(lambda: outside_reads(lambda p: os.symlink(OUTSIDE, os.path.join(p, 'Ab')))) == UNREAD)


def link_toolchain(project):
    """Replaces lean-toolchain with a symlink to a copy outside: same text, so only skipping it shows."""
    shutil.copy(os.path.join(project, 'lean-toolchain'), os.path.join(OUTSIDE, 'lean-toolchain'))
    os.remove(os.path.join(project, 'lean-toolchain'))
    os.symlink(os.path.join(OUTSIDE, 'lean-toolchain'), os.path.join(project, 'lean-toolchain'))


check('a symlinked lake file is not read', attempt(lambda: outside_reads(link_toolchain)[2]) is False)
BIG = 'theorem t1 : True := trivial\n@[extern "x"] opaque y : Nat\n'
check('a lean file over 2 MB is not read',
      attempt(lambda: outside_reads(lambda p: write(os.path.join(p, 'A.lean'), BIG + ' ' * (MB2 + 1 - len(BIG)))))
      == UNREAD)
check('a lean file of 2 MB is read',
      attempt(lambda: outside_reads(lambda p: write(os.path.join(p, 'A.lean'), BIG + ' ' * (MB2 - len(BIG)))))
      == ({'path': 'core/A.lean', 'line': 1},
          [{'path': 'core/A.lean', 'line': 2, 'text': '@[extern "x"] opaque y : Nat'}], False))


def symlinked_project():
    root, manifest = source_tree('good', [('x', 'Good.t1', 'model')])
    os.rename(os.path.join(root, 'core'), os.path.join(OUTSIDE, 'core'))
    os.symlink(os.path.join(OUTSIDE, 'core'), os.path.join(root, 'core'))
    return run('good', tree=(root, manifest))


check('a symlinked project folder rejected', analysis_error(symlinked_project) is not None)


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
shutil.rmtree(TMP)

if failures:
    print('FAILED: ' + ', '.join(failures))
    sys.exit(1)
print('test_vacheck: %d checks' % count)
