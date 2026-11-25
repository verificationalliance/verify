"""The command line, run as the workflow runs it: `python3 -I vacheck.pyz ...`, with the zipapp that
scripts/build.sh builds for a release, on the fixtures, and with the real tools of the v4.36.0
toolchain: its nanoda_bin (NANODA_BIN overrides where it is), and its lean and leanc to build the
sanity helper (LEAN_TOOLCHAIN overrides where the toolchain is)."""
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unicodedata

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
from vacheck.text import log_line  # noqa: E402
FIXTURES = os.path.join(ROOT, 'tests', 'fixtures')
NANODA = os.environ.get('NANODA_BIN') or os.path.expanduser(
    '~/.elan/toolchains/leanprover--lean4---v4.36.0/bin/nanoda_bin')
LEAN_TOOLCHAIN = os.environ.get('LEAN_TOOLCHAIN') or os.path.expanduser(
    '~/.elan/toolchains/leanprover--lean4---v4.36.0')
MODULES = {'good': 'Good', 'sorry': 'Sorry', 'native': 'Native', 'weak': 'Weak', 'printed': 'Printed'}
REPO, COMMIT = 'github.com/acme/proj', 'c' * 40
TMP = tempfile.mkdtemp(prefix='test_cli-')

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


def attempt(fn):
    """Runs fn. An exception is a failed check, not a crash that hides the checks after it."""
    try:
        return fn()
    except Exception as e:
        print('      %s: %s' % (type(e).__name__, e))
        return None


_serial = iter(range(10 ** 6))


def fresh(name):
    return os.path.join(TMP, '%d-%s' % (next(_serial), name))


def write(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'wb') as f:
        f.write(data if isinstance(data, bytes) else data.encode('utf-8'))
    return path


def sha256_of(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=False)


def build_pyz(out_dir):
    return subprocess.run(['bash', os.path.join(ROOT, 'scripts', 'build.sh'), out_dir],
                          capture_output=True, text=True)


# The zipapp, built as a release builds it.
OUT1, OUT2 = fresh('dist'), fresh('dist')
build = attempt(lambda: build_pyz(OUT1))
PYZ = os.path.join(OUT1, 'vacheck.pyz')
check('build.sh builds vacheck.pyz and prints its sha256',
      build is not None and build.returncode == 0 and os.path.isfile(PYZ)
      and build.stdout.split()[:1] == [sha256_of(PYZ)])
time.sleep(2)  # zip times have a resolution of two seconds
build2 = attempt(lambda: build_pyz(OUT2))
check('build.sh builds the same bytes every time',
      build2 is not None and build2.returncode == 0 and os.path.isfile(PYZ)
      and sha256_of(os.path.join(OUT2, 'vacheck.pyz')) == sha256_of(PYZ))


class Run:
    def __init__(self, proc):
        self.code = proc.returncode
        self.raw = proc.stdout
        self.out = proc.stdout.decode('utf-8', errors='replace')
        self.err = proc.stderr.decode('utf-8', errors='replace')

    def one_line(self):
        """The message on stderr is one line of printable ASCII, with no `::` or `##` that GitHub's runner
        could read as a workflow command."""
        ok = (self.err.endswith('\n') and all(' ' <= c <= '~' for c in self.err[:-1])
              and '::' not in self.err and '##' not in self.err)
        if not ok:
            print('      stderr: %r' % self.err)
        return ok

    def rejected(self, *needles):
        ok = self.code == 1 and self.out == '' and self.one_line() and all(n in self.err for n in needles)
        if not ok:
            print('      exit %s, stderr: %r' % (self.code, self.err))
        return ok


def cli(*args):
    return Run(subprocess.run([sys.executable, '-I', PYZ] + list(args), capture_output=True, cwd=TMP))


# toolchain <lean-toolchain file>
with open(os.path.join(ROOT, 'vacheck', 'toolchains.json'), encoding='utf-8') as f:
    TABLE = json.load(f)
r = cli('toolchain', write(fresh('lean-toolchain'), 'leanprover/lean4:v4.36.0\n'))
check('toolchain v4.36.0 prints the url and the sha256',
      r.code == 0 and r.out == '%s %s\n' % (TABLE['v4.36.0']['url'], TABLE['v4.36.0']['sha256']))
r = cli('toolchain', write(fresh('lean-toolchain'), 'leanprover/lean4:v4.34.0\n'))
check('toolchain v4.34.0 rejected', r.rejected())
check('toolchain v4.34.0 names the supported versions',
      r.err == 'v1 supports Lean v4.35.0 or later from: v4.35.0, v4.36.0\n')
link = fresh('lean-toolchain')
os.symlink(write(fresh('lean-toolchain'), 'leanprover/lean4:v4.36.0\n'), link)
check('toolchain through a symlink rejected', cli('toolchain', link).rejected('symlink'))
r = cli('toolchain', write(fresh('lean-toolchain'), 'leanprover/lean4:v4.36.0' + ' ' * 1001 + '\n'))
check('a lean-toolchain over 1024 bytes rejected', r.rejected('larger than 1024 bytes'))
check('toolchain nightly rejected', cli('toolchain', write(fresh('lean-toolchain'), 'leanprover/lean4:nightly\n'))
      .rejected('v1 supports Lean v4.35.0 or later'))

# deps <lake-manifest.json>
check('deps without packages accepted', cli('deps', os.path.join(FIXTURES, 'good', 'lake-manifest.json')).code == 0)
lake = json.load(open(os.path.join(FIXTURES, 'good', 'lake-manifest.json'), encoding='utf-8'))
lake['packages'] = [{'type': 'git', 'name': 'mathlib', 'url': 'x', 'rev': 'y', 'inherited': False}]
r = cli('deps', write(fresh('lake-manifest.json'), json.dumps(lake)))
check('deps with one package rejected', r.rejected() and r.err == 'v1 supports projects without dependencies\n')
check('deps not JSON rejected', cli('deps', write(fresh('lake-manifest.json'), 'nope')).rejected())


# modules <manifest>
def manifest(project='core', modules=('Good',), claims=(('says', 'Good.t1', 'model'),), **extra):
    d = {'version': 1, 'project': project, 'modules': list(modules),
         'claims': [{'says': s, 'theorem': t, 'about': a} for s, t, a in claims]}
    d.update(extra)
    return json.dumps(d)


r = cli('modules', write(fresh('m.json'), manifest(modules=('Good', 'Good.Extra'))))
check('modules prints the project, then the modules', r.code == 0 and r.out == 'core\nGood\nGood.Extra\n')
r = cli('modules', write(fresh('m.json'), manifest(**{'x\n::error::injected': 1})))
check('a manifest error is one line, with no workflow command', r.rejected('unknown field'))
r = cli('modules', write(fresh('m.json'), manifest(**{'##[add-mask]x': 1})))
check('a manifest error has no legacy ##[ workflow command', r.rejected('unknown field'))


# analyze
def reference(case):
    """The toolchain's own export of the fixture's library names: the fixture's export without the
    declarations in its own namespace."""
    own = MODULES[case]
    return export_without(case, lambda n: n == own or n.startswith(own + '.'), case + '-reference.ndjson')


def export_without(case, drop, name):
    """A copy of the fixture's export without the lines that declare a name for which drop is true."""
    names = {0: None}
    path = fresh(name)
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
            if any(drop(n) for n in decls):
                continue
            out.write(line)
    return path


def tree(case, claims, raw=None):
    """A checkout: the fixture's Lake project in `core`, the manifest at the root."""
    root = fresh('repo')
    shutil.copytree(os.path.join(FIXTURES, case), os.path.join(root, 'core'), ignore=shutil.ignore_patterns('.lake'))
    write(os.path.join(root, '.verificationalliance.json'),
          raw if raw is not None else manifest(modules=(MODULES[case],), claims=claims))
    return root


def skipped(case, root):
    """A verdict file as if the sanity helper skipped every pair that sanity-targets lists for the
    checkout's manifest: empty when it lists none, or rejects the manifest."""
    r = cli('sanity-targets', '--export', os.path.join(FIXTURES, case + '.ndjson'), '--reference', REFS[case],
            '--manifest', os.path.join(root, '.verificationalliance.json'))
    pairs = [json.loads(line)[:2] for line in r.out.split('\n') if line] if r.code == 0 else []
    return write(fresh('verdicts'), ''.join('%d %d skipped\n' % (i, j) for i, j in pairs))


def analyze(case, claims=(), root=None, nanoda=NANODA, toolchain='v4.36.0', verdicts=None, abstracted=True):
    """vacheck analyze on the fixture, with the verdict file given, or skipped's."""
    root = root or tree(case, claims)
    more = ['--abstracted', verdicts or skipped(case, root)] if abstracted else []
    return cli('analyze', '--export', os.path.join(FIXTURES, case + '.ndjson'), '--reference', REFS[case],
               '--manifest', os.path.join(root, '.verificationalliance.json'), '--source', root,
               '--repo', REPO, '--commit', COMMIT, '--toolchain', toolchain, '--kernels', 'lean,nanoda',
               '--nanoda', nanoda, *more)


def result_of(r):
    try:
        return json.loads(r.out)
    except ValueError:
        print('      exit %s, stdout %r, stderr %r' % (r.code, r.out[:200], r.err))
        return {}


check('nanoda_bin is at %s' % NANODA, os.access(NANODA, os.X_OK))
REFS = {case: reference(case) for case in MODULES}
good_claims = (('Never leaks.', 'Good.«key never leaves»', 'code'), ('f is n + 1, or not.', 'Good.t1', 'model'))
good_run = analyze('good', good_claims)
good_res = result_of(good_run)
by_theorem = {c.get('theorem'): c for c in good_res.get('claims', [])}
t1 = by_theorem.get('Good.t1', {})
check('analyze good exits 0 with nothing on stderr', good_run.code == 0 and good_run.err == '')
check('analyze good writes canonical JSON', good_run.out == canonical(good_res))
check('analyze good carries the run',
      {k: good_res.get(k) for k in ('repo', 'commit', 'toolchain', 'project', 'kernels')}
      == {'repo': REPO, 'commit': COMMIT, 'toolchain': 'v4.36.0', 'project': 'core', 'kernels': ['lean', 'nanoda']})
check('the statement of Good.t1 is printed by nanoda, without its value',
      t1.get('statement') == 'theorem Good.t1 (n : Nat) :\n'
      '  Or (Eq (Good.f n) (HAdd.hAdd n (OfNat.ofNat 1))) (Ne (Good.f n) (HAdd.hAdd n (OfNat.ofNat 1)))')
check('the definition of Good.f is printed by nanoda',
      t1.get('defs') == [{'name': 'Good.f', 'text': 'def Good.f (n : Nat) : Nat := HAdd.hAdd n (OfNat.ofNat 1)',
                          'source': {'path': 'core/Good.lean', 'line': 3}, 'term': None}])
check('a name with «» is printed',
      by_theorem.get('Good.«key never leaves»', {}).get('statement')
      == 'theorem «Good.key never leaves» (n : Nat) : LT.lt n (Good.f n)')
check('analyze sorry rejected', analyze('sorry', (('x', 'Sorry.t', 'model'),)).rejected('Sorry.t', 'sorryAx'))
check('analyze native_decide rejected, by the axiom it adds',
      analyze('native', (('x', 'Native.t', 'model'),)).rejected('Native.t._native.native_decide.ax_1_1'))
check('analyze an unsupported toolchain rejected',
      analyze('good', good_claims, toolchain='v4.34.0').rejected('v1 supports Lean v4.35.0 or later'))
check('an analysis error is one line, with no workflow command',
      analyze('good', (('x', 'Good.«::error::x»', 'model'),)).rejected('is not in the export'))
forged = 'Good.«##[set-output name=result;]{"forged":1}»'
r = analyze('good', (('x', forged, 'model'),))
check('an analysis error has no legacy ##[ workflow command', r.rejected('is not in the export'))
check('an analysis error is escaped once: \\xab for «, not \\\\xab',
      r.err == log_line('%s is not in the export' % forged) + '\n'
      and '.\\xab# #[set-output' in r.err and '\\\\' not in r.err)
moved = tree('good', (('x', 'Good.t1', 'model'),))
os.makedirs(os.path.join(moved, 'sub'))
os.rename(os.path.join(moved, '.verificationalliance.json'), os.path.join(moved, 'sub', 'va.json'))
T1_SKIPPED = write(fresh('verdicts'), '0 0 skipped\n')  # Good.t1's one pair, Good.f
r = cli('analyze', '--export', os.path.join(FIXTURES, 'good.ndjson'), '--reference', REFS['good'],
        '--manifest', os.path.join(moved, 'sub', 'va.json'), '--source', moved, '--repo', REPO, '--commit', COMMIT,
        '--toolchain', 'v4.36.0', '--kernels', 'lean', '--nanoda', NANODA, '--abstracted', T1_SKIPPED)
check('analyze reads the manifest that --manifest names', r.code == 0 and r.err == '')
# --reference again for each library of the toolchain: every one that declares a name must agree.
two = tree('good', (('x', 'Good.t1', 'model'),))
for refs_, name in (((REFS['good'], REFS['good']), 'two references that agree accepted'),
                    ((REFS['good'], os.path.join(FIXTURES, 'fakeeq.ndjson')), 'a second reference whose Eq differs rejects')):
    r = cli('analyze', '--export', os.path.join(FIXTURES, 'good.ndjson'), *[a for p in refs_ for a in ('--reference', p)],
            '--manifest', os.path.join(two, '.verificationalliance.json'), '--source', two, '--repo', REPO,
            '--commit', COMMIT, '--toolchain', 'v4.36.0', '--kernels', 'lean', '--nanoda', NANODA,
            '--abstracted', T1_SKIPPED)
    check(name, r.code == 0 and r.err == '' if 'accepted' in name else r.rejected("Eq differs from the toolchain's Eq"))

# vacheck 1.1.2, with the real nanoda_bin: a structure with its constructor and named fields, a
# definition through a match or structural recursion by its header, and macro-scoped names as Lean
# shows them, x\u271d.
osva_like = result_of(analyze('good', (('x', 'Good.anyIn_nil', 'model'), ('y', 'Good.pick_lowest', 'model'))))
osva_defs = {d['name']: (d['text'], d['source']) for c in osva_like.get('claims', []) for d in c['defs']}
osva_terms = {d['name']: d['term'] for c in osva_like.get('claims', []) for d in c['defs']}
src = lambda line: {'path': 'core/Good.lean', 'line': line}  # noqa: E731
check('a structure is shown with its constructor and its fields, by name',
      osva_defs.get('Good.Range') == ('inductive Good.Range : Type 0\nconstructor:\n  Good.Range.mk (lo hi : Nat) : Good.Range', src(15)))
check('a definition through structural recursion is shown by its header, with its source',
      osva_defs.get('Good.lowest') == ('def Good.lowest (a\u271d : List Nat) : Nat\n  (body compiled; the checked term is below)', src(23)))
check('... and its checked term, as nanoda_bin prints it, macro-scoped names as Lean shows them',
      osva_terms.get('Good.lowest') == 'def Good.lowest (a\u271d : List Nat) : Nat := List.brecOn a\u271d Good.lowest._f'
      and osva_terms.get('Good.pick', '').startswith('def Good.pick (o : Option Nat) : Nat :=\n  Good.pick.match_1')
      and osva_terms.get('Good.anyIn') is None and osva_terms.get('Good.Range') is None)
check('a definition through a match is shown by its header, with its source',
      osva_defs.get('Good.pick') == ('def Good.pick (o : Option Nat) : Nat\n  (body compiled; the checked term is below)', src(27)))
check('a definition is shown whole, with macro-scoped names as Lean shows them',
      osva_defs.get('Good.anyIn') == ('def Good.anyIn (rs : List Good.Range) (x\u271d : Nat) : Bool :=\n  List.any rs\n'
                                      '    (fun (x\u271d\u00b9 : Good.Range) =>\n    Good.Range.contains x\u271d\u00b9 x\u271d)', src(21)))
check('the claims have their sources by full name',
      [c.get('source') for c in osva_like.get('claims', [])] == [src(32), src(34)])

# names <export>: the exact components of every declaration's name, for the workflow's reference.
NAMES_IN_GOOD = 264
r = cli('names', os.path.join(FIXTURES, 'good.ndjson'))
name_lines = r.out.split('\n')
parsed = attempt(lambda: [json.loads(line) for line in name_lines[:-1]]) or []
check('names prints one JSON array per declaration, sorted, and nothing else',
      r.code == 0 and r.err == '' and name_lines[-1] == '' and len(parsed) == NAMES_IN_GOOD
      and name_lines[:-1] == sorted(name_lines[:-1])
      and all(isinstance(p, list) and p and all(type(c) in (str, int) for c in p) for p in parsed))
check('names writes a «» component as it is and a number as a number',
      ['Good', 'key never leaves'] in parsed and ['_private', 'Init', 'Classical', 0, 'Classical', 'em', 'match_1_1'] in parsed
      and '["Good","key never leaves"]' in name_lines)
# imports --manifest F --source D: the toolchain libraries the project's .lean files import.
imp = tree('good', (('x', 'Good.t1', 'model'),))
write(os.path.join(imp, 'core', 'Good', 'X.lean'), 'import LeanChecker.«x»\npublic import Std.Data\n')
write(os.path.join(imp, 'Outside.lean'), 'import LeanIR\n')
r = cli('imports', '--manifest', os.path.join(imp, '.verificationalliance.json'), '--source', imp)
check('imports prints the roots the project imports, sorted, one per line',
      r.code == 0 and r.err == '' and r.out == 'LeanChecker\nStd\n')
os.symlink(os.path.join(imp, 'core', 'Good.lean'), os.path.join(imp, 'core', 'Link.lean'))
check('imports through a symlinked file rejected',
      cli('imports', '--manifest', os.path.join(imp, '.verificationalliance.json'), '--source', imp).rejected('symlink'))
check('names of a file that is not an export rejected',
      cli('names', write(fresh('x.ndjson'), '{"meta":1}\n::error::x\n')).rejected('the export cannot be read'))
# The build digest covers the manifest file that --manifest names.
spaced = result_of(analyze('good', root=tree('good', (), raw=manifest(claims=good_claims) + ' ')))
check('the build digest covers the manifest file',
      'build_digest' in spaced and good_res.get('build_digest') not in (None, spaced['build_digest']))

# sanity-source, sanity-targets, and the kernel helper they feed: built from sanity-source's output as
# the action builds it (`lean -c`, then `leanc -lLeanExport`), and run with the environment the
# sandbox gives it.
SANITY_LEAN = os.path.join(ROOT, 'vacheck', 'sanity.lean')
r = cli('sanity-source')
packaged = attempt(lambda: open(SANITY_LEAN, 'rb').read())
check('sanity-source prints the packaged sanity.lean', r.code == 0 and r.err == '' and r.raw and r.raw == packaged)


def build_helper(source):
    """The helper's path, compiled from source by the toolchain; None if it does not build."""
    d = fresh('sanity')
    write(os.path.join(d, 'Sanity.lean'), source)
    start = time.monotonic()
    for argv in ([os.path.join(LEAN_TOOLCHAIN, 'bin', 'lean'), '-c', 'sanity.c', 'Sanity.lean'],
                 [os.path.join(LEAN_TOOLCHAIN, 'bin', 'leanc'), '-o', 'sanity', 'sanity.c', '-lLeanExport']):
        p = attempt(lambda: subprocess.run(argv, cwd=d, capture_output=True, stdin=subprocess.DEVNULL))
        if p is None or p.returncode != 0:
            if p is not None:
                print('      %s exits %d: %s' % (os.path.basename(argv[0]), p.returncode,
                                                 (p.stdout + p.stderr).decode('utf-8', errors='replace')[-2000:]))
            return None
    print('      the helper builds in %.1f s' % (time.monotonic() - start))
    return os.path.join(d, 'sanity')


SANITY = build_helper(r.raw) if r.code == 0 and r.raw else None
check('the helper builds with %s' % LEAN_TOOLCHAIN, SANITY is not None)


def sanity_targets(case):
    return cli('sanity-targets', '--export', os.path.join(FIXTURES, case + '.ndjson'), '--reference', REFS[case],
               '--manifest', os.path.join(FIXTURES, case, '.verificationalliance.json'))


def helper(targets, export):
    """The helper on a targets file and an export, with only what the sandbox passes on; None if it was
    not built."""
    if SANITY is None:
        return None
    start = time.monotonic()
    p = subprocess.run([SANITY, targets, export], capture_output=True, stdin=subprocess.DEVNULL, cwd=TMP,
                       env={'HOME': TMP, 'PATH': '/usr/bin:/bin', 'LEAN_SYSROOT': LEAN_TOOLCHAIN,
                            'LEAN_ABORT_ON_PANIC': '1'})
    print('      the helper took %.2f s' % (time.monotonic() - start))
    return Run(p)


TARGETS = {case: sanity_targets(case) for case in ('good', 'weak')}
good_lines = TARGETS['good'].out.split('\n')
check('sanity-targets names a guillemet theorem by its components',
      TARGETS['good'].code == 0 and TARGETS['good'].err == '' and len(good_lines) > 2
      and good_lines[1] == '[1,0,["Good","key never leaves"],["Good","f"]]')
TARGET_FILES = {case: write(fresh(case + '-targets.jsonl'), t.raw) for case, t in TARGETS.items()}
VERDICTS = {}
for case, want in (('weak', '0 0 needed\n0 1 any\n1 0 needed\n1 1 needed\n2 0 any\n3 0 any\n4 0 any\n6 0 any\n'),
                   ('good', '0 0 any\n1 0 needed\n2 0 needed\n3 0 any\n3 1 needed\n')):
    h = helper(TARGET_FILES[case], os.path.join(FIXTURES, case + '.ndjson'))
    check('sanity helper: %s verdicts' % case, h is not None and h.code == 0 and h.err == '' and h.out == want)
    if h is not None and h.out != want:
        print('      exit %s, stdout %r, stderr %r' % (h.code, h.out, h.err))
    VERDICTS[case] = write(fresh(case + '-verdicts'), h.raw if h is not None else b'')


def fixture_claims(case):
    with open(os.path.join(FIXTURES, case, '.verificationalliance.json'), encoding='utf-8') as f:
        return [(c['says'], c['theorem'], c['about']) for c in json.load(f)['claims']]


def warnings_of(r):
    """Each claim's warnings in a result, as (check, name, arg), by theorem."""
    return {c['theorem']: [(w['check'], w['name'], w['arg']) for w in c['warnings']]
            for c in result_of(r).get('claims', [])}


# analyze with the real helper's verdicts and nanoda_bin: the weak fixture's warnings are Task 2's table.
WANT = {'Weak.prog_safe': [('holds-for-any', 'Weak.prog', None), ('always-true', 'Weak.Safe', None)],
        'Weak.sort_example': [],
        'Weak.add_zero_of_valid': [('holds-for-any', 'Weak.Valid', None), ('unused-assumption', 'h', None)],
        'Weak.sort_length_self': [('holds-for-any', 'Weak.sort', None)],
        'Weak.vacuous': [('holds-for-any', 'Weak.sort', None)],
        'Weak.no_project': [('no-project-definition', None, None)],
        'Weak.arrow': [('holds-for-any', 'Weak.Valid', None), ('unused-assumption', None, None)],
        'Weak.by_lemma': [('no-project-definition', None, None)]}
weak_run = analyze('weak', fixture_claims('weak'), verdicts=VERDICTS['weak'])
weak_claims = result_of(weak_run).get('claims', [])
check("analyze weak: each claim's warnings, and a null template",
      weak_run.code == 0 and warnings_of(weak_run) == WANT and list(warnings_of(weak_run)) == list(WANT)
      and all(c['template'] is None for c in weak_claims))
if warnings_of(weak_run) != WANT:
    print('      %r' % warnings_of(weak_run))
good_warned = analyze('good', fixture_claims('good'), verdicts=VERDICTS['good'])
check('analyze good: Good.t1 and Good.pick_lowest',
      warnings_of(good_warned) == {'Good.t1': [('holds-for-any', 'Good.f', None)], 'Good.«key never leaves»': [],
                                   'Good.anyIn_nil': [], 'Good.pick_lowest': [('holds-for-any', 'Good.lowest', None)]})
# What the page prints: nanoda_bin prints t5 as `theorem Printed.t5 : forall {α : Type 0} (xs : List α), Ne xs
# List.nil → ...`, so its unused h is not named; and P2 as `fun {α : Type 0} (m n : Nat) =>`, whose type
# calls m n.
printed_run = analyze('printed', fixture_claims('printed'))
check('analyze printed: an assumption printed after the colon, and an argument named two ways, are not named',
      {t: w for t, w in warnings_of(printed_run).items() if t in ('Printed.t5', 'Printed.u2', 'Printed.u4')}
      == {'Printed.t5': [('no-project-definition', None, None), ('unused-assumption', None, None)],
          'Printed.u2': [('ignores-argument', 'Printed.P2', None)],
          'Printed.u4': [('ignores-argument', 'Printed.P4', None)]})
short = write(fresh('verdicts'), open(VERDICTS['good'], 'rb').read().split(b'\n', 1)[1])
check('analyze rejects a verdict file missing a line',
      analyze('good', fixture_claims('good'), verdicts=short).rejected("the sanity helper's verdicts cannot be read"))
r = analyze('good', fixture_claims('good'), abstracted=False)
check('analyze needs --abstracted', r.code == 2 and r.out == '' and r.one_line() and '--abstracted' in r.err)
v1 = result_of(good_warned)
v1['schema'] = 'https://verificationalliance.org/attestations/proof-check/v1'
check('validate rejects a v1 result',
      cli('validate', write(fresh('result.json'), json.dumps(v1))).rejected('result.json is not valid'))


def string_literal_export():
    """An export of a theorem whose proof reduces a string literal. The kernel unfolds one to
    String.ofList [Char.ofNat n, ...], which no declaration names, so a replay in the order of what
    each declaration names can check the theorem first and reject it: leanchecker --from-export
    does, on v4.35.0 and v4.36.0 (lean4#15853). None if it cannot be built."""
    d = fresh('strlit')
    write(os.path.join(d, 'StrLit.lean'),
          'def greeting : String := "abc"\ntheorem t : greeting ++ "def" = "abcdef" := by decide\n')
    out = os.path.join(d, 'strlit.ndjson')
    # Without LEAN_SYSROOT, leanexport asks the `lean` on PATH where the toolchain is.
    env = dict(os.environ, LEAN_PATH=d, LEAN_SYSROOT=LEAN_TOOLCHAIN, LEAN_ABORT_ON_PANIC='1')
    for argv, stdout in (([os.path.join(LEAN_TOOLCHAIN, 'bin', 'lean'), '-o', 'StrLit.olean', 'StrLit.lean'], None),
                         ([os.path.join(LEAN_TOOLCHAIN, 'bin', 'leanexport'), 'StrLit', '--', 't'], out)):
        with open(stdout or os.devnull, 'wb') as f:
            p = attempt(lambda: subprocess.run(argv, cwd=d, stdout=f, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL,
                                               env=env))
        if p is None or p.returncode != 0:
            if p is not None:
                print('      %s exits %d: %s' % (os.path.basename(argv[0]), p.returncode,
                                                 p.stderr.decode('utf-8', errors='replace')[-2000:]))
            return None
    return out


strlit = string_literal_export()
h = strlit and helper(write(fresh('strlit-targets.jsonl'), '[0,0,["t"],["greeting"]]\n'), strlit)
check('sanity helper: a proof that reduces a string literal replays, String.ofList and Char.ofNat first',
      h is not None and h.code == 0 and h.out == '0 0 needed\n')
h = helper(TARGET_FILES['good'], export_without('good', lambda n: n == 'Good.f', 'good-without-f.ndjson'))
check('sanity helper: an export that does not replay gives skipped, exit 0',
      h is not None and h.code == 0 and h.err == ''
      and h.out == '0 0 skipped\n1 0 skipped\n2 0 skipped\n3 0 skipped\n3 1 skipped\n')
for bad in ('[0,0,["Good","t1"]]\n', '[0,"0",["Good","t1"],["Good","f"]]\n', '[0,-1,["Good","t1"],["Good","f"]]\n',
            '[0,0.5,["Good","t1"],["Good","f"]]\n', '[0,0,[],["Good","f"]]\n', '[0,0,["Good",true],["Good","f"]]\n',
            '[0,0,["Good","t1"],["Good","f"]]\n::error::x\n'):
    h = helper(write(fresh('bad-targets.jsonl'), bad), os.path.join(FIXTURES, 'good.ndjson'))
    check('sanity helper: a target line %r exits 1, one line on stderr' % bad, h is not None and h.rejected('targets'))
h = helper(os.path.join(TMP, 'no-such-targets.jsonl'), os.path.join(FIXTURES, 'good.ndjson'))
check('sanity helper: a file it cannot read exits 1, one line on stderr', h is not None and h.rejected())


# The printer: nanoda reads names by splitting them at dots, so a name it would read as another one
# is refused, and its output must name what was asked for, in order.
try:
    from vacheck import __main__ as vm  # noqa: E402
except ImportError as e:
    print('      cannot import vacheck.__main__: %s' % e)
    vm = None


def nanoda_name(name):
    try:
        return vm._nanoda_name(name)
    except Exception as e:
        return type(e).__name__


check('nanoda names: «» dropped, numbers kept',
      [nanoda_name(n) for n in ('Good.«key never leaves»', '_private.Good.0.Good.g', 'Good.t1')]
      == ['Good.key never leaves', '_private.Good.0.Good.g', 'Good.t1'])
check('nanoda names: a dot or a number inside «» refused',
      [nanoda_name(n) for n in ('Good.«a.b»', 'Good.«0»', '«Good.t1»')] == ['AnalysisError'] * 3)

SEEN = os.path.join(TMP, 'seen-config')


def fake_nanoda(prints):
    """A stand-in for nanoda_bin that keeps the path and the text of its config in SEEN and SEEN.json,
    then runs `prints`, Python with `names` (pp_declars) and `sep` (declar_sep) in scope."""
    path = write(fresh('fake-nanoda'), '#!%s -I\n' % sys.executable + '''import json, shutil, sys
with open(%r, 'w') as f:
    f.write(sys.argv[1])
shutil.copyfile(sys.argv[1], %r)
with open(sys.argv[1]) as f:
    config = json.load(f)
names, sep = config['pp_declars'], config['pp_options']['declar_sep']
''' % (SEEN, SEEN + '.json') + prints)
    os.chmod(path, 0o755)
    return path


AXIOM = "'axiom propext {a b : Prop} : Iff a b → Eq a b'"
# Leaves out the first declaration, as nanoda_bin does for a name it reads as another one.
r = analyze('good', (('x', 'Good.t1', 'model'),), nanoda=fake_nanoda(
    "sys.stdout.write(''.join('def %s : Nat := 1' % n + sep for n in names[1:]) + " + AXIOM + " + sep)"))
check('a printer output that skips a declaration rejected', r.rejected('Good.t1'))
check('the nanoda config is deleted', os.path.exists(SEEN) and not os.path.exists(open(SEEN).read()))
config = attempt(lambda: json.load(open(SEEN + '.json', encoding='utf-8'))) or {}
sep1 = config.get('pp_options', {}).pop('declar_sep', '')
check('the nanoda config: the options nanoda_bin prints with by default, and a separator',
      config == {
          'export_file_path': os.path.join(FIXTURES, 'good.ndjson'), 'use_stdin': False,
          'permitted_axioms': ['Classical.choice', 'Quot.sound', 'propext'], 'unpermitted_axiom_hard_error': False,
          'nat_extension': True, 'string_extension': True, 'pp_declars': ['Good.t1', 'Good.f'], 'pp_to_stdout': True,
          'pp_options': {'all': False, 'explicit': False, 'universes': False, 'notation': True, 'proofs': False},
          'print_success_message': False})
# Every declaration, but the output stops before the last separator: the last text may be cut short.
r = analyze('good', (('x', 'Good.t1', 'model'),), nanoda=fake_nanoda(
    "sys.stdout.write(sep.join('def %s : Nat := 1' % n for n in names))"))
check('a printer output cut short rejected', r.rejected('did not print'))
r = analyze('good', (('x', 'Good.t1', 'model'),), nanoda=fake_nanoda(
    "sys.stdout.write(''.join('def %s : Nat := 1' % n + sep for n in names) + 'def Good.g : Nat := 2' + sep)"))
check('a printer output with more than axioms after the declarations rejected', r.rejected('did not print'))
r = analyze('good', (('x', 'Good.t1', 'model'),), nanoda=fake_nanoda(
    "sys.stdout.write(''.join('def %s : Nat := 1' % n + sep for n in names) + " + AXIOM + " + sep)"))
check('a fake printer output in the expected shape accepted', r.code == 0 and r.err == '')
last = attempt(lambda: json.load(open(SEEN + '.json', encoding='utf-8'))) or {}
sep2 = last.get('pp_options', {}).get('declar_sep')
check('the separator is random, new each run',
      all(isinstance(x, str) and re.fullmatch('[0-9a-f]{32}', x) for x in (sep1, sep2)) and sep1 != sep2)
r = analyze('good', (('x', 'Good.t1', 'model'),), nanoda=fake_nanoda(
    "sys.stderr.write('##[add-mask]x\\n::error::y\\n'); sys.exit(1)"))
check('a nanoda_bin error is one line, with no workflow command', r.rejected('nanoda_bin could not print'))
r = analyze('good', (('x', 'Good.t1', 'model'),), nanoda=fake_nanoda(
    "sys.stdout.write(''.join('theorem %s : True := trivial' % n + sep for n in names))"))
check('a statement printed with its proof rejected', r.rejected('Good.t1'))
sleeper = fake_nanoda('import time\ntime.sleep(10)\n')


def timed_out():
    """The printer's message, and how long it took, with a timeout of 1 s on a nanoda_bin that sleeps 10 s."""
    vm.NANODA_TIMEOUT, start = 1, time.monotonic()
    try:
        vm.nanoda_printer(sleeper, os.path.join(FIXTURES, 'good.ndjson'))(['Good.t1'])
    except vm.AnalysisError as e:
        return str(e), time.monotonic() - start
    finally:
        vm.NANODA_TIMEOUT = 900
    return None, None


msg, took = attempt(timed_out) or (None, None)
check('nanoda_bin is stopped at the timeout, 900 s', vm is not None and vm.NANODA_TIMEOUT == 900
      and msg is not None and 'did not finish' in msg and took < 5)


def invisible(path):
    """The lines of a source file that hold a control, format or line separator character."""
    with open(path, encoding='utf-8') as f:
        return [i for i, line in enumerate(f, 1)
                if any(unicodedata.category(c) in ('Cc', 'Cf', 'Zl', 'Zp') for c in line.rstrip('\n'))]


sources = sorted(glob.glob(os.path.join(ROOT, 'vacheck', '*.py')) + glob.glob(os.path.join(ROOT, 'vacheck', '*.lean'))) + [
    os.path.abspath(__file__), os.path.join(ROOT, 'scripts', 'build.sh'),
    os.path.join(ROOT, 'scripts', 'release.sh')]
found = {os.path.relpath(p, ROOT): invisible(p) for p in sources}
check('invisible characters are written as escapes in the sources', len(found) > 5 and not any(found.values()))
if any(found.values()):
    print('      %s' % {k: v for k, v in found.items() if v})

# validate result.json
good_file = write(fresh('result.json'), good_run.out)
r = cli('validate', good_file)
check('validate prints the canonical JSON it read', r.code == 0 and r.out == good_run.out and good_run.out != '')
pretty = write(fresh('result.json'), json.dumps(good_res, indent=2, ensure_ascii=True))
r = cli('validate', pretty)
check('validate canonicalises', r.code == 0 and r.out == good_run.out and good_run.out != '')
check('validate rejects an extra key',
      cli('validate', write(fresh('result.json'), canonical(dict(good_res, extra=1)))).rejected())
check('validate rejects a repeated key',
      cli('validate', write(fresh('result.json'), good_run.out[:-1] + ',"repo":"github.com/a/b"}')).rejected())
check('validate rejects a file over 1 MB',
      cli('validate', write(fresh('result.json'), good_run.out + ' ' * (1024 * 1024))).rejected())

# Misuse exits 2, with one line.
for args in ((), ('nope',), ('##[add-mask]x::',), ('toolchain',), ('analyze', '--export', 'x')):
    r = cli(*args)
    check('misuse %r exits 2' % (args,), os.path.isfile(PYZ) and r.code == 2 and r.one_line())

shutil.rmtree(TMP)
if failures:
    print('FAILED: ' + ', '.join(failures))
    sys.exit(1)
print('test_cli: %d checks' % count)
