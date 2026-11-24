"""The command line, run as the workflow runs it: `python3 -I vacheck.pyz ...`, with the zipapp that
scripts/release.sh builds, on the fixtures, and with the real nanoda_bin of the v4.36.0 toolchain
(NANODA_BIN overrides where it is)."""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
FIXTURES = os.path.join(ROOT, 'tests', 'fixtures')
NANODA = os.environ.get('NANODA_BIN') or os.path.expanduser(
    '~/.elan/toolchains/leanprover--lean4---v4.36.0/bin/nanoda_bin')
MODULES = {'good': 'Good', 'sorry': 'Sorry', 'native': 'Native'}
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


def release(out_dir):
    return subprocess.run(['bash', os.path.join(ROOT, 'scripts', 'release.sh'), out_dir],
                          capture_output=True, text=True)


# The zipapp, built as a release builds it.
OUT1, OUT2 = fresh('dist'), fresh('dist')
build = attempt(lambda: release(OUT1))
PYZ = os.path.join(OUT1, 'vacheck.pyz')
check('release.sh builds vacheck.pyz and prints its sha256',
      build is not None and build.returncode == 0 and os.path.isfile(PYZ)
      and build.stdout.split()[:1] == [sha256_of(PYZ)])
time.sleep(2)  # zip times have a resolution of two seconds
build2 = attempt(lambda: release(OUT2))
check('release.sh builds the same bytes every time',
      build2 is not None and build2.returncode == 0 and os.path.isfile(PYZ)
      and sha256_of(os.path.join(OUT2, 'vacheck.pyz')) == sha256_of(PYZ))


class Run:
    def __init__(self, proc):
        self.code = proc.returncode
        self.out = proc.stdout.decode('utf-8', errors='replace')
        self.err = proc.stderr.decode('utf-8', errors='replace')

    def one_line(self):
        """The message on stderr is one line, with no `::` that GitHub could read as a workflow command."""
        ok = self.err.endswith('\n') and self.err.count('\n') == 1 and '::' not in self.err
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


# analyze
def reference(case):
    """The toolchain's own export of the fixture's library names: the fixture's export without the
    declarations in its own namespace."""
    own = MODULES[case]
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
            if any(n == own or n.startswith(own + '.') for n in decls):
                continue
            out.write(line)
    return path


def tree(case, claims, raw=None):
    """A checkout: the fixture's Lake project in `core`, the manifest at the root."""
    root = fresh('repo')
    shutil.copytree(os.path.join(FIXTURES, case), os.path.join(root, 'core'))
    write(os.path.join(root, '.verificationalliance.json'),
          raw if raw is not None else manifest(modules=(MODULES[case],), claims=claims))
    return root


def analyze(case, claims=(), root=None, nanoda=NANODA, toolchain='v4.36.0'):
    root = root or tree(case, claims)
    return cli('analyze', '--export', os.path.join(FIXTURES, case + '.ndjson'), '--reference', REFS[case],
               '--manifest', os.path.join(root, '.verificationalliance.json'), '--source', root,
               '--repo', REPO, '--commit', COMMIT, '--toolchain', toolchain, '--kernels', 'lean,nanoda',
               '--nanoda', nanoda)


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
check('the statement of Good.t1 is printed by nanoda',
      t1.get('statement') == 'theorem Good.t1 (n : Nat) :\n'
      '  Or (Eq (Good.f n) (HAdd.hAdd n (OfNat.ofNat 1))) (Ne (Good.f n) (HAdd.hAdd n (OfNat.ofNat 1))) :=\n'
      '  _')
check('the definition of Good.f is printed by nanoda',
      t1.get('defs') == [{'name': 'Good.f', 'text': 'def Good.f (n : Nat) : Nat := HAdd.hAdd n (OfNat.ofNat 1)'}])
check('a name with «» is printed',
      by_theorem.get('Good.«key never leaves»', {}).get('statement')
      == 'theorem «Good.key never leaves» (n : Nat) : LT.lt n (Good.f n) := _')
check('analyze sorry rejected', analyze('sorry', (('x', 'Sorry.t', 'model'),)).rejected('Sorry.t', 'sorryAx'))
check('analyze native_decide rejected, by the axiom it adds',
      analyze('native', (('x', 'Native.t', 'model'),)).rejected('Native.t._native.native_decide.ax_1_1'))
check('analyze an unsupported toolchain rejected',
      analyze('good', good_claims, toolchain='v4.34.0').rejected('v1 supports Lean v4.35.0 or later'))
check('an analysis error is one line, with no workflow command',
      analyze('good', (('x', 'Good.«::error::x»', 'model'),)).rejected('is not in the export'))
moved = tree('good', (('x', 'Good.t1', 'model'),))
os.makedirs(os.path.join(moved, 'sub'))
os.rename(os.path.join(moved, '.verificationalliance.json'), os.path.join(moved, 'sub', 'va.json'))
r = cli('analyze', '--export', os.path.join(FIXTURES, 'good.ndjson'), '--reference', REFS['good'],
        '--manifest', os.path.join(moved, 'sub', 'va.json'), '--source', moved, '--repo', REPO, '--commit', COMMIT,
        '--toolchain', 'v4.36.0', '--kernels', 'lean', '--nanoda', NANODA)
check('analyze reads the manifest that --manifest names', r.code == 0 and r.err == '')
# The build digest covers the manifest file that --manifest names.
spaced = result_of(analyze('good', root=tree('good', (), raw=manifest(claims=good_claims) + ' ')))
check('the build digest covers the manifest file',
      'build_digest' in spaced and good_res.get('build_digest') not in (None, spaced['build_digest']))


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
for args in ((), ('nope',), ('toolchain',), ('analyze', '--export', 'x')):
    r = cli(*args)
    check('misuse %r exits 2' % (args,), os.path.isfile(PYZ) and r.code == 2 and r.one_line())

shutil.rmtree(TMP)
if failures:
    print('FAILED: ' + ', '.join(failures))
    sys.exit(1)
print('test_cli: %d checks' % count)
