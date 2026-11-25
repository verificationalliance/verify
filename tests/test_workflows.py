"""lean.yml and the check action (.github/actions/check) must hold the same copies of the steps they
share. The action cannot use lean.yml's YAML anchors, so it writes out its own copy of each step that
build or sign also runs: the runner test, the checker and its scripts, the manifest reading and the
toolchain. A check that ran another checker, sandbox or runner test than build and sign would not be
the check this repository describes, so each copy's script, each constant and each action's pin must
be the same in both files. The files are read as text: the tests use the standard library only.
Then scripts/release.sh, which refuses a release whose lean.yml pins another check action than the
release commit's own, is run on a repository of commits made here."""
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, '.github', 'workflows', 'lean.yml')
ACTION = os.path.join(ROOT, '.github', 'actions', 'check', 'action.yml')
SHARED = ('Require a standard GitHub-hosted runner', 'Get the checker', 'Read the manifest',
          'Install the toolchain')
CONSTANTS = ('VACHECK_URL', 'VACHECK_SHA256', 'MAX_EXPORT', 'MAX_RESULT_B64')
PINNED = re.compile(r'(?:- )?uses: ([^@\s]+)@([0-9a-f]{40}) # \S+')

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


def lines_of(path):
    with open(path, encoding='utf-8') as f:
        return f.read().split('\n')


def indent(line):
    return len(line) - len(line.lstrip(' '))


def run_script(lines, name):
    """The `run: |` script of the one step called `name`, as YAML reads it; None if there is not
    exactly one such step, or it has no such script."""
    at = [i for i, line in enumerate(lines) if re.fullmatch(r' *(- )?name: ' + re.escape(name), line)]
    if len(at) != 1:
        return None
    key = lines[at[0]].index('name:')
    i = at[0] + 1
    while i < len(lines) and (not lines[i].strip() or indent(lines[i]) >= key):
        if indent(lines[i]) == key and lines[i].strip() == 'run: |':
            body = []
            for line in lines[i + 1:]:
                if line.strip() and indent(line) <= key:
                    break
                body.append(line)
            while body and not body[-1].strip():
                body.pop()
            if not body:
                return None
            cut = indent(body[0])
            return '\n'.join(line[cut:] for line in body)
        i += 1
    return None


def constants(lines):
    """Each constant's values in the file, as written, without a trailing comment."""
    found = {}
    for line in lines:
        m = re.fullmatch(r' *(%s): (.*?)(?: +#.*)?' % '|'.join(CONSTANTS), line)
        if m:
            found.setdefault(m.group(1), []).append(m.group(2))
    return found


def pins(lines):
    """Each action's pins, from the `uses:` lines that pin one by full SHA with a version comment."""
    found = {}
    for line in lines:
        m = PINNED.fullmatch(line.strip())
        if m:
            found.setdefault(m.group(1), set()).add(m.group(2))
    return found


lean, action = lines_of(LEAN), lines_of(ACTION)

for name in SHARED:
    mine, theirs = run_script(lean, name), run_script(action, name)
    check('lean.yml and the action each have one step "%s"' % name, mine is not None and theirs is not None)
    check('the step "%s" runs the same script in both' % name, mine is not None and mine == theirs)

lean_constants, action_constants = constants(lean), constants(action)
for c in CONSTANTS:
    values = lean_constants.get(c, []) + action_constants.get(c, [])
    check('%s is set in both files' % c, c in lean_constants and c in action_constants)
    check('%s has one value in both files' % c, len(set(values)) == 1)

uses = [line.strip() for line in lean + action if re.match(r' *(- )?uses: ', line)]
check('every action is pinned by full SHA, with a version comment',
      bool(uses) and all(PINNED.fullmatch(u) for u in uses))
lean_pins, action_pins = pins(lean), pins(action)
check('the action pins each action as lean.yml does',
      all(lean_pins.get(a, p) == p and len(p) == 1 for a, p in action_pins.items()))
check('lean.yml runs the check action, by its full name and SHA, once',
      len(lean_pins.get('verificationalliance/verify/.github/actions/check', ())) == 1
      and sum('.github/actions/' in u for u in uses) == 1)

# The test tests itself: a script changed by one character, or a step called twice, must not pass.
changed = [line.replace('HEAD, TAIL = 100, 300', 'HEAD, TAIL = 100, 301') for line in action]
check('a copy changed by one character differs',
      run_script(changed, 'Get the checker') != run_script(lean, 'Get the checker'))
check('a step called twice is not read', run_script(lean + lean, 'Get the checker') is None)



# scripts/release.sh, in a repository of its own: this checkout's history may be shallow.
def git(*args):
    return subprocess.run(['git', '-C', REPO] + list(args), env=GIT_ENV, capture_output=True, text=True,
                          check=True).stdout.strip()


def commit(message):
    git('add', '-A')
    git('commit', '-q', '-m', message)
    return git('rev-parse', 'HEAD')


def edit(path, old, new):
    path = os.path.join(REPO, path)
    with open(path, encoding='utf-8') as f:
        text = f.read()
    with open(path, 'w', encoding='utf-8') as f:
        f.write(re.sub(old, new, text, count=1))


def release():
    r = subprocess.run(['bash', os.path.join(REPO, 'scripts', 'release.sh'), os.path.join(TMP, 'dist')],
                       env=GIT_ENV, capture_output=True, text=True)
    return r.returncode, r.stdout


def pin(sha):
    edit(LEAN_PATH, r'(uses: verificationalliance/verify/\.github/actions/check@)[0-9a-f]{40}', r'\g<1>' + sha)


TMP = tempfile.mkdtemp(prefix='test_workflows-')
REPO = os.path.join(TMP, 'repo')
LEAN_PATH = os.path.join('.github', 'workflows', 'lean.yml')
ACTION_PATH = os.path.join('.github', 'actions', 'check', 'action.yml')
GIT_ENV = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM='1', GIT_AUTHOR_NAME='t',
               GIT_AUTHOR_EMAIL='t@example.invalid', GIT_COMMITTER_NAME='t', GIT_COMMITTER_EMAIL='t@example.invalid')
try:
    for d in ('scripts', 'vacheck', '.github'):
        shutil.copytree(os.path.join(ROOT, d), os.path.join(REPO, d), ignore=shutil.ignore_patterns('__pycache__'))
    subprocess.run(['git', 'init', '-q', REPO], env=GIT_ENV, capture_output=True, check=True)
    pin('0' * 40)
    first = commit('the action, pinned at no commit')
    check('release.sh refuses a pin that is no commit', release()[0] == 1)
    pin(first)
    second = commit('pinned at the commit before')
    code, out = release()
    check('release.sh releases a pin whose action is the release commit\'s, and prints the sha256',
          code == 0 and re.fullmatch(r'[0-9a-f]{64}  \S+vacheck\.pyz\n', out) is not None)
    edit(ACTION_PATH, 'HEAD, TAIL = 100, 300', 'HEAD, TAIL = 100, 301')
    check('release.sh refuses an action changed and not committed', release()[0] == 1)
    commit('the action changed after its pin')
    check('release.sh refuses an action changed after its pin', release()[0] == 1)
    pin(git('rev-parse', 'HEAD'))
    commit('pinned again')
    check('release.sh releases once the pin is the action\'s commit again', release()[0] == 0)
    with open(os.path.join(REPO, LEAN_PATH), 'a', encoding='utf-8') as f:
        f.write('      - uses: verificationalliance/verify/.github/actions/check@%s # workflow-7\n' % second)
    commit('the action run again, pinned at an earlier action')
    check('release.sh refuses the action run twice', release()[0] == 1)
    git('reset', '-q', '--hard', 'HEAD~1')
    pin(second)
    commit('pinned at a commit whose action differs')
    check('release.sh refuses a pin at an earlier action', release()[0] == 1)
    edit(LEAN_PATH, r'uses: verificationalliance/verify/\.github/actions/check@[0-9a-f]{40} # \S+',
         'uses: ./.github/actions/check')
    commit('the ./ form')
    check('release.sh refuses the action named by ./', release()[0] == 1)
finally:
    shutil.rmtree(TMP)

if failures:
    print('FAILED: ' + ', '.join(failures))
    sys.exit(1)
print('test_workflows: %d checks' % count)
