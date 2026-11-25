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

# The checker both files download is the release of this repository's vacheck, at its version.
sys.path.insert(0, ROOT)
from vacheck import VERSION  # noqa: E402


def other_versions(urls, version):
    url = 'https://github.com/verificationalliance/verify/releases/download/v%s/vacheck.pyz' % version
    return [u for u in urls if u != url]


URLS = lean_constants.get('VACHECK_URL', []) + action_constants.get('VACHECK_URL', [])
check('VACHECK_URL is the release of vacheck.VERSION, in both files',
      len(URLS) == 2 and other_versions(URLS, VERSION) == [])
check('... another version is found', other_versions(URLS, VERSION + '.1') != [])

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


# Every run: step of the action runs in the shell lean.yml's jobs run in, written out: a composite
# action has no defaults.
def default_shell(lines):
    m = re.search(r'^defaults:\n  run:\n    shell: (.+)$', '\n'.join(lines), re.MULTILINE)
    return m.group(1) if m else None


def action_steps(lines):
    """The action's steps, each as its lines: from one `    - ` to the next."""
    steps, step = [], None
    for line in lines:
        if line.startswith('    - '):
            step = [line]
            steps.append(step)
        elif step is not None and (not line.strip() or indent(line) > 4):
            step.append(line)
        elif step is not None and line.strip() and not line.lstrip().startswith('#'):
            step = None
    return steps


def wrong_shells(lines, shell):
    """The steps with a run: whose shell: is not exactly `shell`, by their first line."""
    out = []
    for step in action_steps(lines):
        runs = step[0].startswith('    - run:') or any(line.startswith('      run:') for line in step)
        shells = [line[len('      shell: '):] for line in step if line.startswith('      shell: ')]
        if runs and shells != [shell]:
            out.append(step[0].strip())
    return out


SHELL = default_shell(lean)
check('lean.yml runs its jobs in bash --noprofile --norc -euo pipefail',
      SHELL == 'bash --noprofile --norc -euo pipefail {0}')
check("every run: step of the action has lean.yml's shell, exactly",
      len(action_steps(action)) > 10 and wrong_shells(action, SHELL) == [])
first_shell = action.index('      shell: ' + SHELL) if '      shell: ' + SHELL in action else 0
check('... a step with another shell, or none, is found',
      wrong_shells([line.replace('shell: bash --noprofile', 'shell: bash --profile', 1) for line in action], SHELL)
      and wrong_shells(action[:first_shell] + action[first_shell + 1:], SHELL))


# No run: script holds ${{ }}: an expression is written into the script before bash reads it, so an
# input or a name would be read as code. Inputs reach a script through env: only.
def run_blocks(lines):
    """The text of every run: in the file: its inline value, or the lines of its block."""
    out = []
    for i, line in enumerate(lines):
        m = re.fullmatch(r'( *)(- )?run:(.*)', line)
        if not m:
            continue
        key = len(m.group(1)) + (2 if m.group(2) else 0)
        value = m.group(3).strip()
        if value == '' or re.fullmatch(r'[|>][-+0-9]*', value):
            body = []
            for line2 in lines[i + 1:]:
                if line2.strip() and indent(line2) <= key:
                    break
                body.append(line2)
            out.append('\n'.join(body))
        else:
            out.append(value)
    return out


def expression_in_run(lines):
    return [b for b in run_blocks(lines) if '${{' in b]


check('no run: script in lean.yml or the action holds ${{',
      len(run_blocks(lean)) > 5 and len(run_blocks(action)) > 10
      and expression_in_run(lean) == [] and expression_in_run(action) == [])
check('... an expression in a run: script is found, a block or one line',
      expression_in_run([line.replace('va="$RUNNER_TEMP/va"', 'va="${{ runner.temp }}/va"', 1) for line in action])
      and expression_in_run(lean + ['      - run: echo ${{ inputs.manifest }}']))
check('... and in a block of any style: >-, |+, |2, >',
      all(expression_in_run(lean + ['      - run: %s' % style, '          echo ${{ inputs.manifest }}'])
          for style in ('>-', '|+', '|2', '>')))


# The schema the attestation is made for is vacheck's result schema, wherever a file names one.
sys.path.insert(0, ROOT)
from vacheck.result import SCHEMA  # noqa: E402
SCHEMA_URL = re.compile(r'https://verificationalliance\.org/attestations/proof-check/v[0-9]+')
SELFTEST = os.path.join(ROOT, '.github', 'workflows', 'selftest.yml')


def schemas(lines):
    return SCHEMA_URL.findall('\n'.join(lines))


selftest = lines_of(SELFTEST)
check('lean.yml signs under result.SCHEMA, selftest verifies under it, and the action names it',
      any(line.strip() == 'predicate-type: ' + SCHEMA for line in lean)
      and any(line.strip() == '--predicate-type %s \\' % SCHEMA for line in selftest)
      and all(schemas(f) and set(schemas(f)) == {SCHEMA} for f in (lean, selftest, action)))
check('... another schema is found',
      set(schemas([line.replace(SCHEMA, SCHEMA[:-1] + '1') for line in lean])) != {SCHEMA})


# The sanity helper and sanity-targets read the export, so each runs only in the sandbox, under the
# step's limits (`limited`), with the export bound read-only, and with its output and its messages
# in files, never in the log. Their commands are read with continued lines joined.
def commands(script):
    out, held = [], ''
    for line in script.split('\n'):
        if line.endswith('\\'):
            held += line[:-1]
            continue
        out.append(held + line)
        held = ''
    return out


# Each tool as the action runs it: what may start it after the sandbox's --, and what the sandbox
# must bind read-only.
SANDBOXED = {'"$work/sanity"': ('', ('--ro "$export_file"', '--ro "$work/targets.jsonl"')),
             '"$va/vacheck.pyz" sanity-targets': ('/usr/bin/python3 -I ', ('--ro "$export_file"',))}


def unsandboxed(lines):
    """Problems with how the action runs the helper and sanity-targets; [] if none, and each runs."""
    problems, runs = [], {tool: 0 for tool in SANDBOXED}
    for script in run_blocks(lines):
        for command in commands(script):
            words = ' '.join(command.split())
            for tool, (launcher, binds) in SANDBOXED.items():
                for m in re.finditer(re.escape(tool), words):
                    before = words[:m.start()]
                    if before.endswith('--ro '):
                        continue  # bound for the sandbox, not run
                    runs[tool] += 1
                    sandbox, sep, started = before.rpartition(' -- ')
                    after = words[m.end():]
                    if not (sep and started == launcher and re.match(r'(.* )?limited "\$va/sandbox" ', sandbox + ' ')
                            and all(b in sandbox for b in binds)):
                        problems.append('%s runs outside the limited sandbox, or without its export' % tool)
                    if not (re.search(r' > "[^"]+"', after) and re.search(r' 2> "[^"]+"', after)):
                        problems.append('%s writes to the log' % tool)
    return problems + ['%s never runs' % t for t, n in runs.items() if n == 0]


check('the sanity helper and sanity-targets run only in the limited sandbox, their output in files',
      unsandboxed(action) == [])


def edited(old, new):
    text = '\n'.join(action)
    if text.count(old) != 1:
        return None
    return text.replace(old, new).split('\n')


for what, old, new in (
        ('the helper run without the sandbox', 'limited "$va/sandbox" --ro "$lean" --ro "$work/sanity"',
         'true --ro "$lean" --ro "$work/sanity"'),
        ('the helper run without its limits', 'limited "$va/sandbox" --ro "$lean"', '"$va/sandbox" --ro "$lean"'),
        ('the helper run without the export', '--ro "$work/targets.jsonl" --ro "$export_file"',
         '--ro "$work/targets.jsonl"'),
        ('the helper run a second time', '        touch "$va/sanity-done"\n',
         '        "$work/sanity" "$work/targets.jsonl" "$export_file" > "$va/again" 2> "$work/again.log"\n'
         '        touch "$va/sanity-done"\n'),
        ("the helper's messages in the log", '> "$va/verdicts" 2> "$work/sanity.log"', '> "$va/verdicts"'),
        ('sanity-targets run without the sandbox',
         '-- /usr/bin/python3 -I "$va/vacheck.pyz" sanity-targets', '; /usr/bin/python3 -I "$va/vacheck.pyz" sanity-targets'),
        ('sanity-targets run again, by another python3', '        python3 -I "$va/vacheck.pyz" sanity-source',
         '        python3 -I "$va/vacheck.pyz" sanity-targets --export "$export_file" > "$work/t" 2> "$work/t.log"\n'
         '        python3 -I "$va/vacheck.pyz" sanity-source'),
        ("sanity-targets' output in the log", '> "$work/targets.jsonl" 2> "$work/targets.log"', '2> "$work/targets.log"')):
    broken = edited(old, new)
    check('... %s is found' % what, broken is not None and unsandboxed(broken) != [])



# limited, the sanity step's scope: as root, systemd-run makes the scope (8 GiB, no swap), then setpriv
# makes the tool this user, with this user's group and no other (systemd-run --uid keeps root's), then
# timeout ends it at the deadline. Its body is pinned, and its test comes before any tool runs under it.
LIMITED = ['local left=$((deadline - SECONDS))', '(( left > 0 )) || return 124',
           'sudo systemd-run --scope --quiet --collect -p MemoryMax=8G -p MemorySwapMax=0 -- setpriv '
           '--reuid="$(id -u)" --regid="$(id -g)" --clear-groups -- timeout -k 10 "$left" "$@"']
SANITY_STEP = 'Test which definitions each proof needs'


def limited_problems(lines):
    """What is wrong with limited and its test in the sanity step; [] if nothing."""
    script = run_script(lines, SANITY_STEP)
    if script is None:
        return ['no sanity step']
    problems = []
    cmds = [' '.join(c.split()) for c in commands(script)]
    starts = [i for i, c in enumerate(cmds) if c == 'limited() {']
    if len(starts) != 1 or sum('limited()' in c for c in cmds) != 1:
        return ['limited is not defined once']
    end = cmds.index('}', starts[0])
    if cmds[starts[0] + 1:end] != LIMITED:
        problems.append('limited is not as pinned')
    test = [i for i, c in enumerate(cmds) if c.startswith('if [[ " $(limited id -G) " != " $(id -g) " ]]')]
    first_tool = [i for i, c in enumerate(cmds) if c.startswith('limited "$va/sandbox" --ro "$va/vacheck.pyz"')]
    if not (len(test) == 1 and first_tool and test[0] < first_tool[0]
            and '|| limited "$va/sandbox" --ro "$probe/root-group" -- /bin/cat "$probe/root-group"' in cmds[test[0]]
            and '-- /bin/bash "$probe/probe.sh" "$probe/given"' in cmds[test[0]] and cmds[test[0] + 2] == 'exit 1'):
        problems.append("limited's test of the groups does not come first, or does not fail the check")
    return problems


check('limited is as pinned, and its test of the groups comes first and fails the check', limited_problems(action) == [])
for what, old, new in (
        ('limited keeping the groups', ' --clear-groups -- timeout', ' -- timeout'),
        ('limited without setpriv', '-- setpriv --reuid="$(id -u)" --regid="$(id -g)" --clear-groups -- timeout',
         '-- timeout'),
        ('limited by systemd-run --uid',
         '            -- setpriv --reuid="$(id -u)" --regid="$(id -g)" --clear-groups -- timeout',
         '            --uid="$(id -u)" --gid="$(id -g)" -- timeout'),
        ('limited without the memory cap', '-p MemoryMax=8G -p MemorySwapMax=0', '-p MemorySwapMax=0'),
        ('limited without the deadline', ' -- timeout -k 10 "$left" "$@"', ' -- "$@"'),
        ('no test of the groups', '        if [[ " $(limited id -G) " != " $(id -g) " ]] \\\n', '        if false \\\n'),
        ("the sandbox's test run from $RUNNER_TEMP, which binds it into the sandbox",
         'limited "$va/sandbox" --ro "$probe/given" --ro "$probe/probe.sh" -- /bin/bash "$probe/probe.sh"',
         'limited "$va/sandbox" --ro "$probe/given" --ro "$va/probe.sh" -- /bin/bash "$va/probe.sh"'),
        ('a test of the groups that does not fail the check',
         'or the sandbox does not isolate them."\n          exit 1', 'or the sandbox does not isolate them."\n          true')):
    broken = edited(old, new)
    check('... %s is found' % what, broken is not None and limited_problems(broken) != [])


# The marker: the helper's verdicts reach Analyze only after a clean exit of the helper, this run.
MARKER_CHECK = ['sanity=(--sanity-stopped)', 'if [[ -e "$va/sanity-done" ]]; then',
                'sanity=(--abstracted "$va/verdicts")', 'fi']


def marker_problems(lines):
    script, analyze = run_script(lines, SANITY_STEP), run_script(lines, 'Analyze')
    if script is None or analyze is None:
        return ['no sanity step or Analyze']
    problems = []
    cmds = [' '.join(c.split()) for c in commands(script)]
    marks = [i for i, c in enumerate(cmds) if 'sanity-done' in c]
    calls = [i for i, c in enumerate(cmds) if re.search(r'(^|[|&!(;] *)limited ', c)]
    if not marks or cmds[marks[0]] != 'rm -f "$va/sanity-done"' or not calls or marks[0] > calls[0]:
        problems.append('the marker is not removed first')
    touches = [i for i in marks if cmds[i] == 'touch "$va/sanity-done"']
    helper = [i for i, c in enumerate(cmds) if ' -- "$work/sanity" ' in c]
    if (len(marks) != 2 or len(touches) != 1 or len(helper) != 1 or touches[0] != helper[0] + 1
            or not cmds[helper[0]].endswith('|| stopped "the helper exited with $?" "$work/sanity.log"')):
        problems.append('the marker is not made only right after a clean exit of the helper')
    acmds = [' '.join(c.split()) for c in commands(analyze)]
    at = [i for i in range(len(acmds)) if acmds[i:i + 4] == MARKER_CHECK]
    if len(at) != 1 or sum(c.count('--abstracted') for b in run_blocks(lines) for c in commands(b)) != 1:
        problems.append('--abstracted is passed outside the marker check')
    return problems


check('the marker: removed first, made only after a clean exit of the helper, read before --abstracted',
      marker_problems(action) == [])
for what, old, new in (
        ('a marker not removed first', '        rm -f "$va/sanity-done"\n', ''),
        ('a marker never made', '        touch "$va/sanity-done"\n', ''),
        ('a marker made before the helper runs', '        # Exit 124 is the deadline',
         '        touch "$va/sanity-done"\n        # Exit 124 is the deadline'),
        ('a marker made even when the helper fails',
         '\n          || stopped "the helper exited with $?" "$work/sanity.log"', ' || true'),
        ('--abstracted outside the marker check',
         'sanity=(--sanity-stopped)\n        if [[ -e "$va/sanity-done" ]]; then\n'
         '          sanity=(--abstracted "$va/verdicts")\n        fi',
         'sanity=(--abstracted "$va/verdicts")'),
        ('--abstracted passed again', '          "${sanity[@]}" \\\n',
         '          "${sanity[@]}" --abstracted "$va/verdicts" \\\n')):
    broken = edited(old, new)
    check('... %s is found' % what, broken is not None and marker_problems(broken) != [])


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


def release(*args):
    r = subprocess.run(['bash', os.path.join(REPO, 'scripts', 'release.sh')] + list(args or [os.path.join(TMP, 'dist')]),
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
    check('release.sh --check-only refuses it too', release('--check-only')[0] == 1)
    pin(first)
    second = commit('pinned at the commit before')
    check('release.sh --check-only accepts the pin, and builds nothing',
          release('--check-only') == (0, '') and not os.path.exists(os.path.join(TMP, 'dist')))
    code, out = release()
    check('release.sh releases a pin whose action is the release commit\'s, and prints the sha256',
          code == 0 and re.fullmatch(r'[0-9a-f]{64}  \S+vacheck\.pyz\n', out) is not None)
    # It builds what HEAD holds: a change not committed is not released.
    with open(os.path.join(REPO, 'vacheck', '__init__.py'), 'a', encoding='utf-8') as f:
        f.write('# not committed\n')
    check('release.sh builds HEAD, not a change to vacheck/ that is not committed', release() == (code, out))
    git('checkout', '--', 'vacheck/__init__.py')
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
