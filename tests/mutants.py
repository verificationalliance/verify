"""Mutants for vacheck: each breaks one rule by one exact text replacement, and the tests must fail.

Each mutant runs in a fresh copy of the whole repository (but .git and build folders), so tests that
read .github or the fixtures run as they do here. An unchanged copy runs first, and every test script
the mutants use must pass on it: otherwise no mutant counts. Mutants run one at a time.

MUTANTS are caught by tests/test_vacheck.py; CLI_MUTANTS, which break the sanity helper or the command
line, by tests/test_cli.py, which builds and runs them (it needs the toolchain, as in ci).

    python3 -I tests/mutants.py

prints `mutants: n/N caught`, and exits 1 when one is not caught, when its text is not in its file
exactly once, or when the unchanged copy fails. A mutant is caught only when a check prints FAIL: a
test script that crashes or runs out of time proves nothing about the rule, and is reported as
`crashed` or `timed out`, not caught.
"""
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VACHECK, CLI = 'tests/test_vacheck.py', 'tests/test_cli.py'
SANITY, EXPORT, RESULT, ANALYZE = 'vacheck/sanity.py', 'vacheck/export.py', 'vacheck/result.py', 'vacheck/analyze.py'
TIMEOUT = {VACHECK: 600, CLI: 1800}  # seconds

# (file, what is broken, text in that file, replacement)
MUTANTS = [
    # The checks.
    (SANITY, 'no-project-definition never fires',
     "'no-project-definition': [] if defs else [(None, None)],", "'no-project-definition': [],"),
    (SANITY, 'holds-for-any ignores the verdicts',
     "'holds-for-any': [(d, None) for d in defs if d in any_defs],", "'holds-for-any': [(d, None) for d in defs],"),
    (SANITY, 'always-true accepts any constant body',
     "body_constant(export, d) == 'True'", "body_constant(export, d) is not None"),
    (SANITY, 'ignores-argument counts implicit binders',
     "if arg_info == 'default' and not arg_used]", "if not arg_used]"),
    (SANITY, 'unused-assumption counts implicit binders',
     "if info == 'default' and not used_by_proof]", "if not used_by_proof]"),
    (SANITY, "unused-assumption reads use from the statement's binders instead of the proof's",
     "proof = binder_uses(export, theorem, 'value', budget)", "proof = binder_uses(export, theorem, 'type', budget)"),
    (EXPORT, 'a binder with a _@ component keeps its name',
     "None if not comps or '_@' in comps else", "None if not comps else"),
    (SANITY, 'at most 10 warnings: no cap',
     "for check in CHECKS for name, arg in found[check]][:MAX_WARNINGS]",
     "for check in CHECKS for name, arg in found[check]]"),
    (SANITY, 'a verdict for a definition the statement does not mention is accepted',
     'if not set(any_defs) <= set(defs):', 'if False:'),
    # The helper's verdicts.
    (SANITY, 'read_verdicts accepts a missing pair', 'if len(lines) != len(pairs):', 'if len(lines) > len(pairs):'),
    (SANITY, 'read_verdicts accepts an unknown word', 'or verdict not in VERDICTS:', 'or not verdict:'),
    (SANITY, 'read_verdicts accepts a last line without its line break',
     "if lines.pop() != '':", "if lines.pop() != '' and False:"),
    # The pairs: definitions without universe parameters, that no other constant of the statement
    # reaches, by each kind of step.
    (SANITY, 'targets keep a definition with universe parameters', " and universe_params(export, d) == 0", ""),
    (SANITY, 'targets keep a definition another constant of the statement reaches',
     "\n                             and not reaches(export, stated - {d}, d, library)", ""),
    (EXPORT, 'reach takes no step through values',
     "[d.fields['type']] if d.kind == 'theorem' else d.exprs()", "[d.fields['type']]"),
    (EXPORT, "reach steps through a theorem's value",
     "[d.fields['type']] if d.kind == 'theorem' else d.exprs()", "d.exprs()"),
    (EXPORT, 'reach takes no step between the members of an inductive block',
     "nxt.update(m['name'] for key, _ in _MEMBERS for m in d.block[key])", "nxt.update(())"),
    (EXPORT, "reach takes no step between a mutual block's definitions",
     "nxt.update(d.fields['all'])", "nxt.update(())"),
    (EXPORT, 'reach takes no step from a _mutual or _unary helper to its definition',
     'if comp in _HELPERS and pre in env._decls:', 'if False:'),
    (EXPORT, 'reach steps into the library',
     "        if library and env._render(c) in library:\n            continue\n", ""),
    (EXPORT, 'a name the export does not have reaches nothing',
     "if goal is None or None in todo:\n        return True", "if goal is None or None in todo:\n        return False"),
    # Names as the page prints them.
    (SANITY, 'an ignored argument is named by its type even when its value names it otherwise',
     'return [arg if arg == param else None', 'return [arg if True else None'),
    (SANITY, "an ignored argument's explicitness comes from the value",
     "for (arg, arg_info), (param, _), arg_used in", "for (arg, _), (param, arg_info), arg_used in"),
    (SANITY, "an unused assumption is named by the proof's lambda",
     "return [(k, statement[k][0]) for k in unused if not stated[k]]",
     "return [(k, binder_chain(export, theorem, 'value')[k][0]) for k in unused if not stated[k]]"),
    (SANITY, 'an assumption the rest of the statement mentions is judged',
     "return [(k, statement[k][0]) for k in unused if not stated[k]]",
     "return [(k, statement[k][0]) for k in unused]"),
    (SANITY, 'shown is not asked', "return name if shown is None or shown(declaration, position, name) else None",
     "return name"),
    (SANITY, 'a name over 200 characters is kept', "len(name) > MAX_NAME", "len(name) > MAX_NAME + 1"),
    (SANITY, 'a name with a character a report cannot show is kept', " or hidden_character(name) is not None", ""),
    (EXPORT, "only a binder name's last component is rendered", "else env._render(binder)", "else str(comps[-1])"),
    (ANALYZE, 'an assumption is named wherever its name is printed before the colon',
     "lambda d, k, n: before_colon[d][k:k + 1] == (n,))", "lambda d, k, n: n in before_colon[d])"),
    (ANALYZE, 'a binder printed without a name takes no place', "            names.append(None)", "            pass"),
    (ANALYZE, "a printed binder's type is read as names", "group[1:colon[0] + 1]", "group[1:-1]"),
    (ANALYZE, 'brackets that do not match are read', " or group[-1] != _BRACKETS[group[0]]", ""),
    # Binders in linear time, within a budget.
    (EXPORT, 'a lambda does not shift its body',
     "bits = loose[node[2]] | (loose[node[3]] >> 1)", "bits = loose[node[2]] | loose[node[3]]"),
    (EXPORT, 'a let does not shift its body',
     "bits = loose[node[2]] | loose[node[3]] | (loose[node[4]] >> 1)",
     "bits = loose[node[2]] | loose[node[3]] | loose[node[4]]"),
    (EXPORT, 'the steps are not counted', "        budget.spend(1)\n", "        budget.spend(0)\n"),
    (SANITY, 'out of steps, the warnings of the earlier walks are kept',
     "    except OutOfSteps:\n        found['ignores-argument'] = found['unused-assumption'] = []\n",
     "    except OutOfSteps:\n        found.setdefault('ignores-argument', [])\n"
     "        found.setdefault('unused-assumption', [])\n"),
    (SANITY, 'out of steps, the other checks are dropped too',
     "    except OutOfSteps:\n        found['ignores-argument'] = found['unused-assumption'] = []\n",
     "    except OutOfSteps:\n        found = {c: [] for c in CHECKS}\n"),
    (EXPORT, 'fields lets OutOfSteps escape',
     "    try:\n        _loose(env, d.fields['type'], budget)\n    except OutOfSteps:\n        return None\n",
     "    _loose(env, d.fields['type'], budget)\n"),
    (ANALYZE, "each constructor has a budget of its own, not one for its type's",
     "lines = [_constructor(export, c, printed[c], budget) for c in ctors[name]]",
     "lines = [_constructor(export, c, printed[c]) for c in ctors[name]]"),
    # The result.
    (ANALYZE, "the helper's verdicts are ignored",
     "else sanity.read_verdicts(verdicts, pairs))", "else {t: frozenset() for t in theorems})"),
    (RESULT, 'validate_result accepts an unknown check',
     "        if not isinstance(check, str) or check not in CHECKS:\n            _fail('unknown warning check')\n"
     "        if CHECKS.index(check) < last:\n            _fail('warnings out of order')\n"
     "        last = CHECKS.index(check)\n",
     "        if not isinstance(check, str):\n            _fail('unknown warning check')\n"
     "        if check in CHECKS and CHECKS.index(check) < last:\n            _fail('warnings out of order')\n"
     "        last = CHECKS.index(check) if check in CHECKS else last\n"),
    (RESULT, 'validate_result accepts 11 warnings',
     "_list(ws, 'warnings', 0, MAX_WARNINGS)", "_list(ws, 'warnings', 0, MAX_WARNINGS + 1)"),
    (RESULT, 'validate_result accepts a template', "    if c['template'] is not None:", "    if False:"),
    (RESULT, 'validate_result accepts warnings out of order', "        if CHECKS.index(check) < last:", "        if False:"),
    (RESULT, 'validate_result accepts a binder name over 200 characters',
     "        _str(v, what, MAX_NAME)", "        _str(v, what)"),
    (RESULT, "validate_result caps a definition's name at 200 characters",
     "            _str(w['name'], 'warning name')", "            _str(w['name'], 'warning name', MAX_NAME)"),
    # The result says whether the helper ran to the end.
    (RESULT, 'validate_result accepts any value of sanity',
     "if not isinstance(obj['sanity'], str) or obj['sanity'] not in SANITY:", "if False:"),
    (ANALYZE, 'a stopped helper is recorded as complete',
     "        sanity_reached = 'stopped'\n", "        sanity_reached = 'complete'\n"),
    (ANALYZE, 'a skipped pair is recorded as complete',
     "        sanity_reached = 'partial'\n", "        sanity_reached = 'complete'\n"),
    (ANALYZE, 'a result is partial without a skipped pair',
     "        sanity_reached = 'complete'\n", "        sanity_reached = 'partial'\n"),
    (RESULT, 'validate_result refuses partial', "SANITY = ('complete', 'partial', 'stopped')", "SANITY = ('complete', 'stopped')"),
]

CLI_MUTANTS = [
    ('vacheck/sanity.lean', 'the helper replays the whole export, not what its pairs need',
     'replay (map.filter fun n _ => needed.contains n)', 'replay map'),
    ('vacheck/sanity.lean', 'the replay has no budget',
     'maxHeartbeats.set {} replayHeartbeats', 'maxHeartbeats.set {} 0'),
    ('vacheck/sanity.lean', 'the helper never stops at its total budget',
     'if spent < totalHeartbeats * 1000 then', 'if true then'),
    (ANALYZE, 'a stopped helper is read as a helper that gave no verdict',
     "holds_for_any = ({t: frozenset() for t in theorems} if verdicts is None",
     "holds_for_any = (sanity.read_verdicts('', pairs) if verdicts is None"),
    ('vacheck/__main__.py', 'analyze takes --abstracted and --sanity-stopped together',
     'sanity_step = p.add_mutually_exclusive_group(required=True)', 'sanity_step = p.add_argument_group()'),
]

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


def copy():
    """A fresh copy of the repository, without .git and build folders."""
    tmp = tempfile.mkdtemp(prefix='vacheck-mutant-')
    repo = os.path.join(tmp, 'repo')
    shutil.copytree(ROOT, repo, symlinks=True,
                    ignore=shutil.ignore_patterns('.git', '.lake', 'dist', '__pycache__'))
    return tmp, repo


def run(repo, test):
    """(exit code, the first failing check) of a test script in the copy."""
    try:
        p = subprocess.run([sys.executable, '-I', os.path.join(repo, test)], capture_output=True, text=True,
                           stdin=subprocess.DEVNULL, timeout=TIMEOUT[test])
    except subprocess.TimeoutExpired:
        return 'timeout', None
    fails = [line[6:] for line in p.stdout.splitlines() if line.startswith('FAIL  ')]
    return p.returncode, fails[0] if fails else None


def mutated(path, old, new):
    """A copy of the repository with old replaced by new in path; None if old is not there exactly once."""
    with open(os.path.join(ROOT, path), encoding='utf-8') as f:
        text = f.read()
    if text.count(old) != 1:
        return None
    tmp, repo = copy()
    with open(os.path.join(repo, path), 'w', encoding='utf-8') as f:
        f.write(text.replace(old, new))
    return tmp, repo


def main():
    sys.stdout.reconfigure(line_buffering=True)  # a line as each mutant ends, in a long ci step
    lists = [(VACHECK, MUTANTS), (CLI, CLI_MUTANTS)]
    tmp, repo = copy()
    try:
        baseline = {test: run(repo, test) for test, ms in lists if ms}
    finally:
        shutil.rmtree(tmp)
    for test, (code, first) in baseline.items():
        check('%s passes on the unchanged copy' % test, code == 0)
        if code != 0:
            print('      exit %s, first failure: %s' % (code, first))
    if failures:
        print('mutants: none counted, the unchanged copy fails')
        return 1
    caught = total = 0
    for test, ms in lists:
        for path, what, old, new in ms:
            total += 1
            made = mutated(path, old, new)
            if made is None:
                check('%s: its text is in %s exactly once' % (what, path), False)
                continue
            tmp, repo = made
            try:
                code, first = run(repo, test)
            finally:
                shutil.rmtree(tmp)
            if first is not None and code not in (0, 'timeout'):
                status = 'caught'
            elif code == 'timeout':
                status = 'timed out'
            else:
                status = 'crashed' if code != 0 else 'survived'
            check('%s is caught' % what, status == 'caught')
            if status == 'caught':
                caught += 1
                print('      by %s' % first)
            else:
                print('      %s (exit %s)' % (status, code))
    print('mutants: %d/%d caught' % (caught, total))
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
