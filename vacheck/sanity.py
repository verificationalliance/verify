"""The sanity checks: signs that a claim says less than it reads.

Each warning is a fact. Four are read off the checked export; holds-for-any is the kernel's own
verdict, from the helper vacheck/sanity.lean:
- no-project-definition: the statement names none of the project's definitions;
- holds-for-any: the kernel accepts the developer's proof with a definition replaced by a variable
  of its type, so the claim holds whatever that definition is;
- always-true: a definition in the statement whose type ends in Prop and whose body, under its
  lambdas, is the constant True;
- ignores-argument: such a definition, not always true, whose body never uses one of its explicit
  arguments;
- unused-assumption: an explicit binder of the statement whose variable the proof's matching lambda
  never mentions. A proof that is not a lambda, or has fewer lambdas, is not judged past them.

A binder with no plain name (anonymous, or with macro scopes, as an arrow's hypothesis has) is
named None, and the report says "one of its ...". Warnings never fail a check. The helper's verdicts
are read as strictly as the export: anything but one well-formed verdict per pair, in order, is a
SanityError, never fewer warnings.
"""
import pkgutil

from .export import binders, body_constant, ends_in_prop, universe_params

# The most serious first: the order of a claim's warnings.
CHECKS = ('no-project-definition', 'holds-for-any', 'always-true', 'ignores-argument', 'unused-assumption')
MAX_WARNINGS = 10
VERDICTS = ('any', 'needed', 'skipped')  # what the helper says of one (theorem, definition) pair


class SanityError(Exception):
    pass


def source():
    """The helper's Lean source, vacheck/sanity.lean, as bytes. pkgutil reads it through the module's
    loader, so this works from inside vacheck.pyz too."""
    return pkgutil.get_data(__name__, 'sanity.lean')


def targets(export, theorems, defs):
    """The pairs the helper re-checks: for each theorem, in order, the names in defs[theorem], in
    order, that are definitions without universe parameters."""
    return [(t, tuple(d for d in defs[t] if export.kind(d) == 'def' and universe_params(export, d) == 0))
            for t in theorems]


def read_verdicts(text, targets):
    """Each theorem of targets -> the definitions its proof holds for any value of.

    text is exactly one line `<i> <j> <verdict>` per pair, in the order of targets: i indexes
    targets, j its definitions, both in decimal without leading zeros, and the verdict is one of
    VERDICTS. Anything else (a line short, extra, out of order, repeated, or of another shape) is a
    SanityError. Messages hold no text from the verdicts.
    """
    if type(text) is not str:
        raise SanityError('the verdicts are not text')
    pairs = [(i, j) for i, (_, ds) in enumerate(targets) for j in range(len(ds))]
    lines = text.split('\n')
    if lines.pop() != '':
        raise SanityError('the last line does not end with a line break')
    if len(lines) != len(pairs):
        raise SanityError('%d lines for %d pairs' % (len(lines), len(pairs)))
    found = {t: set() for t, _ in targets}
    for n, ((i, j), line) in enumerate(zip(pairs, lines), 1):
        pair = '%d %d ' % (i, j)
        verdict = line[len(pair):]
        if not line.startswith(pair) or verdict not in VERDICTS:
            raise SanityError('line %d is not a verdict for pair %d %d' % (n, i, j))
        if verdict == 'any':
            theorem, ds = targets[i]
            found[theorem].add(ds[j])
    return {t: frozenset(ds) for t, ds in found.items()}


def warnings(export, theorem, defs, any_defs):
    """The claim's warnings, each {'check', 'name', 'arg'}: in CHECKS order, then in the order of
    defs or of the statement's binders, and at most MAX_WARNINGS.

    defs are the project's definitions in the statement, as analyze lists them; any_defs, those of
    them the helper found the proof holds for any value of.
    """
    if not set(any_defs) <= set(defs):
        raise SanityError('a verdict names a definition the statement does not mention')
    found = {check: [] for check in CHECKS}
    if not defs:
        found['no-project-definition'].append((None, None))
    for d in defs:
        if d in any_defs:
            found['holds-for-any'].append((d, None))
        if export.kind(d) == 'def' and ends_in_prop(export, d):
            if body_constant(export, d) == 'True':
                found['always-true'].append((d, None))
            else:
                for arg, arg_info, arg_used in binders(export, d, 'value'):
                    if arg_info == 'default' and not arg_used:
                        found['ignores-argument'].append((d, arg))
    statement, proof = binders(export, theorem, 'type'), binders(export, theorem, 'value')
    for (name, info, _), (_, _, used_by_proof) in zip(statement, proof):
        if info == 'default' and not used_by_proof:
            found['unused-assumption'].append((name, None))
    return [{'check': check, 'name': name, 'arg': arg}
            for check in CHECKS for name, arg in found[check]][:MAX_WARNINGS]
