"""The sanity checks: signs that a claim says less than it reads.

Each warning is a fact. Four are read off the checked export; holds-for-any is the kernel's own
verdict, from the helper vacheck/sanity.lean:
- no-project-definition: the statement names none of the project's definitions;
- holds-for-any: the kernel accepts the developer's proof with a definition replaced by a variable
  of its type, so the claim holds whatever that definition is. It is tried only for a definition
  that no other constant of the statement reaches (targets);
- always-true: a definition in the statement whose type ends in Prop and whose body, under its
  lambdas, is the constant True;
- ignores-argument: such a definition, not always true, whose value never uses one of its explicit
  arguments;
- unused-assumption: an explicit binder of the statement that neither the rest of the statement nor
  the proof's matching lambda mentions. A proof that is not a lambda, or has fewer lambdas, is not
  judged past them.

Names are as the page prints them. leanexport shares one expression among those equal but for binder
names and binder info, so a declaration's type may carry another declaration's binder names, and
nanoda_bin prints a definition under its type's names (`def Pos (n a✝ : Nat)`) or, when it has an
implicit or instance argument, as `fun` over its value's (`fun {α} (m n : Nat) =>`). So a binder's
explicitness comes from the type and its use from the value, and an argument is named only when its
type and value name it alike. A binder name the page may not show (none, macro scopes, over MAX_NAME
characters, a character a report cannot show, an argument named differently, or an assumption the
caller's `shown` rejects) is None, and the report says "one of its ...". The binder walks of one claim share an export.Budget; past it, the claim gets no warning read
off binders, as the helper skips a re-check out of heartbeats. Warnings never fail a check.

The helper's verdicts are read as strictly as the export: anything but one well-formed verdict per
pair, in order, is a SanityError, never fewer warnings.
"""
import pkgutil

from .export import (Budget, OutOfSteps, binder_chain, binder_name, binder_uses, body_constant, constants_in_type,
                     ends_in_prop, reaches, universe_params)

# The most serious first: the order of a claim's warnings.
CHECKS = ('no-project-definition', 'holds-for-any', 'always-true', 'ignores-argument', 'unused-assumption')
MAX_WARNINGS = 10
MAX_NAME = 200  # the longest binder name a warning names; a longer one is None
VERDICTS = ('any', 'needed', 'skipped')  # what the helper says of one (theorem, definition) pair


class SanityError(Exception):
    pass


def source():
    """The helper's Lean source, vacheck/sanity.lean, as bytes. pkgutil reads it through the module's
    loader, so this works from inside vacheck.pyz too."""
    return pkgutil.get_data(__name__, 'sanity.lean')


def targets(export, theorems, defs, library=frozenset()):
    """The pairs the helper re-checks: for each theorem, in order, the names in defs[theorem], in
    order, that are definitions without universe parameters and that no other constant of the
    statement reaches (export.reaches, which takes no step from a name in `library`, the
    toolchain's).

    The helper replaces a definition only where the statement names it. Where another constant of
    the statement is made of it (`isHigh n := n > threshold` in `isHigh 20 = true`), the kernel may
    accept the proof with it replaced, yet the claim does not hold whatever it is: such a pair is never
    tried, and gives no warning."""
    out = []
    for t in theorems:
        stated = constants_in_type(export, t)
        out.append((t, tuple(d for d in defs[t] if export.kind(d) == 'def' and universe_params(export, d) == 0
                             and not reaches(export, stated - {d}, d, library))))
    return out


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


def warnings(export, theorem, defs, any_defs, shown=None):
    """The claim's warnings, each {'check', 'name', 'arg'}: in CHECKS order, then in the order of
    defs or of the statement's binders, and at most MAX_WARNINGS.

    defs are the project's definitions in the statement, as analyze lists them; any_defs, those of
    them the helper found the proof holds for any value of. shown, when given, takes the theorem, the
    position of one of its statement's binders (0 for the first) and that binder's name, and says
    whether the page shows that name for that binder; it is asked only about the assumptions the
    warnings would name.
    """
    if not set(any_defs) <= set(defs):
        raise SanityError('a verdict names a definition the statement does not mention')
    props = [d for d in defs if export.kind(d) == 'def' and ends_in_prop(export, d)]
    always = [d for d in props if body_constant(export, d) == 'True']
    found = {'no-project-definition': [] if defs else [(None, None)],
             'holds-for-any': [(d, None) for d in defs if d in any_defs],
             'always-true': [(d, None) for d in always]}
    try:
        budget = Budget()
        found['ignores-argument'] = [(d, arg) for d in props if d not in always for arg in _ignored(export, d, budget)]
        found['unused-assumption'] = [(h, None) for h in _unused(export, theorem, budget)]  # h: (position, binder)
    except OutOfSteps:
        found['ignores-argument'] = found['unused-assumption'] = []
    kept = [(check, name, arg) for check in CHECKS for name, arg in found[check]][:MAX_WARNINGS]
    return [{'check': check,
             'name': _named(export, name[1], shown, theorem, name[0]) if check == 'unused-assumption' else name,
             'arg': _named(export, arg) if check == 'ignores-argument' else arg}
            for check, name, arg in kept]


def _ignored(export, d, budget):
    """The explicit arguments of definition d that its value never uses, as binder handles: made
    explicit by d's type, used or not by its value, and None when the two name it differently."""
    params, uses = binder_chain(export, d, 'value'), binder_uses(export, d, 'value', budget)
    return [arg if arg == param else None
            for (arg, arg_info), (param, _), arg_used in zip(binder_chain(export, d, 'type'), params, uses)
            if arg_info == 'default' and not arg_used]


def _unused(export, theorem, budget):
    """The explicit binders of the statement that neither the rest of the statement nor the proof's
    matching lambda mentions, as (position, binder handle). A binder the statement mentions is what
    the claim is about, not an assumption: by proof irrelevance, the proof of `(h1 h2 : 1 = 1) :
    f h1 = f h2` may well mention only h1. The statement is walked only when the proof leaves a binder
    unused."""
    statement = binder_chain(export, theorem, 'type')
    proof = binder_uses(export, theorem, 'value', budget)
    unused = [k for k, ((_, info), used_by_proof) in enumerate(zip(statement, proof))
              if info == 'default' and not used_by_proof]
    if not unused:
        return []
    stated = binder_uses(export, theorem, 'type', budget)
    return [(k, statement[k][0]) for k in unused if not stated[k]]


def _named(export, binder, shown=None, declaration=None, position=None):
    """A binder's name for a warning, or None when there is none, it has no plain name, is longer
    than MAX_NAME, holds a character a report cannot show, or shown(declaration, position, name) is false."""
    # Imported here, not above: the result contract reads CHECKS from this module.
    from .result import hidden_character
    name = None if binder is None else binder_name(export, binder)
    if name is None or len(name) > MAX_NAME or hidden_character(name) is not None:
        return None
    return name if shown is None or shown(declaration, position, name) else None
