"""Checks a Lean export against the toolchain's reference and the manifest, and builds result.json.

Everything here is hostile data: the export comes from a job that ran the developer's code, and the
checkout is the developer's repository. Nothing in it is run; its files are only hashed or read as
text, never through a symlink. The build digest covers every file in the checkout but its .git, a
symlink by where it points (one into the project, or a symlinked .lean or Lake file, is an error, as is
one pointing outside the checkout), and a committed .lake in the project folder is an error. Only the project's .lean files of at most 2 MiB,
outside any folder named .lake or .git, are read as text. Messages name things from the export and
the manifest, so each goes through text.log_line.

What the result publishes must be shown as it is: a name, a statement or a sentence that holds a
character a report cannot show (a control or format character, a line or paragraph separator, a
surrogate; a line break is allowed in a statement and a definition's text) is rejected, so the
checker and the server agree on every result.
"""
import errno
import hashlib
import json
import os
import posixpath
import re
import stat

from . import VERSION
from .export import (Budget, ExportError, axioms_of, constants_in_type, constructors, digest, fields, parameters,
                     value_constants)
from .manifest import _STRIP
from .result import ALLOWED_AXIOMS, SCHEMA, ResultError, describe, hidden_character, validate_result
from .text import log_line

MAX_FILE = 2 * 1024 * 1024  # the largest .lean file read as text
MAX_TOTAL = 512 * 1024 * 1024  # the most bytes hashed for the build digest
_CHUNK = 1024 * 1024
MAX_DEFS = 20
MAX_LINE_TEXT = 160
MAX_REPLACED = 200  # the result contract's limit
LAKE_FILES = ('lakefile.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')
# Folders whose files are hashed for the build digest but never read as text: Lake's build and
# package folders, and git's.
UNREAD = ('.lake', '.git')
_SYMLINK = 'symlinks are not supported in v1: '
REPLACERS = ('implemented_by', 'extern', 'csimp')
_ALLOWED_TEXT = 'propext, Quot.sound and Classical.choice'
_KINDS = {'def': 'a definition', 'axiom': 'an axiom', 'opaque': 'an opaque definition',
          'inductive': 'an inductive type', 'ctor': 'a constructor', 'rec': 'a recursor',
          'quot': 'a quotient primitive'}
class AnalysisError(Exception):
    """A rejection, with a message for the developer's log, made safe for it by log_line."""

    def __init__(self, message):
        super().__init__(log_line(message))


def analyze(export, reference, manifest, source_dir, repo, commit, toolchain, kernels, printer, manifest_path):
    """result.json for the manifest's claims, or AnalysisError with a message for the developer's log.

    `reference` is the toolchain's own export of (at least) the library names that `export` uses, or
    a list of such exports, one per library of the toolchain: a name is the library's when any of
    them declares it, and must then be identical to every one that does.
    `source_dir` is the checkout, and `manifest_path` the manifest file's path inside it.
    """
    references = list(reference) if isinstance(reference, (list, tuple)) else [reference]
    theorems = [c.theorem for c in manifest.claims]
    _shown(manifest.project, 'the project folder %s' % manifest.project)
    for s in manifest.ships:
        _shown(s, 'the shipped target %s' % s)
    for c in manifest.claims:
        _shown(c.theorem, 'the theorem name %s' % c.theorem)
        _shown(c.says, 'what the claim on %s says' % c.theorem)
    try:
        # 1. The claimed theorems exist, and are theorems.
        check_theorems(export, theorems)
        # 2. Every name the export shares with the toolchain's library is the library's own
        # declaration. A digest names the constants a declaration uses without covering them, so
        # every shared name is compared, not only those the claimed theorems mention.
        library = frozenset().union(*(r.names() for r in references))
        for name in sorted(export.names() & library):
            mine = digest(export, name)
            if any(name in r.names() and digest(r, name) != mine for r in references):
                raise AnalysisError("%s differs from the toolchain's %s" % (name, name))
        # 3. No axioms but the allowed three.
        axioms = {}
        for t in theorems:
            axioms[t] = sorted(axioms_of(export, t))
            for ax in axioms[t]:
                if ax not in ALLOWED_AXIOMS:
                    hint = ' (native_decide)' if '._native.native_decide.' in ax else ''
                    raise AnalysisError('%s depends on the axiom %s%s; only %s are allowed'
                                        % (t, ax, hint, _ALLOWED_TEXT))
        # And those three only as the library declares them: an axiom the reference lacks was not
        # compared in step 2, and a project can declare its own `propext`.
        for t in theorems:
            for ax in axioms[t]:
                if ax not in library:
                    raise AnalysisError("%s depends on %s, which is not in the toolchain's reference"
                                        % (t, ax))
        # 5. The project's own constants in each type: those the library does not have.
        defs = project_constants(export, references, theorems)
    except ExportError as e:
        raise AnalysisError('the export cannot be read: %s' % e) from None

    # 4 and 5. Statements and definitions as printed from the checked export, and the constructors
    # of an inductive type among the definitions, to show them with it.
    names = list(dict.fromkeys(theorems + [d for t in theorems for d in defs[t]]))
    try:
        ctors = {d: constructors(export, d) for d in names if export.kind(d) == 'inductive'}
    except ExportError as e:
        raise AnalysisError('the export cannot be read: %s' % e) from None
    wanted = list(dict.fromkeys(names + [c for cs in ctors.values() for c in cs]))
    printed = printer(wanted)
    if not isinstance(printed, dict) or not all(isinstance(printed.get(n), str) for n in wanted):
        raise AnalysisError('the printer did not print every declaration')
    try:
        shown, terms = {}, {}
        for n in names:
            text, term = (printed[n], None) if n in theorems else _definition(export, n, printed, ctors)
            shown[n], terms[n] = _hygiene(text), None if term is None else _capped(_hygiene(term))
    except ExportError as e:
        raise AnalysisError('the export cannot be read: %s' % e) from None

    # 6 to 8. One file at a time, in path order. Steps 6 and 7 read the project's .lean files of at
    # most 2 MiB as text; step 8 hashes every build input in the checkout.
    project_dir, prefix = _project(source_dir, manifest.project)
    manifest_rel, manifest_file = _manifest_file(source_dir, manifest_path)
    declared = {}
    replaced = []
    hashes = {}
    total = 0
    for rel, path, target in _build_inputs(source_dir, prefix) + [(manifest_rel, manifest_file, None)]:
        if rel in hashes:
            continue
        if target is not None:                     # a symlink counts by where it points, never followed
            size, data = len(target.encode('utf-8', errors='surrogateescape')), None
            if size > MAX_TOTAL - total:
                raise AnalysisError('the build inputs (every file in the checkout and the manifest) are larger than 512 MiB in total')
            hashes[rel] = [rel, 'link', target]
        else:
            sha, size, data, mode = _hash(path, rel, MAX_TOTAL - total, _read_as_text(rel, prefix))
            hashes[rel] = [rel, 'file', mode, sha]
        total += size
        if data is None:
            continue
        if not _plain_path(rel):
            raise AnalysisError('the file name %s is not plain text' % rel)
        text = data.decode('utf-8', errors='replace')
        for comps, line in declarations(text):
            declared.setdefault(comps, set()).add((rel, line))
        for i, raw in enumerate(text.split('\n'), 1):
            plain = _STRIP.sub('', raw)
            if any(w in plain for w in REPLACERS):
                if len(replaced) == MAX_REPLACED:
                    raise AnalysisError('more than %d lines use implemented_by, extern or csimp' % MAX_REPLACED)
                replaced.append({'path': rel, 'line': i, 'text': _visible(raw).strip()[:MAX_LINE_TEXT]})
    # The digest of the JSON array of typed entries, sorted by path: [path, "file", git mode, sha256 of
    # the file] (mode 100755 when its owner may run it, else 100644) and [path, "link", target].
    build_digest = _sha256(json.dumps(sorted(hashes.values()), separators=(',', ':')).encode())

    def source(name):
        """Where the source declares `name`: the one declaration whose full name, from the namespaces
        around it, is `name`; None if there is none, or more than one."""
        found = declared.get(components(name), ())
        if len(found) != 1:
            return None
        (path, line), = found
        return {'path': path, 'line': line}

    claims = []
    for c in manifest.claims:
        _shown(shown[c.theorem], 'the statement of %s' % c.theorem, newlines=True)
        for d in defs[c.theorem]:
            _shown(d, 'the definition name %s' % d)
            _shown(shown[d], 'the text of %s' % d, newlines=True)
            if terms[d] is not None:
                _shown(terms[d], 'the checked term of %s' % d, newlines=True)
        claims.append({
            'says': c.says,
            'theorem': c.theorem,
            'about': c.about,
            'statement': shown[c.theorem],
            'defs': [{'name': d, 'text': shown[d], 'source': source(d), 'term': terms[d]} for d in defs[c.theorem]],
            'axioms': axioms[c.theorem],
            'source': source(c.theorem),
        })
    result = {
        'schema': SCHEMA,
        'repo': repo,
        'commit': commit,
        'toolchain': toolchain,
        'checker': VERSION,
        'project': manifest.project,
        'build_digest': build_digest,
        'claims': claims,
        'evidence': {'ships': list(manifest.ships), 'replaced': replaced},
        'kernels': list(kernels),
    }
    try:
        validate_result(result)
    except ResultError as e:
        raise AnalysisError('the result is not valid: %s' % e) from None
    return result


def check_theorems(export, theorems):
    """AnalysisError unless each name is a theorem of the export."""
    for t in theorems:
        kind = export.kind(t)
        if kind is None:
            raise AnalysisError('%s is not in the export' % t)
        if kind != 'theorem':
            raise AnalysisError('%s is %s, not a theorem' % (t, _KINDS.get(kind, kind)))


def project_constants(export, references, theorems):
    """Each theorem -> the project's own constants that its type mentions, those that no reference
    declares: sorted, and at most MAX_DEFS. These are a claim's `defs`, and the definitions the sanity
    helper re-checks. ExportError if the export cannot be read."""
    library = frozenset().union(*(r.names() for r in references))
    return {t: sorted(c for c in constants_in_type(export, t) if c not in library)[:MAX_DEFS]
            for t in theorems}


# An import at the start of a line or after a comment, with its modifiers. Group 1 is the module's
# first component as written, in «» or not.
_IMPORT = re.compile(r'(?:^|-/)[^\S\n]*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(«[^»\n]*»|[^\s.«]+)',
                     re.MULTILINE)


def import_roots(source_dir, project):
    """The first component of every module that the project's .lean files import (Lean for
    `import Lean.Data.Json`), sorted: the libraries of the toolchain that the project may use.

    The files are those analyze reads as text, read the same way. Imports are plain syntax at the top
    of a file, which no macro can make. This takes every line that starts like one (after spaces, or
    after a comment's closing -/), wherever it is in the file, even inside a comment: it may name more
    libraries than the project imports, so more names are compared, not fewer."""
    _, prefix = _project(source_dir, project)
    roots = set()
    total = 0
    for rel, path, target in _build_inputs(source_dir, prefix):
        if target is not None or not _read_as_text(rel, prefix):
            continue
        _, size, data, _ = _hash(path, rel, MAX_TOTAL - total, True)
        total += size
        if data is not None:
            for m in _IMPORT.finditer(data.decode('utf-8', errors='replace')):
                root = m.group(1)
                roots.add(root[1:-1] if root.startswith('«') else root)
    return sorted(roots)


def _read_as_text(rel, prefix):
    """Whether steps 6 and 7 read a build input as text: a .lean file of the project, outside any
    folder named .lake or .git."""
    return (rel.endswith('.lean') and (not prefix or rel.startswith(prefix + '/'))
            and not any(p in UNREAD for p in rel.split('/')[:-1]))


def _shown(text, what, newlines=False):
    """AnalysisError if text holds a character that a report cannot show."""
    c = hidden_character(text, newlines)
    if c is not None:
        raise AnalysisError('%s holds the character %s, which a report cannot show' % (what, describe(c)))


def _visible(line):
    """A source line as the report can show it: tabs as spaces, other hidden characters removed."""
    if hidden_character(line) is None:
        return line
    return ''.join(' ' if c == '\t' else c for c in line if c == '\t' or hidden_character(c) is None)


# How the source declares names. Steps 6 and 7 read Lean files as text, so a declaration is found by
# its full name: the namespaces open around it and the name it is declared with. Comments, strings
# and character literals are blanked out first, keeping line breaks, so nothing in them counts.
_SPECIAL = re.compile('«|--|/-|"|\'|(?<![\\w\'!?.])r#*"')
_NESTED = re.compile(r'/-|-/')
_STRING = re.compile(r'"[^"\\]*(?:\\.[^"\\]*)*"', re.DOTALL)
_CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]{1,6}\}|[^\n])|[^\\'\n])'")
_NAME = r'(?:[^\s«(){}\[\]:⦃,]|«[^»\n]*»)+'
_ATTRS = r'(?:@\[[^\]\n]*\][^\S\n]*)*'
_MODIFIERS = r'(?:(?:private|protected|public|noncomputable|nonrec|unsafe|partial|scoped|local)[^\S\n]+)*'
_WORD_END = r'(?![^\s(])'
# A command at the start of a line: namespace, section, mutual, end, or a declaration after any
# attributes and modifiers. No two ways to match the same text, so a hostile file cannot make it
# backtrack.
_COMMAND = re.compile(
    r'^[^\S\n]*(?:'
    r'namespace[^\S\n]+(?P<namespace>' + _NAME + ')'
    r'|' + _ATTRS + _MODIFIERS + r'(?P<section>section)(?:[^\S\n]+(?P<section_name>' + _NAME + '))?' + _WORD_END +
    r'|(?P<mutual>mutual)' + _WORD_END +
    r'|(?P<end>end)(?:[^\S\n]+(?P<end_name>' + _NAME + '))?' + _WORD_END +
    r'|' + _ATTRS + r'(?P<modifiers>' + _MODIFIERS + ')'
    r'(?:theorem|lemma|def|abbrev|structure|inductive|class(?:[^\S\n]+inductive)?|opaque|axiom|instance)'
    r'[^\S\n]+(?P<declared>' + _NAME + '))', re.MULTILINE)


def _mask(text):
    """(masked, first): the text with its comments (nested /- -/ too), strings, raw strings and
    character literals blanked out, line breaks kept, «» names kept as they are; and where the first
    « with no » on its line is (len(text) when there is none)."""
    out = []
    i, n = 0, len(text)
    first = n
    unclosed = -1  # up to here, a « has no » on its line, and nor has any after it on that line
    while True:
        m = _SPECIAL.search(text, i)
        if m is None:
            out.append(text[i:])
            return ''.join(out), first
        start = m.start()
        out.append(text[i:start])
        token = m.group()
        if token == '«':
            if start < unclosed:
                out.append(token)
                i = start + 1
                continue
            newline = text.find('\n', start + 1)
            newline = n if newline < 0 else newline
            end = text.find('»', start + 1, newline)
            if end < 0:
                unclosed = newline
                first = min(first, start)
                out.append(token)
                i = start + 1
                continue
            out.append(text[start:end + 1])
            i = end + 1
            continue
        if token == '--':
            end = text.find('\n', start)
            end = n if end < 0 else end
        elif token == '/-':
            depth, end = 1, n
            for t in _NESTED.finditer(text, start + 2):
                depth += 1 if t.group() == '/-' else -1
                if not depth:
                    end = t.end()
                    break
        elif token == "'":
            lit = _CHAR_LITERAL.match(text, start)
            if lit is None or (start and re.match(r"[\w'!?.]", text[start - 1])):
                out.append(token)
                i = start + 1
                continue
            end = lit.end()
        elif token == '"':
            lit = _STRING.match(text, start)
            end = n if lit is None else lit.end()
        else:  # r"...", r#"..."#
            close = '"' + token[1:-1]
            end = text.find(close, m.end())
            end = n if end < 0 else end + len(close)
        out.append(re.sub('[^\n]', ' ', text[start:end]))
        i = end


def components(name):
    """The components of a Lean name as written (`A.«b c».d`), without «»; None if it is not one."""
    out = []
    i, n = 0, len(name)
    while i < n:
        if name.startswith('«', i):
            j = name.find('»', i + 1)
            if j < 0:
                return None
            comp, i = name[i + 1:j], j + 1
        else:
            j = name.find('.', i)
            j = n if j < 0 else j
            comp, i = name[i:j], j
            if '«' in comp or '»' in comp:
                return None
        if not comp:
            return None
        out.append(comp)
        if i < n:
            if name[i] != '.' or i + 1 == n:
                return None
            i += 1
    return tuple(out) or None


def declarations(text):
    """(components of the full name, line) of each declaration in Lean source text, from the
    namespaces open around it: `theorem b` inside `namespace A` is A.b, and `_root_.b` is b. A
    private declaration is left out (Lean gives it another name). From an `end` that closes nothing,
    or not what is open, on, nothing more is found in the file: its names are not certain; nor after
    `#exit` (anywhere outside comments and strings: Lean stops at `end A #exit` too, and at `x#exit`),
    after which Lean reads nothing, nor after a « with no » on its line. Stopping early costs only a
    link that is then null."""
    masked, unclosed = _mask(text)
    stop = masked.find('#exit')
    masked = masked[:min(unclosed, stop if stop >= 0 else len(masked))]
    scopes = []  # (kind, name): ('namespace', components), ('section', text or None), ('mutual', None)
    out = []
    line, pos = 1, 0
    for m in _COMMAND.finditer(masked):
        line += masked.count('\n', pos, m.start())
        pos = m.start()
        if m.group('namespace') is not None:
            comps = components(m.group('namespace'))
            if comps is None:
                return out
            scopes.append(('namespace', comps))
        elif m.group('section') is not None:
            scopes.append(('section', m.group('section_name')))
        elif m.group('mutual') is not None:
            scopes.append(('mutual', None))
        elif m.group('end') is not None:
            name = m.group('end_name')
            closes = scopes[-1] if scopes else None
            if closes is None or closes[0] == 'namespace' and (name is None or components(name) != closes[1]) \
                    or closes[0] == 'section' and name != closes[1] or closes[0] == 'mutual' and name is not None:
                return out
            scopes.pop()
        elif 'private' not in m.group('modifiers').split():
            declared = m.group('declared')
            comps = components(declared[:-1] if declared.endswith('.') else declared)  # theorem t.{u}
            if comps is None:
                continue
            if comps[0] == '_root_':
                full = comps[1:]
            else:
                full = tuple(c for kind, name in scopes if kind == 'namespace' for c in name) + comps
            if full:
                out.append((full, line))
    return out


# How a definition is shown: as nanoda_bin prints it from the checked export, never from the source,
# with three changes that only make it readable. An inductive type is shown with its constructors. A
# definition compiled through recursors or match auxiliaries (structural or well-founded recursion,
# `match`) is shown by its header, the name and the type, since its body is the compiled term; that
# term, in full (cut at MAX_TEXT, saying so), goes beside it as the definition's `term`. And a name with macro scopes, which Lean gives a variable a
# macro made (x._@.Mod._hyg.21), is shown as Lean shows it, x✝, numbered if two differ.
COMPILED_NOTE = '(body compiled; the checked term is below)'
_MORE_CHARS = '\n\u2026 %d more characters'
_COMPILED = re.compile(r'(?:^|\.)(?:brecOn|binductionOn|below|rec|recOn|casesOn|match_\d+|_f|_unary|_mutual)$')
_HYGIENIC = re.compile(r"(?<![^\s(){}\[\]⟨⟩⦃⦄,:@])([^\W\d][\w'!?]*(?:\.(?!_@\.)[^\W\d][\w'!?]*)*)"
                       r"\._@\.[\w'!?.]*?\._hyg\.\d+(?![\w'!?.])")
_DAGGER = '✝'
_SUPERSCRIPT = str.maketrans('0123456789', '⁰¹²³⁴⁵⁶⁷⁸⁹')
_OPENING, _CLOSING = '([{⟨⦃', ')]}⟩⦄'
WIDTH = 100
MAX_TEXT = 4000  # the result contract's limit on a definition's text
_MORE = '\n  \u2026 and %d more'


def _hygiene(text):
    """The text with each name that has macro scopes shown as its name and ✝, then a superscript
    number for the second and later different ones with the same name."""
    seen = {}

    def shown(m):
        same = seen.setdefault(m.group(1), {})
        k = same.setdefault(m.group(0), len(same))
        return m.group(1) + _DAGGER + (str(k).translate(_SUPERSCRIPT) if k else '')
    return _HYGIENIC.sub(shown, text)


def _depth_zero(text, stop):
    """The positions in text where `stop` starts outside any bracket, skipping «» names; None when the
    text has a string in it or its brackets do not balance, so that where things are is not certain."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        c = text[i]
        if c == '«':
            j = text.find('»', i + 1)
            if j < 0:
                return None
            i = j + 1
            continue
        if c == '"':
            return None
        if c in _OPENING:
            depth += 1
        elif c in _CLOSING:
            depth -= 1
            if depth < 0:
                return None
        elif depth == 0 and text.startswith(stop, i):
            out.append(i)
        i += 1
    return out if depth == 0 else None


def _flat(text):
    """Line breaks nanoda_bin put in, with the indent around them, as one space."""
    return re.sub(r'[^\S\n]*\n\s*', ' ', text)


def _header(text):
    """A definition as nanoda_bin prints it, `def <name> <binders> : <type> := <value>`, as its header,
    `def <name> <binders> : <type>`; None when it is not certain where the header ends: before the
    first `:=` outside brackets, if no `let` comes before it."""
    stops = _depth_zero(text.split(':=', 1)[0] + ':=', ':=') if ':=' in text else None
    if not stops:
        return None
    head = text[:stops[0]].rstrip()
    if re.search(r"(?<![\w'!?.])let\s", head):
        return None
    flat = _flat(head)
    return flat if len(flat) <= WIDTH and '«' not in head else head


def _unwrap(part):
    """A part in one pair of brackets, `(Nat -> Nat)`, without them."""
    if part.startswith('(') and part.endswith(')') and _depth_zero(part[1:-1], ')') == []:
        return part[1:-1]
    return part


def _constructor(export, ctor, text, budget=None):
    """A constructor as Lean's #print shows one: its name, then (field : type) for each field, then the
    type it makes, from nanoda_bin's `constructor <name> : <type> -> ... -> <type>` and the fields'
    names in the export. As nanoda_bin prints it, without the keyword, when that is not certain: a
    parameter, a field another depends on, a field that is not explicit or has no plain name, or
    fields past the budget."""
    shown = text[len('constructor '):] if text.startswith('constructor ') else text
    name, sep, rest = shown.partition(' : ')
    fs = fields(export, ctor, budget)
    if not sep or not fs or parameters(export, ctor) or re.search(r'[\s(){}\[\]⦃]', name) \
            or not all(f is not None and info == 'default' and not dep for f, info, dep in fs):
        return shown
    stops = _depth_zero(rest, '→')
    if stops is None or len(stops) != len(fs) or _depth_zero(rest, ',') != []:
        return shown
    cuts = [-1] + stops + [len(rest)]
    parts = [_unwrap(_flat(rest[a + 1:b]).strip()) for a, b in zip(cuts, cuts[1:])]
    if any(not p or re.match(r'(?:forall|fun|let)\b|∀|λ', p) for p in parts):
        return shown
    groups = []
    for (field, _, _), t in zip(fs, parts):
        if groups and groups[-1][1] == t:
            groups[-1][0].append(field)
        else:
            groups.append(([field], t))
    binders = ['(%s : %s)' % (' '.join(names), t) for names, t in groups]
    one = ' '.join([name] + binders) + ' : ' + parts[-1]
    if len(one) <= WIDTH - 2:
        return one
    return '\n  '.join([name] + binders[:-1] + [binders[-1] + ' : ' + parts[-1]])


def _definition(export, name, printed, ctors):
    """(text, term) for one of the project's definitions (see above): the text shown, at most MAX_TEXT
    characters when it is made of more than nanoda_bin's text; and the checked term, nanoda_bin's whole
    text, when the text shows less of it (a compiled definition), else None."""
    text = printed[name]
    kind = export.kind(name)
    if kind == 'inductive':
        budget = Budget()  # one for all its constructors, so their number does not multiply it
        lines = [_constructor(export, c, printed[c], budget) for c in ctors[name]]
        if not lines:
            return text, None
        out = text + '\n' + ('constructor:' if len(lines) == 1 else 'constructors:')
        for i, line in enumerate(lines):
            item = '\n  ' + line.replace('\n', '\n  ')
            left = len(lines) - i - 1
            if len(out) + len(item) + (len(_MORE % left) if left else 0) > MAX_TEXT:
                return out + _MORE % (left + 1), None
            out += item
        return out, None
    if kind == 'def' and any(_COMPILED.search(c) or c.startswith('WellFounded.') for c in value_constants(export, name)):
        head = _header(text)
        if head is not None:
            return head + '\n  ' + COMPILED_NOTE, text
    return text, None


def _capped(term):
    """A checked term of at most MAX_TEXT characters: cut, ending with how many characters were left out."""
    if len(term) <= MAX_TEXT:
        return term
    keep = MAX_TEXT - len(_MORE_CHARS % len(term))
    return term[:keep] + _MORE_CHARS % (len(term) - keep)


def _sha256(data):
    return hashlib.sha256(data).hexdigest()


def _join(prefix, rel):
    return prefix + '/' + rel if prefix else rel


def _parts(rel, what):
    """The components of a path relative to the checkout; AnalysisError if it could leave it."""
    if not isinstance(rel, str) or rel.startswith('/') or '\\' in rel:
        raise AnalysisError('%s must be a relative path inside the repository' % what)
    parts = [p for p in rel.split('/') if p not in ('', '.')]
    if '..' in parts:
        raise AnalysisError('%s must be a relative path inside the repository' % what)
    return parts


def _walk_in(source_dir, parts):
    """The path of `parts` under source_dir. None of them may be a symlink."""
    path = source_dir
    for i, p in enumerate(parts):
        path = os.path.join(path, p)
        if os.path.islink(path):
            raise AnalysisError(_SYMLINK + '/'.join(parts[:i + 1]))
    return path


def _project(source_dir, project):
    """The project folder, and its path relative to the checkout ('' for the root)."""
    parts = _parts(project, 'project')
    path = _walk_in(source_dir, parts)
    if not os.path.isdir(path):
        raise AnalysisError('project %s is not a folder in the repository' % project)
    return path, '/'.join(parts)


def _manifest_file(source_dir, manifest_path):
    """The manifest file's path relative to the checkout, and its path."""
    parts = _parts(manifest_path, 'the manifest path')
    if not parts:
        raise AnalysisError('the manifest path names no file')
    return '/'.join(parts), _walk_in(source_dir, parts)


def _build_inputs(source_dir, prefix):
    """(relpath, path, link) of every build input in the checkout, in path order: every file, outside the
    root .git (a lakefile can build from anywhere in it, ../ included, and put its buildDir there).
    `link` is None for a file. A project folder that holds .lake raises: Lake builds there, so a
    committed one could hand the build files that are not hashed.

    Symlinks are never followed, and are checked by their real path (see _link): a symlink counts by
    its target as written (`link`), and only a symlink to a file of the checkout may stand."""
    lake = _join(prefix, '.lake')
    if os.path.lexists(os.path.join(source_dir, *lake.split('/'))):
        raise AnalysisError('%s is in the repository: Lake builds there, so it must not be committed '
                            '(add .lake to .gitignore)' % lake)
    skip = {'.git', lake}

    def fail(e):
        raise AnalysisError('cannot list %s' % os.path.relpath(e.filename or source_dir, source_dir))

    out = []
    for dirpath, dirnames, filenames in os.walk(source_dir, onerror=fail):
        here = os.path.relpath(dirpath, source_dir)
        here = '' if here == os.curdir else here.replace(os.sep, '/')
        kept = []
        for d in dirnames:
            rel = _join(here, d)
            if rel in skip:
                continue
            path = os.path.join(dirpath, d)
            if os.path.islink(path):
                _link(source_dir, rel, path, prefix)       # raises for every folder: why, if it can tell
                raise AnalysisError('a symlink to a folder: %s' % rel)
            kept.append(d)
        dirnames[:] = kept
        for name in filenames:
            rel = _join(here, name)
            path = os.path.join(dirpath, name)
            if os.path.islink(path):
                out.append((rel, path, _link(source_dir, rel, path, prefix)))
            else:
                out.append((rel, path, None))
    out.sort()
    return out


def _link(source_dir, rel, path, prefix):
    """The target, as written, of a symlink that may stand as a build input: outside the project folder,
    neither a .lean nor a Lake file, and to an existing regular file of the checkout, outside .git, by
    its real path, which must be the checkout's real path joined with where the target reads. Anything
    else raises: what it points at could be compiled, or is not what the digest hashes (a folder
    symlink on the way, `up -> .`, makes ../../up/../core/x read as core/x and be ../core/x)."""
    name = rel.rsplit('/', 1)[-1]
    if not prefix or rel == prefix or rel.startswith(prefix + '/') or name.endswith('.lean') or name in LAKE_FILES:
        raise AnalysisError(_SYMLINK + rel)
    try:
        target = os.readlink(path)
    except OSError:
        raise AnalysisError('cannot read %s' % rel) from None
    root, real = os.path.realpath(source_dir), os.path.realpath(path)
    inside = os.path.relpath(real, root).replace(os.sep, '/')
    if os.path.isabs(target) or inside == '..' or inside.startswith('../'):
        raise AnalysisError('a symlink points outside the repository: %s' % rel)
    if inside == '.git' or inside.startswith('.git/'):
        raise AnalysisError('a symlink points into .git: %s' % rel)
    if os.path.isdir(real):
        raise AnalysisError('a symlink to a folder: %s' % rel)
    if not os.path.lexists(real):
        raise AnalysisError('a symlink points at nothing: %s' % rel)
    reads = posixpath.normpath(posixpath.join(posixpath.dirname(rel), target.replace(os.sep, '/')))
    if reads != inside:
        raise AnalysisError('a symlink points outside the repository: %s' % rel)
    if not stat.S_ISREG(os.stat(path).st_mode):
        raise AnalysisError('a symlink to something that is not a regular file: %s' % rel)
    return target


def _hash(path, rel, budget, as_text):
    """(sha256, size, text, mode) of a regular file, read in chunks and never through a symlink. `text`
    is its bytes if as_text and it is at most 2 MiB, else None; `mode` its git mode, 100755 when its
    owner may run it, else 100644. More than `budget` bytes raises."""
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except OSError as e:
        raise AnalysisError(_SYMLINK + rel if e.errno == errno.ELOOP else 'cannot read %s' % rel) from None
    with os.fdopen(fd, 'rb') as f:
        st = os.fstat(f.fileno())
        if not stat.S_ISREG(st.st_mode):
            raise AnalysisError('%s is not a regular file' % rel)
        h = hashlib.sha256()
        size = 0
        text = [] if as_text else None
        while True:
            chunk = f.read(_CHUNK)
            if not chunk:
                break
            size += len(chunk)
            if size > budget:
                raise AnalysisError('the build inputs (every file in the checkout and the manifest) '
                                    'are larger than 512 MiB in total')
            h.update(chunk)
            if text is not None and size <= MAX_FILE:
                text.append(chunk)
            else:
                text = None
    return (h.hexdigest(), size, None if text is None else b''.join(text),
            '100755' if st.st_mode & stat.S_IXUSR else '100644')


def _plain_path(rel):
    try:
        rel.encode('utf-8')
    except UnicodeEncodeError:
        return False
    return '\\' not in rel and hidden_character(rel) is None
