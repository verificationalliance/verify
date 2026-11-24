"""Checks a Lean export against the toolchain's reference and the manifest, and builds result.json.

Everything here is hostile data: the export comes from a job that ran the developer's code, and the
source tree is the developer's repository. The source is read as text only: symlinks are skipped,
symlinked folders are not entered, files over 2 MB are skipped, and nothing outside `project` is read
except the manifest file.
"""
import hashlib
import json
import os
import re
import stat

from . import VERSION
from .export import ExportError, axioms_of, constants_in_type, digest
from .manifest import _STRIP
from .result import ALLOWED_AXIOMS, SCHEMA, ResultError, validate_result

MAX_FILE = 2 * 1024 * 1024
MAX_DEFS = 20
MAX_LINE_TEXT = 160
MAX_REPLACED = 200  # the result contract's limit
LAKE_FILES = ('lakefile.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')
REPLACERS = ('implemented_by', 'extern', 'csimp')
_ALLOWED_TEXT = 'propext, Quot.sound and Classical.choice'
_KINDS = {'def': 'a definition', 'axiom': 'an axiom', 'opaque': 'an opaque definition',
          'inductive': 'an inductive type', 'ctor': 'a constructor', 'rec': 'a recursor',
          'quot': 'a quotient primitive'}
# A theorem declaration at the start of a line, after any attributes and modifiers. Group 1 is the
# name as written: dotted, with «» around components that are not identifiers. No two ways to match
# the same text, so a hostile file cannot make it backtrack.
_THEOREM = re.compile(
    r'^[^\S\n]*(?:@\[[^\]\n]*\][^\S\n]*)*'
    r'(?:(?:private|protected|public|noncomputable|nonrec|unsafe|partial)[^\S\n]+)*'
    r'theorem\s+((?:[^\s«(){}\[\]:⦃]|«[^»\n]*»)+)', re.MULTILINE)


class AnalysisError(Exception):
    pass


def analyze(export, reference, manifest, source_dir, repo, commit, toolchain, kernels, printer,
            manifest_path='.verificationalliance.json'):
    """result.json for the manifest's claims, or AnalysisError with a message for the developer's log.

    `reference` is the toolchain's own export of (at least) the library names that `export` uses.
    `manifest_path` is where the manifest file is, relative to `source_dir`, the repository root.
    """
    theorems = [c.theorem for c in manifest.claims]
    try:
        # 1. The claimed theorems exist, and are theorems.
        for t in theorems:
            kind = export.kind(t)
            if kind is None:
                raise AnalysisError('%s is not in the export' % t)
            if kind != 'theorem':
                raise AnalysisError('%s is %s, not a theorem' % (t, _KINDS.get(kind, kind)))
        # 2. Every name the export shares with the toolchain's library is the library's own
        # declaration. A digest names the constants a declaration uses without covering them, so
        # every shared name is compared, not only those the claimed theorems mention.
        library = reference.names()
        for name in sorted(export.names() & library):
            if digest(export, name) != digest(reference, name):
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
        defs = {t: sorted(c for c in constants_in_type(export, t) if c not in library)[:MAX_DEFS]
                for t in theorems}
    except ExportError as e:
        raise AnalysisError('the export cannot be read: %s' % e) from None

    # 4 and 5. Statements and definitions as printed from the checked export.
    wanted = list(dict.fromkeys(theorems + [d for t in theorems for d in defs[t]]))
    printed = printer(wanted)
    if not isinstance(printed, dict) or not all(isinstance(printed.get(n), str) for n in wanted):
        raise AnalysisError('the printer did not print every declaration')

    # 6 to 8. The source, as text, one file at a time in path order.
    project_dir, prefix = _project(source_dir, manifest.project)
    lasts = {_last_component(t) for t in theorems}
    sources = {}
    replaced = []
    hashes = {}
    for rel, data in _lean_files(project_dir, prefix):
        hashes[rel] = _sha256(data)
        text = data.decode('utf-8', errors='replace')
        line, pos = 1, 0
        for m in _THEOREM.finditer(text):
            line += text.count('\n', pos, m.start())
            pos = m.start()
            last = _last_component(m.group(1))
            if last in lasts and last not in sources:
                sources[last] = {'path': rel, 'line': line}
        for i, raw in enumerate(text.split('\n'), 1):
            plain = _STRIP.sub('', raw)
            if any(w in plain for w in REPLACERS):
                if len(replaced) == MAX_REPLACED:
                    raise AnalysisError('more than %d lines use implemented_by, extern or csimp' % MAX_REPLACED)
                replaced.append({'path': rel, 'line': i, 'text': plain.strip()[:MAX_LINE_TEXT]})
    for name in LAKE_FILES:
        data = _read(os.path.join(project_dir, name))
        if data is not None:
            hashes[_join(prefix, name)] = _sha256(data)
    hashes.update(_manifest_file(source_dir, manifest_path))
    # The digest of the JSON array of [path, sha256 of the file] pairs, sorted.
    build_digest = _sha256(json.dumps(sorted(hashes.items()), separators=(',', ':')).encode())

    claims = []
    for c in manifest.claims:
        claims.append({
            'says': c.says,
            'theorem': c.theorem,
            'about': c.about,
            'statement': _plain(printed[c.theorem]),
            'defs': [{'name': _plain(d), 'text': _plain(printed[d])} for d in defs[c.theorem]],
            'axioms': axioms[c.theorem],
            'source': sources.get(_last_component(c.theorem)),
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


def _plain(text):
    """Text without control or bidi characters, line breaks kept."""
    return '\n'.join(_STRIP.sub('', line) for line in text.split('\n'))


def _last_component(name):
    """The last component of a Lean name as written, without its «»."""
    if name.endswith('»'):
        i = name.rfind('«')
        if i >= 0:
            return name[i + 1:-1]
    return name.rsplit('.', 1)[-1]


def _sha256(data):
    return hashlib.sha256(data).hexdigest()


def _join(prefix, rel):
    return prefix + '/' + rel if prefix else rel


def _parts(rel, what):
    """The components of a path relative to the repository root; AnalysisError if it could leave it."""
    if not isinstance(rel, str) or rel.startswith('/') or '\\' in rel:
        raise AnalysisError('%s must be a relative path inside the repository' % what)
    parts = [p for p in rel.split('/') if p not in ('', '.')]
    if '..' in parts:
        raise AnalysisError('%s must be a relative path inside the repository' % what)
    return parts


def _walk_in(source_dir, parts, what):
    """The path of `parts` under source_dir. None of them may be a symlink."""
    path = source_dir
    for p in parts:
        path = os.path.join(path, p)
        if os.path.islink(path):
            raise AnalysisError('%s is a symlink' % what)
    return path


def _project(source_dir, project):
    """The project folder, and its path relative to the repository root ('' for the root)."""
    parts = _parts(project, 'project')
    path = _walk_in(source_dir, parts, 'project %s' % project)
    if not os.path.isdir(path):
        raise AnalysisError('project %s is not a folder in the repository' % project)
    return path, '/'.join(parts)


def _manifest_file(source_dir, manifest_path):
    """{relpath: sha256} of the manifest file, which must be a regular file of at most 2 MB."""
    parts = _parts(manifest_path, 'the manifest path')
    data = _read(_walk_in(source_dir, parts, 'the manifest file'))
    if not parts or data is None:
        raise AnalysisError('the manifest file %s is not a regular file of at most 2 MB' % manifest_path)
    return {'/'.join(parts): _sha256(data)}


def _read(path):
    """The bytes of a regular file of at most 2 MB, never through a symlink; None otherwise."""
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except OSError:
        return None
    with os.fdopen(fd, 'rb') as f:
        st = os.fstat(f.fileno())
        if not stat.S_ISREG(st.st_mode) or st.st_size > MAX_FILE:
            return None
        data = f.read(MAX_FILE + 1)
    return data if len(data) <= MAX_FILE else None


def _plain_path(rel):
    try:
        rel.encode('utf-8')
    except UnicodeEncodeError:
        return False
    return '\\' not in rel and not _STRIP.search(rel)


def _lean_files(project_dir, prefix):
    """(relpath, bytes) of every .lean file under the project outside .lake folders, in path order,
    read one at a time."""
    paths = []
    for dirpath, dirnames, filenames in os.walk(project_dir):
        dirnames[:] = [d for d in dirnames if d != '.lake' and not os.path.islink(os.path.join(dirpath, d))]
        for name in filenames:
            if name.endswith('.lean'):
                path = os.path.join(dirpath, name)
                paths.append((_join(prefix, os.path.relpath(path, project_dir).replace(os.sep, '/')), path))
    paths.sort()
    for rel, path in paths:
        data = _read(path)
        if data is None:
            continue
        if not _plain_path(rel):
            raise AnalysisError('the file name %s is not plain text' % ascii(rel))
        yield rel, data
