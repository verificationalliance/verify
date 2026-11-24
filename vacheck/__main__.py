"""The command line that the workflow runs, as `python3 -I vacheck.pyz <command> ...`.

    toolchain <lean-toolchain>       prints `<url> <sha256>` of the toolchain's release tarball
    deps <lake-manifest.json>        accepts a project without dependencies
    modules <manifest>               prints the project folder, then the modules, one per line
    analyze --export F --reference F --manifest F --source D --repo R --commit C --toolchain V
            --kernels K,K --nanoda PATH
                                     prints result.json
    validate <result.json>           prints the result's canonical JSON

Exit codes: 0 ok, 1 rejected, 2 misuse. Every message is one line on stderr, for the developer's log:
no control or bidi characters, and no `::`, so that no text from the repository can become a GitHub
workflow command. JSON goes to stdout canonical: sorted keys, no spaces, UTF-8, no final newline.
"""
import argparse
import errno
import json
import os
import re
import secrets
import stat
import subprocess
import sys
import tempfile

from . import toolchain as _toolchain
from .analyze import AnalysisError, analyze
from .export import ExportError, load_export
from .manifest import MAX_BYTES as MANIFEST_BYTES, ManifestError, parse_manifest
from .result import ALLOWED_AXIOMS, MAX_BYTES as RESULT_BYTES, ResultError, validate_result

LEAN = 'leanprover/lean4:'
_UNSAFE = re.compile('[\u0000-\u001f\u007f-\u009f‎‏  ‪-‮⁦-⁩]+')


class Rejected(Exception):
    """Exit 1 with this message."""


class Misuse(Exception):
    """Exit 2 with this message."""


def _one_line(msg):
    line = _UNSAFE.sub(' ', str(msg)).strip()
    while '::' in line:
        line = line.replace('::', ': :')
    return line


def _canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=False)


def _out(text):
    try:
        data = text.encode('utf-8')
    except UnicodeEncodeError:
        raise Rejected('the output is not valid Unicode') from None
    sys.stdout.buffer.write(data)
    sys.stdout.buffer.flush()


def _read(path, limit, what):
    """Up to limit + 1 bytes of a regular file, never through a symlink."""
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except OSError as e:
        if e.errno == errno.ELOOP:
            raise Rejected('%s is a symlink' % what) from None
        raise Rejected('cannot read %s: %s' % (what, e.strerror or e)) from None
    with os.fdopen(fd, 'rb') as f:
        if not stat.S_ISREG(os.fstat(f.fileno()).st_mode):
            raise Rejected('%s is not a regular file' % what)
        return f.read(limit + 1)


def _unsupported():
    return 'v1 supports Lean v4.35.0 or later from: ' + ', '.join(_toolchain.versions())


def _manifest(path):
    try:
        return parse_manifest(_read(path, MANIFEST_BYTES, 'the manifest'))
    except ManifestError as e:
        raise Rejected(e) from None


def _export(path, what):
    try:
        return load_export(path)
    except OSError as e:
        raise Rejected('cannot read %s: %s' % (what, e.strerror or e)) from None
    except ExportError as e:
        raise Rejected('%s cannot be read: %s' % (what, e)) from None


def toolchain(args):
    text = _read(args.file, 1024, 'lean-toolchain').decode('utf-8', errors='replace').strip()
    found = _toolchain.lookup(text[len(LEAN):] if text.startswith(LEAN) else text)
    if found is None:
        raise Rejected(_unsupported())
    _out('%s %s\n' % (found.url, found.sha256))


def deps(args):
    data = _read(args.file, 1024 * 1024, 'lake-manifest.json')
    try:
        obj = json.loads(data.decode('utf-8'))
    except (UnicodeDecodeError, ValueError, RecursionError):
        raise Rejected('lake-manifest.json is not valid JSON') from None
    packages = obj.get('packages') if isinstance(obj, dict) else None
    if not isinstance(packages, list):
        raise Rejected('lake-manifest.json has no list of packages')
    if packages:
        raise Rejected('v1 supports projects without dependencies')


def modules(args):
    m = _manifest(args.file)
    _out(''.join(line + '\n' for line in (m.project,) + m.modules))


def _nanoda_name(name):
    """A Lean name (`A.«b c».d`) as nanoda_bin reads it from pp_declars: the components joined by dots.

    nanoda_bin splits that text at the dots and reads a component of digits as a number, so a name
    with a dot or only digits inside «» would be read as another name: AnalysisError for those."""
    comps = []
    i, n = 0, len(name)
    while True:
        if name.startswith('«', i):
            j = name.find('»', i + 1)
            comp, i = name[i + 1:j], j + 1
            if j < 0 or not comp or '.' in comp or comp.isdigit():
                raise AnalysisError('the printer cannot print %s: nanoda_bin would read another name' % name)
        else:
            j = name.find('.', i)
            j = n if j < 0 else j
            comp, i = name[i:j], j
            if not comp:
                raise AnalysisError('%s is not a Lean name' % name)
        comps.append(comp)
        if i == n:
            return '.'.join(comps)
        if name[i] != '.' or i + 1 == n:
            raise AnalysisError('%s is not a Lean name' % name)
        i += 1


def _is_printed(text, name):
    """True if nanoda_bin's text is the declaration `name`: a keyword, the name, and the rest."""
    keyword, space, rest = text.partition(' ')
    if not space or not keyword.isalpha():
        return False
    for form in (name, '«' + name + '»'):
        if rest.startswith(form):
            after = rest[len(form):]
            if after == '' or after.startswith((' ', ':', '\n', '.{')):
                return True
    return False


def nanoda_printer(nanoda, export_path):
    """The printer for analyze: nanoda_bin's pretty-printer on the export, one call for all the names.

    nanoda_bin checks the export first, prints the declarations in the order asked for, each followed
    by declar_sep, then the allowed axioms the export has. The separator is new and random each call,
    so nothing in the export can forge one."""

    def printer(names):
        wanted = [_nanoda_name(n) for n in names]
        sep = secrets.token_hex(16)
        config = {
            'export_file_path': export_path,
            'use_stdin': False,
            'permitted_axioms': sorted(ALLOWED_AXIOMS),
            'unpermitted_axiom_hard_error': False,
            'nat_extension': True,
            'string_extension': True,
            'pp_declars': wanted,
            'pp_to_stdout': True,
            'pp_options': {'all': False, 'explicit': False, 'universes': False, 'notation': True,
                           'proofs': False, 'declar_sep': sep},
            'print_success_message': False,
        }
        fd, path = tempfile.mkstemp(prefix='vacheck-nanoda-', suffix='.json')
        try:
            with os.fdopen(fd, 'w', encoding='utf-8') as f:
                json.dump(config, f)
            proc = subprocess.run([nanoda, path], stdin=subprocess.DEVNULL, capture_output=True)
        except OSError as e:
            raise AnalysisError('cannot run nanoda_bin: %s' % (e.strerror or e)) from None
        finally:
            os.unlink(path)
        if proc.returncode != 0:
            why = ' '.join(proc.stderr.decode('utf-8', errors='replace').split())[:300]
            raise AnalysisError('nanoda_bin could not print the statements: %s' % why)
        parts = proc.stdout.decode('utf-8', errors='replace').split(sep)
        texts, extra = parts[:len(names)], parts[len(names):-1]
        if (len(parts) <= len(names) or parts[-1] != '' or len(extra) > len(ALLOWED_AXIOMS)
                or not all(e.startswith('axiom ') for e in extra)):
            raise AnalysisError('nanoda_bin did not print every declaration')
        for name, nano, text in zip(names, wanted, texts):
            if not _is_printed(text, nano):
                raise AnalysisError('nanoda_bin did not print %s' % name)
        return dict(zip(names, texts))

    return printer


def analyze_command(args):
    if _toolchain.lookup(args.toolchain) is None:
        raise Rejected(_unsupported())
    manifest = _manifest(args.manifest)
    export = _export(args.export, 'the export')
    reference = _export(args.reference, "the toolchain's reference export")
    source = os.path.abspath(args.source)
    manifest_path = os.path.relpath(os.path.abspath(args.manifest), source).replace(os.sep, '/')
    kernels = [k for k in args.kernels.split(',') if k]
    printer = nanoda_printer(args.nanoda, os.path.abspath(args.export))
    try:
        result = analyze(export, reference, manifest, source, args.repo, args.commit, args.toolchain,
                         kernels, printer, manifest_path=manifest_path)
    except AnalysisError as e:
        raise Rejected(e) from None
    _out(_canonical(result))


def _unique(pairs):
    obj = {}
    for k, v in pairs:
        if k in obj:
            raise ValueError('the key %s is repeated' % json.dumps(k)[:80])
        obj[k] = v
    return obj


def _no_constant(name):
    raise ValueError('%s is not JSON' % name)


def validate(args):
    data = _read(args.file, RESULT_BYTES, 'result.json')
    if len(data) > RESULT_BYTES:
        raise Rejected('result.json is larger than 1 MB')
    try:
        obj = json.loads(data.decode('utf-8'), object_pairs_hook=_unique, parse_constant=_no_constant)
    except (UnicodeDecodeError, ValueError, RecursionError) as e:
        raise Rejected('result.json is not valid JSON: %s' % e) from None
    try:
        validate_result(obj)
    except ResultError as e:
        raise Rejected('result.json is not valid: %s' % e) from None
    _out(_canonical(obj))


class _Parser(argparse.ArgumentParser):
    def error(self, message):
        raise Misuse('%s: %s' % (self.prog, message))


def _parser():
    parser = _Parser(prog='vacheck.pyz', description='Checks a Lean project for the Verification Alliance.')
    commands = parser.add_subparsers(dest='command', required=True)
    for name, fn, arg in ((toolchain.__name__, toolchain, 'lean-toolchain file'),
                          (deps.__name__, deps, 'lake-manifest.json'),
                          (modules.__name__, modules, 'manifest'),
                          (validate.__name__, validate, 'result.json')):
        p = commands.add_parser(name)
        p.add_argument('file', metavar=arg)
        p.set_defaults(run=fn)
    p = commands.add_parser('analyze')
    for flag in ('export', 'reference', 'manifest', 'source', 'repo', 'commit', 'toolchain', 'kernels',
                 'nanoda'):
        p.add_argument('--' + flag, required=True)
    p.set_defaults(run=analyze_command)
    return parser


def run(argv=None):
    """The exit code of the command line; messages on stderr."""
    try:
        args = _parser().parse_args(argv)
        args.run(args)
        return 0
    except Misuse as e:
        msg, code = e, 2
    except Rejected as e:
        msg, code = e, 1
    except Exception as e:  # a failure nothing above foresaw: one line too
        msg, code = 'vacheck failed: %s: %s' % (type(e).__name__, e), 1
    sys.stderr.buffer.write((_one_line(msg) + '\n').encode('utf-8', errors='replace'))
    sys.stderr.buffer.flush()
    return code


def main():
    sys.exit(run())


if __name__ == '__main__':
    main()
