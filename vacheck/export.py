"""Reader for Lean's NDJSON export (lean4export, format 3.1.0), treated as hostile data.

The export comes from a job that ran the developer's code, so every line is checked: ids come
in sequence and point only at records already read, objects have exactly the documented fields
with the documented types, and anything else is an ExportError. Exports are deep (long
application spines, long names, long chains of universe levels), so nothing here recurses.
"""
import hashlib
import json

MAX_LINE = 64 * 1024 * 1024
FORMATS = ('3.1.0',)


class ExportError(Exception):
    pass


# Field types: a scalar tag below, a frozenset (a string out of that set), or one of the classes.
_NAME = 'name'          # id of a name other than the anonymous one
_BINDER = 'binder'      # id of any name, the anonymous one (0) included
_LEVEL = 'level'
_EXPR = 'expr'
_NAT = 'nat'
_BOOL = 'bool'
_STR = 'str'
_DIGITS = 'digits'      # a natural number literal, in decimal
_DATA = 'data'          # the payload of an mdata node: any JSON object
_HINTS = 'hints'
_IDS = (_NAME, _BINDER, _LEVEL, _EXPR, _NAT)


class _Many:
    """A JSON list of any length, every item of one type."""

    def __init__(self, item):
        self.item = item


class _Tuple:
    """A JSON list of fixed length, item by item."""

    def __init__(self, *items):
        self.items = items


class _Obj:
    """A JSON object with exactly these (key, type) fields."""

    def __init__(self, *fields):
        self.fields = fields
        self.keys = frozenset(k for k, _ in fields)
        self.types = tuple(t for _, t in fields)


_NAME_SPECS = {
    'str': _Obj(('pre', _BINDER), ('str', _STR)),
    'num': _Obj(('pre', _BINDER), ('i', _NAT)),
}
_LEVEL_SPECS = {'succ': _LEVEL, 'max': _Tuple(_LEVEL, _LEVEL), 'imax': _Tuple(_LEVEL, _LEVEL), 'param': _NAME}
_BINDER_INFO = frozenset({'default', 'implicit', 'strictImplicit', 'instImplicit'})
_BINDING = _Obj(('name', _BINDER), ('type', _EXPR), ('body', _EXPR), ('binderInfo', _BINDER_INFO))
_EXPR_SPECS = {
    'bvar': _NAT,
    'sort': _LEVEL,
    'const': _Obj(('name', _NAME), ('us', _Many(_LEVEL))),
    'app': _Obj(('fn', _EXPR), ('arg', _EXPR)),
    'lam': _BINDING,
    'forallE': _BINDING,
    'letE': _Obj(('name', _BINDER), ('type', _EXPR), ('value', _EXPR), ('body', _EXPR), ('nondep', _BOOL)),
    'proj': _Obj(('typeName', _NAME), ('idx', _NAT), ('struct', _EXPR)),
    'natVal': _DIGITS,
    'strVal': _STR,
    'mdata': _Obj(('expr', _EXPR), ('data', _DATA)),
}

_HEAD = (('name', _NAME), ('levelParams', _Many(_NAME)), ('type', _EXPR))
_ALL = ('all', _Many(_NAME))
_UNSAFE = ('isUnsafe', _BOOL)
_INDUCTIVE = _Obj(*_HEAD, ('numParams', _NAT), ('numIndices', _NAT), _ALL, ('ctors', _Many(_NAME)),
                  ('numNested', _NAT), ('isRec', _BOOL), ('isReflexive', _BOOL), _UNSAFE)
_CTOR = _Obj(*_HEAD, ('induct', _NAME), ('cidx', _NAT), ('numParams', _NAT), ('numFields', _NAT), _UNSAFE)
_RULE = _Obj(('ctor', _NAME), ('nfields', _NAT), ('rhs', _EXPR))
_REC = _Obj(*_HEAD, _ALL, ('numParams', _NAT), ('numIndices', _NAT), ('numMotives', _NAT), ('numMinors', _NAT),
            ('rules', _Many(_RULE)), ('k', _BOOL), _UNSAFE)
_BLOCK = _Obj(('types', _Many(_INDUCTIVE)), ('ctors', _Many(_CTOR)), ('recs', _Many(_REC)))
# Record tag -> (kind, spec).
_DECL_SPECS = {
    'axiom': ('axiom', _Obj(*_HEAD, _UNSAFE)),
    'def': ('def', _Obj(*_HEAD, ('value', _EXPR), ('hints', _HINTS),
                        ('safety', frozenset({'unsafe', 'safe', 'partial'})), _ALL)),
    'opaque': ('opaque', _Obj(*_HEAD, ('value', _EXPR), _UNSAFE, _ALL)),
    'thm': ('theorem', _Obj(*_HEAD, ('value', _EXPR), _ALL)),
    'quot': ('quot', _Obj(*_HEAD, ('kind', frozenset({'type', 'ctor', 'lift', 'ind'})))),
    'inductive': ('inductive', _BLOCK),
}
_SPEC_OF_KIND = {kind: spec for kind, spec in _DECL_SPECS.values()}
_MEMBERS = (('types', 'inductive'), ('ctors', 'ctor'), ('recs', 'rec'))


def _node_types(spec):
    """The types of the fields of a level or expression node (tag, field, ...), in order."""
    if isinstance(spec, _Obj):
        return spec.types
    if isinstance(spec, _Tuple):
        return spec.items
    return (spec,)


_LEVEL_FIELDS = dict({tag: _node_types(s) for tag, s in _LEVEL_SPECS.items()}, zero=())
_EXPR_FIELDS = {tag: _node_types(s) for tag, s in _EXPR_SPECS.items()}
_EXPR_KIDS = {tag: tuple(i + 1 for i, t in enumerate(ts) if t == _EXPR) for tag, ts in _EXPR_FIELDS.items()}
# Positions of the node fields that a digest covers. It leaves out binder names and binder info:
# Lean's Expr equality ignores them, so the exporter gives one id to expressions that differ only
# there, and which binder names an export shows depends on what it happened to export first.
_LEVEL_HASHED = {tag: tuple(range(len(ts))) for tag, ts in _LEVEL_FIELDS.items()}
_EXPR_HASHED = {tag: tuple(i for i, t in enumerate(ts) if t != _BINDER and t is not _BINDER_INFO)
                for tag, ts in _EXPR_FIELDS.items()}


def _sha(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


class _Decl:
    __slots__ = ('kind', 'fields', 'block')

    def __init__(self, kind, fields, block=None):
        self.kind = kind
        self.fields = fields
        self.block = block

    def exprs(self):
        out = [self.fields['type']]
        if 'value' in self.fields:
            out.append(self.fields['value'])
        if self.kind == 'rec':
            out.extend(rule['rhs'] for rule in self.fields['rules'])
        return out


class Env:
    """The declarations of one export. Built by load_export."""

    def __init__(self):
        # Names. `_canon[raw id]` is the id of the first name read with the same structure, so a
        # name repeated under another id is still the same name. `_parts[id]` is (canonical id of
        # the prefix, component): a str component for Name.str, an int for Name.num.
        self._canon = [0]
        self._parts = [None]
        self._intern = {}
        self._levels = [('zero',)]
        self._exprs = []
        self._decls = {}
        self._names = None
        self._literal_deps = {}
        self._nhash = {0: _sha(['anonymous'])}
        self._lhash = {}
        self._ehash = {}

    def kind(self, name):
        """'theorem', 'def', 'axiom', 'opaque', 'inductive', 'ctor', 'rec' or 'quot'; None if absent."""
        d = self._decls.get(self._lookup(name))
        return None if d is None else d.kind

    def components(self):
        """Every declaration's name as the tuple of its components: a str for Name.str, an int for
        Name.num. Unlike the printed names, these are exact: they are what Lean's Name is."""
        return [self._components(c) for c in self._decls]

    def _components(self, c):
        comps = []
        while c != 0:
            c, comp = self._parts[c]
            comps.append(comp)
        return tuple(reversed(comps))

    def names(self):
        if self._names is None:
            names = frozenset(self._render(c) for c in self._decls)
            if len(names) != len(self._decls):
                raise ExportError('two declarations print as the same name')
            self._names = names
        return self._names

    # Reading.

    def _read(self, obj):
        if type(obj) is not dict:
            raise ExportError('a record must be an object')
        if 'ie' in obj:
            self._read_node(obj, 'ie', _EXPR_SPECS, self._exprs)
        elif 'in' in obj:
            self._read_node(obj, 'in', _NAME_SPECS, self._canon)
        elif 'il' in obj:
            self._read_node(obj, 'il', _LEVEL_SPECS, self._levels)
        else:
            if len(obj) != 1:
                raise ExportError('unknown record')
            (tag, body), = obj.items()
            if tag not in _DECL_SPECS:
                raise ExportError('unknown record %r' % tag[:40])
            kind, spec = _DECL_SPECS[tag]
            fields = self._value(spec, body)
            if tag == 'inductive':
                for key, member_kind in _MEMBERS:
                    for member in fields[key]:
                        self._declare(_Decl(member_kind, member, fields))
            else:
                self._declare(_Decl(kind, fields))

    def _read_node(self, obj, id_key, specs, table):
        if len(obj) != 2:
            raise ExportError('a %r record has exactly two fields' % id_key)
        tag = next(k for k in obj if k != id_key)
        if tag not in specs:
            raise ExportError('unknown %r record %r' % (id_key, tag[:40]))
        idx = obj[id_key]
        if type(idx) is not int or idx != len(table):
            raise ExportError('%s %r is out of sequence' % (id_key, idx))
        spec = specs[tag]
        value = self._value(spec, obj[tag])
        if table is self._canon:
            c = self._intern.setdefault(value, idx)
            self._canon.append(c)
            self._parts.append(value)
        else:
            table.append((tag,) + value if isinstance(spec, (_Obj, _Tuple)) else (tag, value))

    def _declare(self, decl):
        name = decl.fields['name']
        if name in self._decls:
            raise ExportError('%s is declared twice' % self._render(name)[:200])
        self._decls[name] = decl

    def _value(self, t, v):
        """Checks v against type t and converts it: name ids to canonical ids, lists to tuples.

        An _Obj becomes a dict, except in names, levels and expressions, where it becomes a tuple.
        """
        if t in _IDS:
            if type(v) is not int or v < 0:
                raise ExportError('expected a natural number')
            if t == _NAT:
                return v
            if t == _EXPR:
                if v >= len(self._exprs):
                    raise ExportError('expression %d is not defined yet' % v)
                return v
            if t == _LEVEL:
                if v >= len(self._levels):
                    raise ExportError('level %d is not defined yet' % v)
                return v
            if v >= len(self._canon) or (t == _NAME and v == 0):
                raise ExportError('name %d is not defined yet' % v)
            return self._canon[v]
        if t == _BOOL:
            if type(v) is not bool:
                raise ExportError('expected true or false')
            return v
        if t == _STR or t == _DIGITS:
            if type(v) is not str:
                raise ExportError('expected a string')
            try:
                v.encode('utf-8')
            except UnicodeEncodeError:
                raise ExportError('a string is not valid Unicode') from None
            if t == _DIGITS and not (v.isascii() and v.isdigit()):
                raise ExportError('expected a natural number literal')
            return v
        if t == _DATA:
            if type(v) is not dict:
                raise ExportError('expected an object')
            return json.dumps(v, sort_keys=True)
        if t == _HINTS:
            if v == 'opaque' or v == 'abbrev':
                return v
            if type(v) is dict and v.keys() == {'regular'} and type(v['regular']) is int and v['regular'] >= 0:
                return ('regular', v['regular'])
            raise ExportError('unexpected reducibility hints')
        if type(t) is frozenset:
            if type(v) is not str or v not in t:
                raise ExportError('unexpected value')
            return v
        if isinstance(t, _Many):
            if type(v) is not list:
                raise ExportError('expected a list')
            return tuple(self._value(t.item, x) for x in v)
        if isinstance(t, _Tuple):
            if type(v) is not list or len(v) != len(t.items):
                raise ExportError('expected a list of %d' % len(t.items))
            return tuple(self._value(tt, x) for tt, x in zip(t.items, v))
        if type(v) is not dict or v.keys() != t.keys:
            raise ExportError('an object does not have the expected fields')
        if t in _NAME_SPECS.values() or t in _EXPR_SPECS.values():
            return tuple(self._value(tt, v[k]) for k, tt in t.fields)
        return {k: self._value(tt, v[k]) for k, tt in t.fields}

    def _finish(self):
        for literal, deps in (('natVal', ('Nat',)), ('strVal', ('Char.ofNat', 'String.ofList'))):
            found = (self._lookup(d) for d in deps)
            self._literal_deps[literal] = tuple(c for c in found if c in self._decls)

    # Names as text.

    def _render(self, c):
        comps = []
        while c != 0:
            pre, comp = self._parts[c]
            comps.append(str(comp) if type(comp) is int else _escape(comp))
            c = pre
        return '.'.join(reversed(comps))

    def _lookup(self, name):
        """The canonical id of a name written as Lean prints it (`A.«b c».d`, `A.0`), or None."""
        if type(name) is not str or not name:
            return None
        c, i, n = 0, 0, len(name)
        while True:
            if name.startswith('«', i):
                j = name.find('»', i + 1)
                if j < 0:
                    return None
                comp, i = name[i + 1:j], j + 1
            else:
                j = name.find('.', i)
                j = n if j < 0 else j
                comp, i = name[i:j], j
                if not comp:
                    return None
                if comp.isascii() and comp.isdigit():
                    if len(comp) > 30:
                        return None
                    comp = int(comp)
            c = self._intern.get((c, comp))
            if c is None:
                return None
            if i == n:
                return c
            if name[i] != '.' or i + 1 == n:
                return None
            i += 1

    def _decl(self, name):
        c = self._lookup(name)
        if c not in self._decls:
            raise ExportError('the export has no declaration %r' % str(name)[:200])
        return c

    # Traversal: an explicit stack, and a memo or a visited mark, never recursion.

    def _constants(self, roots, seen, literals):
        out = set()
        stack = list(roots)
        exprs = self._exprs
        while stack:
            e = stack.pop()
            if seen[e]:
                continue
            seen[e] = 1
            node = exprs[e]
            tag = node[0]
            if tag == 'const':
                out.add(node[1])
            elif literals and tag in self._literal_deps:
                out.update(self._literal_deps[tag])
            else:
                for i in _EXPR_KIDS[tag]:
                    stack.append(node[i])
        return out

    def _name_hash(self, c):
        memo = self._nhash
        chain = []
        while c not in memo:
            chain.append(c)
            c = self._parts[c][0]
        for c in reversed(chain):
            pre, comp = self._parts[c]
            memo[c] = _sha(['num' if type(comp) is int else 'str', memo[pre], comp])
        return memo[c]

    def _level_hash(self, root):
        return self._dag_hash(root, self._levels, self._lhash, _LEVEL_FIELDS, _LEVEL_HASHED, _LEVEL)

    def _expr_hash(self, root):
        return self._dag_hash(root, self._exprs, self._ehash, _EXPR_FIELDS, _EXPR_HASHED, _EXPR)

    def _dag_hash(self, root, table, memo, fields, hashed, own):
        """Merkle hash of a level or an expression: a node's hash covers its children's hashes."""
        stack = [root]
        while stack:
            x = stack[-1]
            if x in memo:
                stack.pop()
                continue
            node = table[x]
            types = fields[node[0]]
            pending = [v for t, v in zip(types, node[1:]) if t == own and v not in memo]
            if pending:
                stack.extend(pending)
                continue
            stack.pop()
            memo[x] = _sha([node[0]] + [self._encode(types[i], node[i + 1]) for i in hashed[node[0]]])
        return memo[root]

    def _encode(self, t, v):
        """A value of type t, with every id replaced by the hash of what it refers to."""
        if t == _NAME or t == _BINDER:
            return self._name_hash(v)
        if t == _LEVEL:
            return self._level_hash(v)
        if t == _EXPR:
            return self._expr_hash(v)
        if isinstance(t, _Many):
            return [self._encode(t.item, x) for x in v]
        if isinstance(t, _Obj):
            return {k: self._encode(tt, v[k]) for k, tt in t.fields}
        return v


def _letter_like(v):
    return ((0x3b1 <= v <= 0x3c9 and v != 0x3bb) or (0x391 <= v <= 0x3a9 and v not in (0x3a0, 0x3a3))
            or 0x3ca <= v <= 0x3fb or 0x1f00 <= v <= 0x1ffe or 0x2100 <= v <= 0x214f
            or 0x1d49c <= v <= 0x1d59f or (0xc0 <= v <= 0xff and v not in (0xd7, 0xf7))
            or 0x100 <= v <= 0x17f)


def _id_first(c):
    return 'a' <= c <= 'z' or 'A' <= c <= 'Z' or c == '_' or _letter_like(ord(c))


def _id_rest(c):
    v = ord(c)
    return (_id_first(c) or '0' <= c <= '9' or c in "'!?"
            or 0x2080 <= v <= 0x209c or 0x1d62 <= v <= 0x1d6a or v == 0x2c7c)


def _escape(s):
    """A name component as Lean's Name.toString writes it: «» around anything not an identifier
    (a component holding » cannot be escaped, and Lean leaves it as it is)."""
    if s and _id_first(s[0]) and all(_id_rest(c) for c in s[1:]) or '»' in s:
        return s
    return '«' + s + '»'


def _check_meta(obj):
    try:
        version = obj['meta']['format']['version']
    except (KeyError, TypeError):
        raise ExportError('the export does not start with its metadata') from None
    if len(obj) != 1 or type(version) is not str or version not in FORMATS:
        raise ExportError('unsupported export format %r' % str(version)[:40])


def load_export(path):
    """Reads an NDJSON export. Malformed input, or a line longer than 64 MB, is an ExportError."""
    env = Env()
    lineno = 0
    with open(path, 'rb') as f:
        while True:
            raw = f.readline(MAX_LINE + 1)
            if not raw:
                break
            lineno += 1
            if raw.endswith(b'\n'):
                raw = raw[:-1]
            elif len(raw) > MAX_LINE:
                raise ExportError('line %d is longer than 64 MB' % lineno)
            try:
                obj = json.loads(raw.decode('utf-8'))
            except (ValueError, RecursionError):
                raise ExportError('line %d is not JSON' % lineno) from None
            try:
                if lineno == 1:
                    _check_meta(obj)
                else:
                    env._read(obj)
            except ExportError as e:
                raise ExportError('line %d: %s' % (lineno, e)) from None
    if lineno == 0:
        raise ExportError('the export is empty')
    env._finish()
    return env


def axioms_of(env, name):
    """The axioms `name` rests on: the transitive closure through types and values, taken as Lean's
    CollectAxioms takes it (an inductive brings in its constructors), plus a recursor's rules and
    the declarations that literals unfold to."""
    start = env._decl(name)
    found = set()
    reached = {start}
    todo = [start]
    seen = bytearray(len(env._exprs))
    while todo:
        c = todo.pop()
        d = env._decls.get(c)
        if d is None:
            raise ExportError('%s is used but not declared in the export' % env._render(c)[:200])
        if d.kind == 'axiom':
            found.add(c)
        refs = env._constants(d.exprs(), seen, literals=True)
        if d.kind == 'inductive':
            refs.update(d.fields['ctors'])
        for r in refs:
            if r not in reached:
                reached.add(r)
                todo.append(r)
    return frozenset(env._render(c) for c in found)


def constants_in_type(env, name):
    """The constants that the type of `name` mentions."""
    d = env._decls[env._decl(name)]
    seen = bytearray(len(env._exprs))
    return frozenset(env._render(c) for c in env._constants([d.fields['type']], seen, literals=False))


def value_constants(env, name):
    """The constants that the value of `name` mentions (none when it has no value)."""
    d = env._decls[env._decl(name)]
    if 'value' not in d.fields:
        return frozenset()
    seen = bytearray(len(env._exprs))
    return frozenset(env._render(c) for c in env._constants([d.fields['value']], seen, literals=False))


_HELPERS = ('_mutual', '_unary')  # what Lean compiles well-founded recursion through


def reaches(env, names, target):
    """Whether one of `names` reaches `target`, by a path of one step or more. A step goes from a
    declaration to each constant that its type mentions, and its value unless it is a theorem (a
    proof changes no meaning); from a member of an inductive block to every other; from a definition
    to the others of its mutual block (`all`), which Lean compiles to helpers that name none of them;
    and from a `_mutual` or `_unary` helper to the definition it serves, whose body it holds but does
    not name. A name the export does not declare takes no step. One that is not a name of the export
    at all counts as reaching: what it would reach is not known."""
    goal = env._lookup(target)
    todo = [env._lookup(n) for n in names]
    if goal is None or None in todo:
        return True
    stepped = set()
    seen = bytearray(len(env._exprs))  # shared: what one declaration's expressions reach, all reach
    while todo:
        c = todo.pop()
        if c in stepped:
            continue
        stepped.add(c)
        d = env._decls.get(c)
        nxt = set()
        if d is not None:
            nxt = env._constants([d.fields['type']] if d.kind == 'theorem' else d.exprs(), seen, literals=False)
            if d.block is not None:
                nxt.update(m['name'] for key, _ in _MEMBERS for m in d.block[key])
            elif d.kind in ('def', 'opaque'):
                nxt.update(d.fields['all'])
        pre, comp = env._parts[c] if c else (0, None)
        if comp in _HELPERS and pre in env._decls:
            nxt.add(pre)
        if goal in nxt:
            return True
        todo.extend(nxt - stepped)
    return False


def constructors(env, name):
    """The constructors of the inductive type `name`, in their order; ExportError if it is not one."""
    d = env._decls[env._decl(name)]
    if d.kind != 'inductive':
        raise ExportError('%s is not an inductive type' % str(name)[:200])
    return [env._render(c) for c in d.fields['ctors']]


def parameters(env, name):
    """The number of parameters of an inductive type or a constructor."""
    d = env._decls[env._decl(name)]
    if d.kind not in ('inductive', 'ctor'):
        raise ExportError('%s is neither an inductive type nor a constructor' % str(name)[:200])
    return d.fields['numParams']


def fields(env, ctor, budget=None):
    """The fields of constructor `ctor`, after its parameters, as (name, binder info, dependent): the
    binder's name as one plain identifier, or None when it is anonymous, has more than one component
    or is not an identifier; and whether a later binder or the result mentions it. None when the
    type is not a chain of that many binders (an mdata node, for one), or when finding which fields
    are dependent takes more steps than the budget (a fresh Budget unless one is given) has left."""
    d = env._decls[env._decl(ctor)]
    if d.kind != 'ctor':
        raise ExportError('%s is not a constructor' % str(ctor)[:200])
    e, params, count = d.fields['type'], d.fields['numParams'], d.fields['numFields']
    out = []
    for i in range(params + count):
        node = env._exprs[e]
        if node[0] != 'forallE':
            return None
        _, binder, _, body, info = node
        if i >= params:
            pre, comp = env._parts[binder] if binder != 0 else (None, None)
            plain = pre == 0 and type(comp) is str and _escape(comp) == comp and '»' not in comp
            out.append((comp if plain else None, info, body))
        e = body
    budget = Budget() if budget is None else budget
    try:
        _loose(env, d.fields['type'], budget)
    except OutOfSteps:
        return None
    return [(name, info, bool(budget.loose[body] & 1)) for name, info, body in out]


# The binder chains a declaration starts with: its type's foralls, its value's lambdas.
_CHAINS = {'type': 'forallE', 'value': 'lam'}


def _under(env, e, tag):
    """The expression under e's leading binders of kind tag."""
    while env._exprs[e][0] == tag:
        e = env._exprs[e][3]
    return e


# The most steps that the binder walks of one claim may take (see Budget).
MAX_STEPS = 1000000


class OutOfSteps(Exception):
    """A walk needed more steps than its Budget had left."""


class Budget:
    """The steps that the walks of one claim may still take, and the loose bound variables found so
    far, which later walks reuse. A step is an expression reached, plus one per 256 bits of its set
    of loose bound variables, so the budget bounds both time and memory."""

    __slots__ = ('left', 'loose')

    def __init__(self):
        self.left = MAX_STEPS
        self.loose = {}

    def spend(self, steps):
        self.left -= steps
        if self.left < 0:
            raise OutOfSteps()


def _loose(env, root, budget):
    """Records in budget.loose the loose bound variables of root and of every expression under it,
    each a bitset: bit k is set when the expression mentions de Bruijn index k at its top.

    An expression refers only to expressions read before it, so in id order each one's children are
    done. Each expression is computed once, however many binders it sits under, so the cost is linear
    in the expressions under root, where a walk per binder and per depth would be cubic."""
    loose, exprs = budget.loose, env._exprs
    todo, stack = set(), [root]
    while stack:
        e = stack.pop()
        if e in loose or e in todo:
            continue
        budget.spend(1)
        todo.add(e)
        node = exprs[e]
        stack.extend(node[i] for i in _EXPR_KIDS[node[0]])
    for e in sorted(todo):
        node = exprs[e]
        tag = node[0]
        if tag == 'bvar':
            budget.spend(node[1] >> 8)  # before the bitset is made: an index can be huge
            loose[e] = 1 << node[1]
            continue
        if tag == 'lam' or tag == 'forallE':
            bits = loose[node[2]] | (loose[node[3]] >> 1)
        elif tag == 'letE':
            bits = loose[node[2]] | loose[node[3]] | (loose[node[4]] >> 1)
        else:
            bits = 0
            for i in _EXPR_KIDS[tag]:
                bits |= loose[node[i]]
        budget.spend(bits.bit_length() >> 8)
        loose[e] = bits


def _chain(env, name, field):
    """The leading binders of the declaration's 'type' (its foralls) or 'value' (its lambdas), as
    (binder name id, binder info, the expression under the binder)."""
    d = env._decls[env._decl(name)]
    out = []
    if field in d.fields:
        tag, node = _CHAINS[field], env._exprs[d.fields[field]]
        while node[0] == tag:
            out.append((node[1], node[4], node[3]))
            node = env._exprs[node[3]]
    return out


def binder_chain(env, name, field):
    """The leading binders of the declaration's 'type' (its foralls) or 'value' (its lambdas), as
    (binder, binder info): binder is a handle for binder_name, so only the names asked for are
    rendered. [] for a value that is not a lambda, or a declaration without a value."""
    return [(binder, info) for binder, info, _ in _chain(env, name, field)]


def binder_name(env, binder):
    """A binder's name as Lean prints it, or None when it is anonymous or has macro scopes (a
    component `_@`, as an arrow's hypothesis or `fun _ =>` gets): a report shows no such name."""
    comps = env._components(binder)
    return None if not comps or '_@' in comps else env._render(binder)


def binder_uses(env, name, field, budget):
    """For each binder of binder_chain, whether the rest of the chain (later binder types and the
    body) mentions its variable. OutOfSteps when that takes more steps than the budget has left."""
    chain = _chain(env, name, field)
    if chain:
        _loose(env, env._decls[env._decl(name)].fields[field], budget)
    return [bool(budget.loose[body] & 1) for _, _, body in chain]


def binders(env, name, field, budget=None):
    """binder_chain and binder_uses together, as (name, binder info, used), every name rendered."""
    budget = Budget() if budget is None else budget
    uses = binder_uses(env, name, field, budget)
    return [(binder_name(env, binder), info, used)
            for (binder, info), used in zip(binder_chain(env, name, field), uses)]


def ends_in_prop(env, name):
    """Whether the declaration's type, after its leading foralls, is Prop: a sort of level zero."""
    d = env._decls[env._decl(name)]
    node = env._exprs[_under(env, d.fields['type'], 'forallE')]
    return node[0] == 'sort' and env._levels[node[1]] == ('zero',)


def body_constant(env, name):
    """The declaration's value under its leading lambdas, as Lean prints it, when that is a bare
    constant; otherwise None, as for a declaration without a value."""
    d = env._decls[env._decl(name)]
    if 'value' not in d.fields:
        return None
    node = env._exprs[_under(env, d.fields['value'], 'lam')]
    return env._render(node[1]) if node[0] == 'const' else None


def universe_params(env, name):
    """The number of the declaration's universe parameters."""
    return len(env._decls[env._decl(name)].fields['levelParams'])


def name_components(env, name):
    """The declaration's name as the tuple of its components, exactly as Env.components gives them."""
    return env._components(env._decl(name))


def digest(env, name):
    """sha256 of the declaration's structure with the export's ids resolved, so two exports of the
    same declaration give the same digest. It covers every field of the record, names included,
    except binder names and binder info (see _EXPR_HASHED). A member of an inductive block (the
    type, a constructor, a recursor) covers the whole block."""
    c = env._decl(name)
    d = env._decls[c]
    if d.block is not None:
        body = env._encode(_BLOCK, d.block)
    else:
        body = env._encode(_SPEC_OF_KIND[d.kind], d.fields)
    return _sha({'kind': d.kind, 'name': env._name_hash(c), 'decl': body})
