"""Immutable shared source indexes; workers read, one locked builder publishes.

Every lookup resolves origin/sheaf-dag anew. Derived data is keyed by the full
commit, lexer source hashes and library configuration. Working-tree differences
are overlaid, including untracked files; no delivered text enters the shared cache.
No cache directory (e.g. on the project server) means the original scanners run.
"""
from __future__ import annotations
import fcntl, hashlib, json, os, pathlib, subprocess, tempfile

VERSION = 1
_MEM = {}

def git(root, *args):
    return subprocess.check_output(['git', *args], cwd=root)

def _load(root, families):
    root = pathlib.Path(root)
    directory = pathlib.Path(os.environ.get('WEIL_DELIVERY_CACHE', pathlib.Path.home() / 'weil-launcher/cache'))
    if not directory.is_dir() or os.environ.get('WEIL_DELIVERY_CACHE_DISABLE') == '1':
        return None
    try:
        commit = git(root, 'rev-parse', '--verify', 'origin/sheaf-dag').decode().strip()
    except subprocess.CalledProcessError:
        return None
    import leanindex as li
    tools = pathlib.Path(__file__).resolve().parent
    digest = hashlib.sha256()
    for name in ('delivery_cache.py', 'delivery_import_cycles.py'):
        digest.update((tools / name).read_bytes())
    # Hash the parser actually imported from this clone, not a launcher's copy.
    digest.update(pathlib.Path(li.__file__).read_bytes())
    signature = digest.hexdigest()[:16]
    families = list(families)
    key = (commit, signature, tuple(families), str(directory))
    if key in _MEM:
        return _MEM[key]
    suffix = hashlib.sha256(json.dumps(families).encode()).hexdigest()[:12]
    filename = directory / f'library-{signature}-{suffix}-{commit}.json'
    def read():
        try:
            data = json.loads(filename.read_text())
            if data['commit'] == commit and data['version'] == VERSION and data['families'] == families and data['signature'] == signature:
                return data
        except (OSError, ValueError, KeyError):
            pass
        return None
    data = read()
    if data is None:
        # One builder for all commits/configurations, avoiding a cold-cache herd.
        with (directory / 'library-builder.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            data = read()
            if data is None:
                data = build(root, commit, families, signature, directory)
                fd, tmp = tempfile.mkstemp(prefix='.library-', dir=directory)
                try:
                    with os.fdopen(fd, 'w') as out:
                        json.dump(data, out, ensure_ascii=False, separators=(',', ':'))
                        out.flush(); os.fsync(out.fileno())
                        os.fchmod(out.fileno(), 0o444)
                    os.replace(tmp, filename)
                finally:
                    pathlib.Path(tmp).unlink(missing_ok=True)
    if git(root, 'rev-parse', '--verify', 'origin/sheaf-dag').decode().strip() != commit:
        return load(root, families)
    _MEM[key] = data
    return data

def load(root, families):
    import leanindex as li
    try:
        return _load(root, families)
    except (OSError, subprocess.CalledProcessError, li.LexError):
        # An unavailable cache must never introduce a new delivery refusal.
        return None


def build(root, commit, families, signature, directory):
    import leanindex as li
    import delivery_import_cycles as cycles
    previous = {}
    # Reuse identical blobs when the base advances; only new/changed sources lexed.
    candidates = sorted(directory.glob(f'library-{signature}-*.json'), key=lambda p: p.stat().st_mtime, reverse=True)
    if candidates:
        try:
            prior = json.loads(candidates[0].read_text())
            previous = {v['blob']: v for v in prior['modules'].values()}
        except (OSError, ValueError, KeyError):
            pass
    modules = {}
    entries = []
    for line in git(root, 'ls-tree', '-r', commit, '--', 'lean').decode().splitlines():
        head, path = line.split('\t', 1)
        if not path.endswith('.lean'): continue
        mod = path[5:-5].replace('/', '.')
        cycle = mod.split('.')[0] in ('Sheaf', 'WeilConjectures', 'TargetsCheck', 'SheafChallenge')
        library = mod.split('.')[0] in families or mod in ('Challenge', 'TargetsCheck')
        if library or cycle:
            entries.append((head.split()[2], mod, library, cycle))
    pending = [(sha, mod, library, cycle) for sha, mod, library, cycle in entries if sha not in previous]
    request = ''.join(sha + '\n' for sha, *_ in pending).encode()
    response = subprocess.run(['git','cat-file','--batch'], cwd=root, input=request, capture_output=True, check=True).stdout
    offset = 0
    fresh = {}
    for sha, mod, library, cycle in pending:
        end = response.index(b'\n', offset); size = int(response[offset:end].split()[2])
        raw = response[end+1:end+1+size]; offset = end+size+2
        text = raw.decode(errors='ignore')
        fresh[sha] = {'blob': sha, 'imports': sorted(li.imports_of(text)),
                      'decls': sorted(li.decls_in_text(text)), 'text': li.strip(text),
                      'cycle': sorted(cycles.imports(raw.decode(errors='replace')))}
    for sha, mod, library, cycle in entries:
        modules[mod] = previous.get(sha) or fresh[sha]
    return {'version': VERSION, 'commit': commit, 'signature': signature, 'families': families, 'modules': modules}

def working_modules(root, data):
    """Paths whose current contents differ from the immutable base."""
    roots = set(data['families']) | {'Sheaf', 'WeilConjectures', 'TargetsCheck', 'SheafChallenge', 'Challenge'}
    scope = [p for r in sorted(roots) for p in ('lean/' + r, 'lean/' + r + '.lean')]
    paths = set(git(root, 'diff', '--name-only', '-z', data['commit'], '--', *scope).decode().split('\0'))
    paths.update(git(root, 'ls-files', '--others', '-z', '--', *scope).decode().split('\0'))
    return {p[5:-5].replace('/', '.'): pathlib.Path(root) / p for p in paths if p.endswith('.lean')}

def imports(root, families):
    import leanindex as li
    data = load(root, families)
    if data is None: return None
    result = {m: set(v['imports']) for m,v in data['modules'].items()
              if m.split('.')[0] in families or m in ('Challenge', 'TargetsCheck')}
    for m,p in working_modules(root, data).items():
        if m.split('.')[0] not in families and m not in ('Challenge', 'TargetsCheck'): continue
        if p.is_file(): result[m] = li.imports_of(p.read_text(errors='ignore'))
        else: result.pop(m, None)
    return result

def cycle_graph(root):
    import delivery_import_cycles as cycles
    import leanindex as li
    data = load(root, li.library_dirs())
    if data is None: return None
    result = {m: set(v['cycle']) for m,v in data['modules'].items()
              if m.split('.')[0] in ('Sheaf','WeilConjectures','TargetsCheck','SheafChallenge')}
    for m,p in working_modules(root, data).items():
        if m.split('.')[0] not in ('Sheaf','WeilConjectures','TargetsCheck','SheafChallenge'): continue
        if p.is_file(): result[m] = cycles.imports(p.read_text(errors='replace'))
        else: result.pop(m, None)
    return result

def declarations(root, families):
    import collections, leanindex as li
    data = load(root, families)
    if data is None: return None
    per_module = {m: set(v['decls']) for m,v in data['modules'].items()
                  if m.split('.')[0] in families or m in ('Challenge', 'TargetsCheck')}
    for m,p in working_modules(root, data).items():
        if m.split('.')[0] not in families and m not in ('Challenge', 'TargetsCheck'): continue
        if p.is_file(): per_module[m] = li.decls_in_text(p.read_text(errors='ignore'))
        else: per_module.pop(m, None)
    out = collections.defaultdict(set)
    for m,names in per_module.items():
        if m != 'Challenge':
            for name in names: out[name].add(m)
    return out

_NODE_MEM = {}

def node_index(root, ref, build_nodes):
    """The declaration-to-node checks also need the immutable base DAG."""
    directory = pathlib.Path(os.environ.get('WEIL_DELIVERY_CACHE', pathlib.Path.home() / 'weil-launcher/cache'))
    if not directory.is_dir() or os.environ.get('WEIL_DELIVERY_CACHE_DISABLE') == '1':
        return None
    try:
        commit = git(root, 'rev-parse', '--verify', 'origin/sheaf-dag').decode().strip()
        if git(root, 'rev-parse', '--verify', ref).decode().strip() != commit:
            return None
        key = (str(directory), commit)
        if key in _NODE_MEM: return _NODE_MEM[key]
        filename = directory / f'nodes-v1-{commit}.json'
        def read():
            try:
                value = json.loads(filename.read_text())
                if value['commit'] == commit: return value['nodes']
            except (OSError, ValueError, KeyError): pass
            return None
        nodes = read()
        if nodes is None:
            with (directory / 'library-builder.lock').open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX)
                nodes = read()
                if nodes is None:
                    nodes = build_nodes(commit)
                    fd, tmp = tempfile.mkstemp(prefix='.nodes-', dir=directory)
                    try:
                        with os.fdopen(fd, 'w') as out:
                            json.dump({'commit':commit,'nodes':nodes}, out, ensure_ascii=False, separators=(',',':'))
                            out.flush(); os.fsync(out.fileno()); os.fchmod(out.fileno(), 0o444)
                        os.replace(tmp, filename)
                    finally:
                        pathlib.Path(tmp).unlink(missing_ok=True)
        if git(root, 'rev-parse', '--verify', 'origin/sheaf-dag').decode().strip() != commit:
            return None
        _NODE_MEM[key] = nodes
        return nodes
    except (OSError, subprocess.CalledProcessError):
        return None
