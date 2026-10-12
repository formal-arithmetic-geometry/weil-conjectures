"""Source-only import-cycle checks shared by the batch lander and delivery launcher."""
from __future__ import annotations
import pathlib, re
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\n]+)", re.M)


def imports(text):
    # Preserve newlines while stripping nested Lean comments and string literals.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i): depth += 1; i += 2
        elif depth and text.startswith('-/', i): depth -= 1; i += 2
        elif depth: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i); i = len(text) if j < 0 else j
        elif text[i] == '"':
            out.append(' '); i += 1
            while i < len(text):
                if text[i] == '\\': i += 2
                elif text[i] == '"': i += 1; break
                else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        else: out.append(text[i]); i += 1
    return {m for line in IMPORT.findall(''.join(out)) for m in line.split()
            if re.fullmatch(r"[\w.']+", m)}


def graph(root):
    root = pathlib.Path(root)
    files = list(root.glob('*.lean'))
    for directory in root.iterdir():
        if directory.is_dir() and not directory.name.startswith('.'):
            files.extend(directory.rglob('*.lean'))
    return {'.'.join(p.relative_to(root).with_suffix('').parts): imports(p.read_text(errors='replace'))
            for p in files}



def path(g, start, end):
    todo, seen = [(start, [start])], set()
    while todo:
        m, route = todo.pop()
        if m == end: return route
        if m in seen: continue
        seen.add(m)
        todo.extend((n, route + [n]) for n in sorted(g.get(m, ()), reverse=True))
    return []


def overlay(g, texts):
    result = dict(g)
    for m, text in texts.items():
        if text is None: result.pop(m, None)
        else: result[m] = imports(text)
    return result


def closing_cycle(g, texts):
    """Find a cycle involving a newly added edge in the proposed tree, no writes."""
    proposed = overlay(g, texts)
    for m in sorted(texts):
        for n in sorted(proposed.get(m, set()) - g.get(m, set())):
            route = path(proposed, n, m)
            if route: return [m] + route
    return []


def refuse(root, texts):
    cycle = closing_cycle(graph(root), texts)
    if cycle: raise RuntimeError('import cycle: ' + ' -> '.join(cycle))


def log_cycles(text):
    """Lake's cycle format lists source paths and bad imports; recover module names."""
    cycles = []
    for block in text.split('build cycle detected:')[1:]:
        mods = []
        for line in block.splitlines():
            m = re.search(r'(?:error:\s*)?([\w./]+\.lean):', line)
            if m:
                mods.append(m.group(1)[:-5].replace('/', '.'))
            m = re.search(r"bad import [\'\"]([\w.\']+)[\'\"]", line)
            if m:
                mods.append(m.group(1)); continue
            if mods and line.strip() and not line.strip().startswith(('error:', '✖', '✔', '⚠')): break
        if mods:
            # Lake emits each edge as a source followed by its import; remove duplicates.
            out=[]
            for m in mods:
                if not out or out[-1] != m: out.append(m)
            cycles.append(out)
    return cycles


def cycle_breakers(text, g, entries, read):
    """Only batch writers with a new edge on a logged cycle can be breakers.

    A single closing edge wins. For interacting deliveries the latest writer is
    removed first, matching the sequential static acceptance order.
    """
    cycles = log_cycles(text)
    if not cycles: return []
    out = []
    for mods in cycles:
        members = set(mods)
        candidates = []
        for e in entries:
            for m in members & set(e['modules']):
                old, now = read(e, m)
                for n in imports(now or '') - imports(old or ''):
                    if n in members and path(g, n, m): candidates.append(e); break
        if candidates:
            winner = next(e for e in reversed(entries) if e in candidates)
            out.append((mods, winner))
    return out


def source_roots(lean):
    """Package/toolchain sources only; never accept an orphaned .olean."""
    import tomllib
    lean = pathlib.Path(lean)
    roots = []
    for package in (lean / '.lake/packages').glob('*'):
        roots.append(package)
        config = package / 'lakefile.toml'
        if config.is_file():
            data = tomllib.loads(config.read_text())
            roots.extend(package / lib.get('srcDir', data.get('srcDir', '.'))
                         for lib in data.get('lean_lib', []))
        # Lean lakefiles in this installation use these source directories.
        config = package / 'lakefile.lean'
        if config.is_file():
            roots.extend(package / d for d in re.findall(r'srcDir\s*:=\s*"([^"\n]+)"', config.read_text()))
    toolchain = lean / 'lean-toolchain'
    if toolchain.is_file():
        name = toolchain.read_text().strip().replace('/', '--').replace(':', '---')
        roots.append(pathlib.Path.home() / '.elan/toolchains' / name / 'src/lean')
    return roots


def refuse_missing(texts, library, roots):
    """Validate every delivered import against source modules of the pinned base,
    installed packages/toolchain, or this delivery (never another delivery).
    """
    available = set(library) | {m for m, t in texts.items() if t is not None}
    missing = []
    for module, text in sorted(texts.items()):
        if text is None: continue
        for dep in sorted(imports(text)):
            rel = pathlib.Path(*dep.split('.')).with_suffix('.lean')
            if dep not in available and not any((r / rel).is_file() for r in roots):
                missing.append(f'{module}: {dep}')
    if missing: raise RuntimeError('missing import source modules: ' + '; '.join(missing))


def source_modules(repo, ref='HEAD'):
    """Tracked source inventory of an exact library base; excludes untracked files."""
    import subprocess
    paths = subprocess.run(['git', '-C', str(repo), 'ls-tree', '-r', '--name-only', ref, '--', 'lean/'],
                           check=True, capture_output=True, text=True).stdout.splitlines()
    return {p[5:-5].replace('/', '.') for p in paths if p.endswith('.lean')}
