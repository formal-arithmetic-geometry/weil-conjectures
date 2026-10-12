"""Source-only import-cycle checks shared by the batch lander and delivery launcher."""
from __future__ import annotations
import pathlib, re
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)", re.M)


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
    return set(IMPORT.findall(''.join(out)))


def graph(root):
    root = pathlib.Path(root)
    return {'.'.join(p.relative_to(root).with_suffix('').parts): imports(p.read_text(errors='replace'))
            for family in ('Sheaf', 'WeilConjectures', 'TargetsCheck', 'SheafChallenge')
            for p in ([root / (family + '.lean')] if (root / (family + '.lean')).is_file() else []) + list((root / family).rglob('*.lean'))}


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
    """Lake prints the cycle as an indented list following its diagnostic."""
    cycles = []
    for block in text.split('build cycle detected:')[1:]:
        mods = []
        for line in block.splitlines():
            s = line.strip().strip('`\"')
            if not s: continue
            s = re.sub(r'^(?:error:\s*)?', '', s).strip()
            if re.fullmatch(r"(?:Sheaf|WeilConjectures)\.[\w.']+", s): mods.append(s)
            elif mods or 'bad import' in s or s.startswith(('error:', '✖', '✔', '⚠')): break
        if mods: cycles.append(mods)
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
