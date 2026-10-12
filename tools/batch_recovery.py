"""Source/record transactions for batch take-out and withdrawal. Never invokes a compiler.

Derived from batch_land.land_one, merge_delivery.unbook/cmd_return/refresh_queue:
landing writes Lean files, local/builds requests/inflight/backup, DAG node fields
(lean, lean_audit, proved status and reviewed_proof), change records, report,
claim, group returns, coord/deliveries.log, ledger; queue refresh also writes
queue.tsv, queue.md, blueprint-index.tsv and blueprint backfill. Take-out restores
each delivery-owned change, preserves later independent edits, closes its request
with restored sorry_allowed, restores its claim, then writes a return and regenerates
the queue. Withdrawal does the same inverse without worker returns, restores branch
heads/passed markers, and leaves every removed delivery waiting; there is no bisection. A genuine
conflicting maintainer edit is never discarded: the transaction refuses before writes.
"""
from __future__ import annotations
import difflib, json, pathlib, re, subprocess, tempfile

IMPORT = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.\']+)\s*$')
TRAILER = '\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>'


class Conflict(RuntimeError):
    pass


class TipMoved(Conflict):
    """Preparation must be retried immediately on the current tree."""
    pass


def git(root, *args):
    p = subprocess.run(['git', '-C', str(root), *args], capture_output=True)
    if p.returncode:
        raise Conflict(p.stderr.decode(errors='replace').strip())
    return p.stdout


def blob(root, ref, path):
    p = subprocess.run(['git', '-C', str(root), 'show', f'{ref}:{path}'], capture_output=True)
    return p.stdout if p.returncode == 0 else None


def import_additions(landed, current):
    if landed is None or current is None:
        return None
    a, b = landed.decode().splitlines(keepends=True), current.decode().splitlines(keepends=True)
    added = []
    for op, i, j, k, l in difflib.SequenceMatcher(a=a, b=b, autojunk=False).get_opcodes():
        if op == 'equal':
            continue
        if op != 'insert' or any(not IMPORT.fullmatch(x.strip()) for x in b[k:l]):
            return None
        added.extend(b[k:l])
    return added


def merge_json(before, landed, current):
    """Inverse only fields changed by this landing; preserve independent later audit fields."""
    if current == landed:
        return before
    if before is None and landed is not None and current is not None:
        b, c = json.loads(landed), json.loads(current)
        derived = {'blueprint', 'lean_audit', 'proved', 'proved_proof'}
        if all(b.get(k) == c.get(k) for k in (b.keys() | c.keys()) - derived):
            return None  # only queue backfill/audit rewrote a delivery-created node
    if before is None or landed is None or current is None:
        raise Conflict('a created/deleted node was edited afterwards')
    a, b, c = [json.loads(x) for x in (before, landed, current)]
    def undo(a, b, c):
        out = dict(c)
        for k in a.keys() | b.keys():
            if a.get(k) == b.get(k) and (k in a) == (k in b):
                continue
            if isinstance(a.get(k), dict) and isinstance(b.get(k), dict) and isinstance(c.get(k), dict):
                out[k] = undo(a[k], b[k], c[k])
            elif c.get(k) == b.get(k) and (k in c) == (k in b):
                if k in a: out[k] = a[k]
                else: out.pop(k, None)
            elif c.get(k) != a.get(k):
                raise Conflict(f'later edit conflicts with delivery field {k}')
        return out
    return (json.dumps(undo(a, b, c), ensure_ascii=False, indent=2) + '\n').encode()


def merge_text(before, landed, current):
    if current == landed or current == before:
        return before
    if None in (before, landed, current):
        raise Conflict('a created/deleted file was edited afterwards')
    # Compose disjoint edits against the landed bytes. Unlike merge-file's
    # context hunks, an append next to a changed proof is not an overlap.
    base = landed.splitlines(keepends=True)
    def edits(data):
        return [(i, j, data.splitlines(keepends=True)[k:l])
                for op, i, j, k, l in difflib.SequenceMatcher(a=base, b=data.splitlines(keepends=True), autojunk=False).get_opcodes()
                if op != 'equal']
    inverse_edits, later = edits(before), edits(current)
    for i, j, _ in inverse_edits:
        for k, l, _ in later:
            if max(i, k) < min(j, l) or (i == j == k == l) or (i < k < j) or (k < i < l):
                raise Conflict('later substantive edit overlaps the delivery')
    out = list(base)
    for i, j, replacement in sorted(inverse_edits + later, key=lambda x: (x[0], x[1]), reverse=True):
        out[i:j] = replacement
    return b''.join(out)


def inverse(root, commits, *, imports_only=False):
    """Prepare the inverse in memory, latest commit first; no live files or index changed."""
    root = pathlib.Path(root); result = {}
    for sha in reversed(commits):
        paths = git(root, 'diff-tree', '--no-commit-id', '--name-only', '-r', sha).decode().splitlines()
        for path in paths:
            before, landed = blob(root, sha + '^', path), blob(root, sha, path)
            p = root / path
            current = result[path] if path in result else (p.read_bytes() if p.is_file() else None)
            if path.startswith('lean/') and path.endswith('.lean'):
                additions = import_additions(landed, current)
                if current != landed and current != before and additions is None and imports_only:
                    raise Conflict(f'{path}: later substantive change; withdraw the batch')
                if additions is not None:
                    # Created delivery modules are removed conservatively, with their nodes.
                    value = before
                    if value is not None:
                        lines = value.decode().splitlines(keepends=True)
                        idx = [i + 1 for i, l in enumerate(lines) if IMPORT.fullmatch(l.strip()) or l.strip() == 'module']
                        at = idx[-1] if idx else 0
                        lines[at:at] = [x for x in additions if x not in lines and
                            ((root / ('lean/' + IMPORT.fullmatch(x.strip())[1].replace('.', '/') + '.lean')).exists() or
                             IMPORT.fullmatch(x.strip())[1].startswith(('Mathlib.', 'Lean.', 'Init.')))]
                        value = ''.join(lines).encode()
                else:
                    value = merge_text(before, landed, current)
            elif path.startswith('coord/claims/'):
                # A renewed/reclaimed item belongs to its current holder. Restore
                # the old claim only when landing removed it and it is still absent.
                value = current if current is not None else before
            elif path.endswith('.json'):
                try:
                    value = merge_json(before, landed, current)
                except Conflict as e:
                    raise Conflict(f'{path}: {e}') from e
            elif path in ('coord/ledger.md', 'coord/deliveries.log'):
                a, b, c = [(x or b'').decode().splitlines(keepends=True) for x in (before, landed, current)]
                added = [x for x in b if x not in a]
                value = ''.join(x for x in c if x not in added).encode()
            else:
                try:
                    value = merge_text(before, landed, current)
                except Conflict as e:
                    raise Conflict(f'{path}: {e}') from e
            result[path] = value
    # Filter replayed proof imports of deleted modules, including in maintainer files.
    removed = {p[5:-5].replace('/', '.') for p, v in result.items() if p.startswith('lean/') and p.endswith('.lean') and v is None}
    for path, data in list(result.items()):
        if data is not None and path.startswith('lean/'):
            lines = data.decode().splitlines(keepends=True)
            result[path] = ''.join(l for l in lines if not (IMPORT.fullmatch(l.strip()) and IMPORT.fullmatch(l.strip())[1] in removed)).encode()
    # A later import-only edit in an outside module can be dropped safely; a real
    # reference to a removed new module needs withdrawal/maintainer investigation.
    for p in (root / 'lean').rglob('*.lean'):
        path = p.relative_to(root).as_posix()
        if path in result: continue
        data = p.read_bytes()
        if any(m in {IMPORT.fullmatch(l.strip())[1] for l in data.decode().splitlines() if IMPORT.fullmatch(l.strip())} for m in removed):
            raise Conflict(f'{path} imports a removed delivery module')
    return result


def commit_inverse(root, prepared, expected, message):
    """Caller holds merge and tree locks only for this write/commit."""
    if git(root, 'rev-parse', 'HEAD').decode().strip() != expected:
        # Unrelated worker commits must not starve a long preparation. Only
        # advancing commits that touch this inverse require a fresh preparation.
        changed = set(git(root, 'diff', '--name-only', expected, 'HEAD').decode().splitlines())
        if changed & set(prepared):
            raise TipMoved('tip moved on recovery paths: prepare and retry')
    previous = {}
    try:
        for path, data in prepared.items():
            p = pathlib.Path(root) / path
            previous[path] = p.read_bytes() if p.is_file() else None
            if data is None: p.unlink(missing_ok=True)
            else: p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(data)
        git(root, 'add', '-A', '--', *prepared)
        if git(root, 'diff', '--cached', '--name-only', '--', *prepared).strip():
            git(root, 'commit', '-q', '-m', message + TRAILER, '--', *prepared)
    except BaseException:
        for path, data in previous.items():
            p = pathlib.Path(root) / path
            if data is None: p.unlink(missing_ok=True)
            else: p.write_bytes(data)
        subprocess.run(['git', '-C', str(root), 'reset', '-q', '--', *prepared], capture_output=True)
        raise



def interface_delta(old, new):
    """Existing classification plus added declarations/public imports and module removal."""
    import leanindex as li
    if old is None or new is None:
        return ['(new/removed module)']
    a, b = li.interface(old), li.interface(new)
    return sorted(set(li.interface_changes(old, new)) |
                  {k for k in b if not k.startswith('#') and k not in a} |
                  ({'(public imports changed)'} if a['#imports'] != b['#imports'] else set()))


def select(entries, failures, imports, changes, messages=None, *, checkpoint=lambda: None):
    """Pure decision shared by live triage and read-only replay. No build or writes.

    changes(entry, module) returns importer-visible declaration names. Exact
    quoted compiler names prefer their changing delivery; never use downstream
    modules as causes of an older importer failure.
    """
    import leanindex as li
    messages = messages or {}; memo = {}; out = []; deltas = {}
    def delta(e, m):
        k = (id(e), m)
        if k not in deltas: deltas[k] = changes(e, m)
        return deltas[k]
    for module in failures:
        checkpoint()
        closure = li.closure(module, imports, memo) | {module}
        writers = [e for e in entries if module in e['modules']]
        suspects, changed = list(writers), {}
        if not writers:
            for e in entries:
                names = {m: delta(e, m) for m in set(e['modules']) & closure}
                names = {m: ns for m, ns in names.items() if ns}
                if names:
                    suspects.append(e); changed[id(e)] = names
            quoted = set(re.findall(r"[`'“‘]([A-Za-z_][\w.']*)[`'”’]", messages.get(module, '')))
            preferred = [e for e in suspects if any(n in quoted for ns in changed[id(e)].values() for n in ns)]
            if preferred: suspects = preferred
        out.append({'failure': module, 'closure': closure, 'suspects': suspects,
                    'message': messages.get(module, ''), 'case': 'own-fault' if writers else 'breaker'})
    return out


def dependents(entries, suspects, imports):
    """Transitive delivery dependency closure, including multi-module deliveries."""
    import leanindex as li
    removed = {id(e) for e in suspects}; modules = {m for e in suspects for m in e['modules']}
    memo = {}
    while True:
        added = [e for e in entries if id(e) not in removed and
                 any(li.closure(m, imports, memo) & modules for m in e['modules'])]
        if not added: break
        removed.update(id(e) for e in added); modules.update(m for e in added for m in e['modules'])
    return [e for e in entries if id(e) in removed and e not in suspects]
