"""Source-only live-pipeline guards; no compiler and no external notification service."""
from __future__ import annotations
import hashlib, json, os, pathlib, time


def alert(batch, module, tried, needs, directory=None):
    directory = pathlib.Path(directory or os.environ.get('SHEAF_ALERT_DIR') or pathlib.Path.home() / 'cc1')
    directory.mkdir(parents=True, exist_ok=True)
    line = ' '.join(f'{time.strftime("%FT%TZ", time.gmtime())} batch={batch or "-"} module={module or "?"} tried={tried} needs={needs}'.split()) + '\n'
    # An unresolved state retains its original line, including its first occurrence.
    try:
        with (directory / 'ALERT').open('x') as f:
            f.write(line)
    except FileExistsError:
        pass


def clear_alert(directory=None):
    directory = pathlib.Path(directory or os.environ.get('SHEAF_ALERT_DIR') or pathlib.Path.home() / 'cc1')
    p = directory / 'ALERT'
    if p.exists():
        with (directory / 'ALERT.log').open('a') as f:
            f.write(p.read_text())
        p.unlink()


def source_fingerprint(root):
    """Ignore ledger/build commits: only bytes that affect compilation identify a tree."""
    root = pathlib.Path(root)
    h = hashlib.sha256()
    for p in sorted(root.rglob('*')):
        if not p.is_file() or any(x.startswith('.') for x in p.relative_to(root).parts):
            continue
        if p.suffix == '.lean' or p.name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
            h.update(str(p.relative_to(root)).encode() + b'\0' + p.read_bytes() + b'\0')
    return h.hexdigest()


def proof_imports_guard(root, modules=()):
    """Fail closed before writes: open batch or any affected pending/inflight landing."""
    root = pathlib.Path(root)
    import landing as ld
    mq = ld.merge_queue()   # merge queue: the import change is a landing of its own and never blocks; only files a
                            # group is still checking (inflight) are refused
    if not mq and ((root / 'local/batch/open.json').exists() or (root / 'local/batch/landing.json').exists()):
        raise RuntimeError('proof imports refused: a batch is open')
    modules = set(modules)
    for directory in (('inflight',) if mq else ('requests', 'inflight')):
        for p in (root / 'local/builds' / directory).glob('*.json'):
            try:
                rec = json.loads(p.read_text())
            except (OSError, ValueError):
                raise RuntimeError(f'proof imports refused: unreadable landing {p.name}')
            if modules & {f['module'] for f in rec.get('files', [])}:
                raise RuntimeError(f'proof imports refused: unverified landing {rec["id"]}')


def frozen_modules(root) -> set[str]:
    """Modules whose files belong to a landing the global build has not verified yet: pending or held landings
    (local/builds/requests, inflight) and the deliveries of the open batch (local/batch/open.json, landing.json).
    No writer other than the landing tools and the take-out may change them until the build has verified them
    (the human, 2026-10-19: a prune of unused imports in a delivered file made the take-out conflict and live stayed
    red for hours). Source-only and fast: reads a few hundred small records."""
    root = pathlib.Path(root)
    out = set()
    for directory in ('requests', 'inflight'):
        for p in (root / 'local/builds' / directory).glob('*.json'):
            try:
                out |= {f['module'] for f in json.loads(p.read_text()).get('files', []) if f.get('module')}
            except (OSError, ValueError):
                continue
    for name in ('open.json', 'landing.json'):
        try:
            b = json.loads((root / 'local/batch' / name).read_text())
        except (OSError, ValueError):
            continue
        for e in b.get('entries', []):
            if e.get('state') in (None, 'landed', 'stuck'):
                out |= set(e.get('modules') or [])
    return out
