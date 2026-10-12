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
    if (root / 'local/batch/open.json').exists() or (root / 'local/batch/landing.json').exists():
        raise RuntimeError('proof imports refused: a batch is open')
    modules = set(modules)
    for directory in ('requests', 'inflight'):
        for p in (root / 'local/builds' / directory).glob('*.json'):
            try:
                rec = json.loads(p.read_text())
            except (OSError, ValueError):
                raise RuntimeError(f'proof imports refused: unreadable landing {p.name}')
            if modules & {f['module'] for f in rec.get('files', [])}:
                raise RuntimeError(f'proof imports refused: unverified landing {rec["id"]}')
