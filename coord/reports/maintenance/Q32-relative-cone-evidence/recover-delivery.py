"""Recover the independently reviewed, dry-run-approved snapshot on the server.

This creates an ordinary delivery commit in a private repository. It does not
land the statement or change the running worker's sandbox.
"""
import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess


ROOT = Path('/home/ubuntu/weil-newtargets')
TASK = Path('/tmp/q32-maint-1792196920')
PAYLOAD = TASK / 'recovery'
REPO = TASK / 'delivery-repo'
ITEM = 'lem-coef-infinity-relative-cone-equivalence'
NODE = f'dag/nodes/sec-six-functors/{ITEM}.json'
MODULE = 'lean/Sheaf/CategoryTheory/RelativeConeEquivalence.lean'
REPORT = f'coord/reports/Q32/{ITEM}.md'
ENV = dict(os.environ, SHEAF_LEAD='L-only')


def git(*args, cwd=REPO, **kwargs):
    return subprocess.check_output(['git', *args], cwd=cwd, env=ENV, **kwargs)


if REPO.exists():
    raise SystemExit('Private recovery repository already exists; inspect it before retrying')
REPO.mkdir()
git('init', '-q')
objects = git('rev-parse', '--git-path', 'objects', cwd=ROOT, text=True).strip()
(REPO / '.git/objects/info/alternates').write_text(str((ROOT / objects).resolve()) + '\n')

with (ROOT / 'coord/.merge.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    base = git('rev-parse', 'newtargets-dag', cwd=ROOT, text=True).strip()
    current = json.loads(git('show', f'{base}:{NODE}'))
    if current.get('lean'):
        raise SystemExit('Item already has a landed Lean record; no duplicate recovery')
    reviewed = json.loads((PAYLOAD / NODE).read_text())
    # Exactly the fields deliver2 owns, preserving every current maintainer field.
    current['lean'] = reviewed['lean']
    if not set(current.get('stmt_deps', [])).issubset(reviewed['stmt_deps']):
        raise SystemExit('New statement dependencies appeared; a fresh reading is required')
    current['stmt_deps'] = reviewed['stmt_deps']
    git('update-ref', 'refs/heads/recovery', base)
    git('symbolic-ref', 'HEAD', 'refs/heads/recovery')
    git('read-tree', base)
    for rel in (NODE, MODULE, REPORT):
        dst = REPO / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        original = subprocess.run(['git', 'show', f'{base}:{rel}'], cwd=ROOT,
                                  env=ENV, capture_output=True)
        if original.returncode == 0:
            dst.write_bytes(original.stdout)
            shutil.copy2(dst, str(dst) + '.maint-Q32-1792196920.bak')
        if rel == NODE:
            dst.write_text(json.dumps(current, indent=1, ensure_ascii=False) + '\n')
        else:
            dst.write_bytes((PAYLOAD / rel).read_bytes())
    git('add', '--', NODE, MODULE, REPORT)
    print('Staged recovery paths:\n' + git('diff', '--cached', '--name-only', text=True), flush=True)
    print(git('-c', 'user.name=Bin Wu', '-c', 'user.email=844524296@qq.com',
              'commit', '-m', f'Recover reviewed statement delivery {ITEM} (Q32)',
              '-m', 'Recover the second reader result from 862bc0e8f0 after worktree wait '
                    'and provider 429 interruptions. Lean bytes and independent reading '
                    'are unchanged; preserve current server-owned node metadata.', text=True), flush=True)
    head = git('rev-parse', 'HEAD', text=True).strip()
    git('bundle', 'create', str(TASK / 'recovery.bundle'), 'HEAD', '^' + base)
    (TASK / 'recovery-head.txt').write_text(head + '\n')
    (TASK / 'recovery-base.txt').write_text(base + '\n')
    print('Recovery head:', head, flush=True)

