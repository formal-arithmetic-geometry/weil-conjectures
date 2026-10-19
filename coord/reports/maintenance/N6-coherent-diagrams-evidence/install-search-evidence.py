import json
import os
import pathlib
import shutil
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
relative = 'dag/nodes/sec-six-functors/lem-coef-cat-infinity-colimits-cartesian-closure.json'
path = root / relative
backup = path.with_name(path.name + '.maint-N6-1792191600-search-evidence.bak')
if not backup.exists():
    shutil.copy2(path, backup)
node = json.loads(path.read_text())
results = {entry['tool']: entry['results'] for entry in json.loads(pathlib.Path('/tmp/n6-search-results.json').read_text())}
for search in node['mathlib_searches']:
    search['results'] = results[search['tool']]
path.write_text(json.dumps(node, indent=1, ensure_ascii=False) + '\n')
subprocess.run(['git', 'diff', '--check', '--', relative], cwd=root, check=True)
if subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', relative], cwd=root).returncode == 0:
    print('ALREADY COMMITTED', relative, flush=True)
    sys.exit(0)
subprocess.run(['git', 'add', '--', relative], cwd=root, check=True)
print('COMMIT PATH', relative, flush=True)
subprocess.run(['git', '-c', 'user.name=Bin Wu', '-c', 'user.email=844524296@qq.com',
                'commit', '--only', '-m', 'N6: retain verbatim foundation search evidence', '--', relative],
               cwd=root, env=dict(os.environ, SHEAF_LEAD='L-only'), check=True)
