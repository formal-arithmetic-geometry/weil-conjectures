import os
import pathlib
import shutil
import subprocess

root = pathlib.Path('/home/ubuntu/weil-newtargets')
source = pathlib.Path('/tmp/n6-maint-handoff')
tag = '.maint-N6-1792191600.bak'
files = [('REPORT.md', 'coord/reports/maintenance/N6-coherent-diagrams.md'),
         ('evidence/worker-handoff.md', 'tools/launcher/route-notes/lem-coef-simplicial-model-coherent-diagrams.md')]
for path in (source / 'evidence').iterdir():
    if path.is_file() and not path.name.endswith('.bak'):
        files.append(('evidence/' + path.name, 'coord/reports/maintenance/N6-coherent-diagrams-evidence/' + path.name))
changed = []
for src, dest in files:
    path = root / dest
    path.parent.mkdir(parents=True, exist_ok=True)
    backup = path.with_name(path.name + tag)
    if path.exists() and not backup.exists():
        shutil.copy2(path, backup)
    shutil.copy2(source / src, path)
    if not backup.exists():
        shutil.copy2(path, backup)
    changed.append(dest)
subprocess.run(['git', 'diff', '--check', '--'] + changed, cwd=root, check=True)
subprocess.run(['git', 'add', '--'] + changed, cwd=root, check=True)
print('COMMIT PATHS', *changed, sep='\n', flush=True)
subprocess.run(['git', '-c', 'user.name=Bin Wu', '-c', 'user.email=844524296@qq.com',
                'commit', '--only', '-m', 'N6: record durable cycle repair and worker handoff', '--'] + changed,
               cwd=root, env=dict(os.environ, SHEAF_LEAD='L-only'), check=True)
