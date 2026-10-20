"""Isolated packet validation; never changes the project's library or delivery refs."""
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tarfile

PROJECT = pathlib.Path('/home/ubuntu/weil-conjectures-sheaf')
ROOT = pathlib.Path('/home/ubuntu/weil-maint-A9-retirement-1792503000')
ITEM = 'Sheaf.AlgebraicGeometry.EtaleFieldGsets'
ROOT.mkdir(exist_ok=True)
SB = ROOT / 'packet'
SB.mkdir(exist_ok=True)
with tarfile.open('/tmp/A9-retirement-1792503000.tar.gz') as archive:
    archive.extractall(SB, filter='data')
WORK = ROOT / 'preflight-worktree'
subprocess.run(['git', 'worktree', 'add', '--detach', str(WORK), 'HEAD'], cwd=PROJECT, check=True)
base = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=WORK, text=True).strip()
paths = []
for tree in ['lean', 'dag', 'coord']:
    for source in sorted((SB / tree).rglob('*')):
        if not source.is_file():
            continue
        rel = source.relative_to(SB)
        dest = WORK / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        if dest.exists():
            shutil.copy2(dest, str(dest) + '.bak')
        shutil.copy2(source, dest)
        paths.append(str(rel))
for rel in (SB / 'deleted.txt').read_text().splitlines():
    if not rel or rel.startswith('#'):
        continue
    dest = WORK / rel
    shutil.copy2(dest, str(dest) + '.bak')
    dest.write_text('module\n\n/-! Withdrawn: no declarations remain. -/\n')
    paths.append(rel)
report_path = pathlib.Path('coord/reports/A9') / (ITEM + '.md')
dest = WORK / report_path
dest.parent.mkdir(parents=True, exist_ok=True)
if dest.exists():
    shutil.copy2(dest, str(dest) + '.bak')
dest.write_text((SB / 'report.md').read_text() + '\n## Second reading by A9\n\n'
                'No second reading by a worker: the maintainer independently reviews the delivery.\n')
paths.append(str(report_path))
subprocess.run(['git', 'add', '--', *paths], cwd=WORK, check=True)
env = dict(os.environ, SHEAF_LEAD='L-only')
subprocess.run(['flock', str(PROJECT / 'coord/.merge.lock'), 'git', '-c', 'user.name=Bin Wu',
                '-c', 'user.email=844524296@qq.com', 'commit', '-m', 'Validate A9 retirement packet in isolation'],
               cwd=WORK, env=env, check=True)
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=WORK, text=True).strip()
(ROOT / 'validation-commits.json').write_text(json.dumps(dict(base=base, packet=head), indent=2) + '\n')
env['SHEAF_COMPILE_ROOT'] = '/nonexistent'
with (ROOT / 'server-preflight.log').open('w') as log:
    result = subprocess.run([sys.executable, 'tools/preflight_delivery.py', 'A9', ITEM,
                             '--stage', '3', '--base', base], cwd=WORK, env=env, stdout=log, stderr=subprocess.STDOUT)
print((ROOT / 'server-preflight.log').read_text(), flush=True)
if result.returncode:
    sys.exit(result.returncode)

# The standard wrapper reads the published build and writes only the unique
# group's private mirror. No build command or shared artifact write is used.
lake = WORK / 'lean/.lake'
lake.mkdir(exist_ok=True)
(lake / 'packages').symlink_to((PROJECT / 'lean/.lake/packages').resolve(), target_is_directory=True)
(lake / 'build').symlink_to((PROJECT / 'lean/.lake/build').resolve(), target_is_directory=True)
sys.path.insert(0, str(WORK / 'tools'))
import stage2_delivery as s2
files = sorted((SB / 'lean').rglob('*.lean'))
mods = {str(p.relative_to(SB / 'lean').with_suffix('')).replace('/', '.'): p for p in files}
done = set()
env = dict(os.environ, SHEAF_LEAD='L-only', SHEAF_GROUP='MA9RETIRE1792503000',
           SHEAF_TREE=str(WORK / 'lean'), SHEAF_FILE_TIMEOUT='60')
with (ROOT / 'server-consumers-compile.log').open('w') as log:
    while len(done) < len(mods):
        ready = sorted(m for m, p in mods.items() if m not in done and
                       (set(s2.imports(p.read_text())) & set(mods)) <= done)
        if not ready:
            raise RuntimeError('Packet import cycle')
        for module in ready:
            target = WORK / mods[module].relative_to(SB)
            log.write('\n' + module + '\n'); log.flush()
            result = subprocess.run(['bash', str(PROJECT / 'tools/lean_file.sh'), str(target)],
                                    cwd=PROJECT, env=env, stdout=log, stderr=subprocess.STDOUT)
            log.flush()
            print(module, 'exit', result.returncode, flush=True)
            if result.returncode:
                print((ROOT / 'server-consumers-compile.log').read_text()[-5000:], flush=True)
                sys.exit(result.returncode)
            done.add(module)
print('All', len(done), 'packet files compiled individually through tools/lean_file.sh, timeout 60 s.', flush=True)
