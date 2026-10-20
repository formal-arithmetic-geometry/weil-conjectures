"""Show the real original consumer fails once the delivery's withdrawal is applied."""
import json
import os
import pathlib
import subprocess

PROJECT = pathlib.Path('/home/ubuntu/weil-conjectures-sheaf')
ROOT = pathlib.Path('/home/ubuntu/weil-maint-A9-retirement-1792503000')
WORK = ROOT / 'preflight-worktree'
module = pathlib.Path('lean/Sheaf/CategoryTheory/DiscreteContActionFiniteOrbitCoproduct.lean')
deleted = WORK / 'lean/Sheaf/AlgebraicGeometry/EtaleFieldGsets.lean'
base = json.loads((ROOT / 'validation-commits.json').read_text())['base']
original = WORK / 'lean/.sandbox/MA9COUNTERFACTUAL/OrbitBefore.lean'
original.parent.mkdir(parents=True, exist_ok=True)
original.write_bytes(subprocess.check_output(['git', 'show', base + ':' + str(module)], cwd=WORK))
env = dict(os.environ, SHEAF_TREE=str(WORK / 'lean'), SHEAF_FILE_TIMEOUT='60')

with (ROOT / 'server-counterfactual.log').open('w') as log:
    def compile_file(label, file, group):
        log.write('\n' + label + '\n'); log.flush()
        result = subprocess.run(['bash', str(PROJECT / 'tools/lean_file.sh'), str(file)], cwd=PROJECT,
                                env=dict(env, SHEAF_GROUP=group), stdout=log, stderr=subprocess.STDOUT)
        log.write('exit code: ' + str(result.returncode) + '\n'); log.flush()
        return result.returncode
    assert compile_file('Original against published baseline', original, 'MA9RETIREBASE1792503000') == 0
    assert compile_file('Real empty withdrawal module', deleted, 'MA9RETIRE1792503000') == 0
    assert compile_file('Original against withdrawn dependency', original, 'MA9RETIRE1792503000') == 1
    assert compile_file('Adapted consumer against withdrawn dependency', WORK / module, 'MA9RETIRE1792503000') == 0

print((ROOT / 'server-counterfactual.log').read_text(), flush=True)
