"""Read-only incident replay: git show and batch JSON only; no builds or live writes.
Usage: python3 tools/replay_red_batch.py <closed-batch.json> <snapshot-commit>
"""
import json, pathlib, sys
import batch_recovery as r
import stage3_delivery as s3


def main():
    b = json.loads(pathlib.Path(sys.argv[1]).read_text())
    root = pathlib.Path(__file__).resolve().parent.parent
    snapshot = sys.argv[2]
    # Read a snapshot into an isolated temporary git checkout, not the live tree.
    import tempfile, subprocess
    with tempfile.TemporaryDirectory(prefix='red-batch-replay-') as d:
        subprocess.run(['git', 'clone', '-q', '--shared', '--no-checkout', str(root), d], check=True)
        subprocess.run(['git', '-C', d, 'checkout', '-q', '--detach', snapshot], check=True)
        e = next(e for e in b['entries'] if e['commit'].startswith('316464bcc'))
        prepared = r.inverse(d, [e['commit']], imports_only=True)
        p = s3.path_of_module(e['item'])
        old = r.blob(d, e['commit'] + '^', p)
        allowed = sorted(k for k, v in s3.decl_table(prepared[p].decode()).items() if v['sorry'])
        print(json.dumps({'batch': b['id'], 'at': '2026-10-12 15:37:29 +08',
            'decision': 'take out Q1; restore records and claim; return compiler message and triage reason',
            'restored_paths': len(prepared), 'sorry_allowed': allowed,
            'source_matches_prelanding': prepared[p] == old,
            'builds_after_takeout': 1, 'counterfactual_seconds': 16,
            'estimate_basis': 'final observed green reused compiled snapshot; actual restored source recompilation may take longer'}, indent=2))
        import import_cycles as cycles
        imports = cycles.graph(pathlib.Path(d) / 'lean')
        deps = r.dependents(b['entries'], [e], imports)
        print(json.dumps({'dependent_deliveries_waiting': [x['item'] for x in deps],
                          'survivors': len(b['entries']) - 1 - len(deps),
                          'one_bad_oracle_builds': 2,
                          'warning': 'initial red plus survivor build; source-only oracle, no claim that replay compiles'}, indent=2))


if __name__ == '__main__': main()
