#!/usr/bin/env python3
"""Durable repair outbox. list/status/result are source-only (no compiler).

Take-out stages a request before committing; its dedicated XR<hash> claim is the
activation token. A crash before/after commit is harmless: list checks the claim.
Original returns are removed in the same inverse transaction. Jobs keep original
source diff, compiler messages, snapshot tip and scope. Repaired deliveries use
normal deliver/XR<hash>/<item> branches and independent reading/static gates.
"""
import hashlib, json, pathlib, subprocess, sys, time
import leanindex as li
ROOT = li.ROOT
JOBS = ROOT / 'local/batch/repair'
NOTES = ROOT / 'coord/repair-notes'

def read(p):
    try: return json.loads(p.read_text())
    except (OSError, ValueError): return {}

def write(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix('.tmp'); tmp.write_text(json.dumps(data, ensure_ascii=False, indent=1)); tmp.replace(p)

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

def claim_path(item): return ROOT / 'coord/claims' / (item.replace('/', '__') + '.lock')

def stage(entry, tip, decisions, reason):
    ident = hashlib.sha256((entry['landing'] + entry['head']).encode()).hexdigest()[:16]
    p = JOBS / (ident + '.json')
    job = read(p)
    if not job:
        job = dict(id=ident, group='XR' + ident, original_group=entry['group'],
                   item=entry['item'], head=entry['head'], landing=entry['landing'],
                   commit=entry['commit'], tip=tip, modules=entry['modules'],
                   failures=sorted({d['failure'] for d in decisions}), decisions=decisions,
                   reason=reason, diff=git('diff', entry['commit']+'^', entry['commit'], '--', 'lean', 'dag/nodes', 'coord/changes'),
                   state='pending', created=time.time(), attempts=0)
        if entry['group'].startswith('XR'):
            parent = read(JOBS / (entry['group'][2:] + '.json'))
            job['attempts'] = parent.get('attempts', 0)
            job['prior_notes'] = parent.get('note', '')
            if parent:
                parent['state'] = 'superseded'; write(JOBS / (parent['id']+'.json'), parent)
        write(p, job)
    return job

def active(job):
    c = read(claim_path(job['item']))
    return c.get('who') == job['group']

def jobs(): return [read(p) for p in sorted(JOBS.glob('*.json'))] if JOBS.exists() else []

def counts():
    out = dict(repaired_in_place=0, released_to_queue=0, repair_still_running=0)
    for j in jobs():
        if j.get('state') == 'released': out['released_to_queue'] += 1
        elif j.get('state') == 'repaired': out['repaired_in_place'] += 1
        elif j.get('state') == 'delivered' or active(j): out['repair_still_running'] += 1
    return out

def result(ident, outcome, note, head='', attempts=0):
    import claim, merge_delivery as md, batch_land as bl
    p = JOBS / (ident + '.json'); j = read(p)
    if not j: raise RuntimeError('unknown repair')
    if j.get('state') in ('released', 'repaired'): return j
    if not active(j): raise RuntimeError('repair claim no longer owned')
    j.update(attempts=attempts, note=note, updated=time.time())
    if outcome == 'delivered':
        branch = 'deliver/' + j['group'] + '/' + j['item']
        actual = git('rev-parse', branch)
        allowed = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', j['commit']).splitlines())
        allowed.update('lean/'+m.replace('.','/')+'.lean' for m in j['failures'])
        allowed.add('coord/reports/'+j['group']+'/'+j['item']+'.md')
        base = git('merge-base','sheaf-dag',actual)
        changed = set(git('diff','--name-only',base,actual).splitlines())
        if changed - allowed: raise RuntimeError('repair exceeded recorded scope: '+repr(changed-allowed))
        if actual != head: raise RuntimeError('repair branch moved')
        # Normal static/reader gates; no compiler on server.
        import argparse
        bl.cmd_pass(argparse.Namespace(group=j['group'], item=j['item'], head=head,
                    reviewer='XREPAIR-'+ident, apply_fixes=None, dry_run=False,
                    verdict='PASS', spot_checked=note[-4000:]))
        mk = bl.marker(j['group'], j['item']); data = read(mk)
        data['repair_priority'] = True; write(mk, data)
        j.update(state='delivered', repaired_head=head)
    elif outcome == 'failed':
        # Serialize claim/branch cleanup with landings. Claim.py performs the
        # abandonment and removes returns; original group's branch is already gone.
        with md.merge_lock():
            if not active(j): raise RuntimeError('repair claim moved')
            note_data = dict(j, state='released', note=note)
            write(NOTES / (j['item']+'.json'), note_data)
            rc = subprocess.run([sys.executable, 'tools/claim.py', 'release', j['group'], j['item'],
                                 'abandon: dedicated repair failed; '+j['reason']+'; tried: '+note], cwd=ROOT).returncode
            if rc: raise RuntimeError('claim release failed')
            ref = 'refs/heads/deliver/'+j['group']+'/'+j['item']
            subprocess.run(['git', 'update-ref', '-d', ref], cwd=ROOT, check=True)
            bl.marker(j['group'], j['item']).unlink(missing_ok=True)
            j['state'] = 'released'
        bl.refresh_recovery_queue()
    else: j['state'] = 'running'
    write(p,j); return j

def reconcile():
    import landing as ld
    pending = [j for j in jobs() if j.get('state') == 'delivered']
    for j in pending:
        records = [ld.DONE / (j['repair_landing']+'.json')] if j.get('repair_landing') else []
        for p in records:
            r = read(p)
            if r.get('group') == j['group'] and r.get('item') == j['item'] and r.get('result') == 'verified':
                j.update(state='repaired', verified=time.time()); write(JOBS/(j['id']+'.json'),j); break

if __name__ == '__main__':
    a=sys.argv[1:]; cmd=a[0] if a else 'status'
    if cmd == 'list': print(json.dumps([j for j in jobs() if j.get('state') in ('pending','running') and active(j)]))
    elif cmd == 'status': reconcile(); print(json.dumps(counts()))
    elif cmd == 'result':
        data=json.load(sys.stdin); print(json.dumps(result(a[1], **data)))
    else: raise SystemExit('list | status | result ID < JSON')
