#!/usr/bin/env python3
"""Atomic stage-2 batches. The caller holds the promotion guard.

Reuse the ordinary merger's local checks and both single-file compile passes.
The merge lock protects a mutable source index, the combined DAG checks, queue,
bookkeeping and commit. A write-ahead journal restores an interrupted uncommitted
batch; committed batches are promoted before their delivery refs are retired.
"""
import argparse
import base64
import contextlib
import io
import json
import os
import pathlib
import re
import subprocess
import sys
import time
import uuid

os.environ['SHEAF_LEAD'] = 'L-only'
import merge_delivery as md
import leanindex as li
import dag_delta
import import_prune_check as prune

P = md.ROOT
TRAILER = 'Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>'
TX = P / 'local/stage2/pending'


def atomic(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix('.tmp')
    with tmp.open('w') as f:
        json.dump(value, f, ensure_ascii=False)
        f.flush()
        os.fsync(f.fileno())
    tmp.replace(path)


def restore(files):
    for rel, data in files.items():
        path = P / rel
        if data is None:
            path.unlink(missing_ok=True)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(base64.b64decode(data))


def retire(rows):
    for row in rows:
        # A worker may have pushed a replacement while this batch was checking.
        md.git('update-ref', '-d', 'refs/heads/' + row['branch'], row['head'], check=False)


def release_claims(record):
    """After durable promotion, release claims, with idempotent crash recovery."""
    if not record.get('defer_claims'):
        return
    paths=set()
    for row in record['rows']:
        _, group, item=row['branch'].split('/', 2)
        done=subprocess.run([sys.executable,'tools/claim.py','done',group,item,
                             'stage-2 reviewed batch '+record['id']+' committed and promoted'],
                            cwd=P,capture_output=True,text=True)
        if done.returncode and done.stdout.strip()!='not your claim':
            raise md.Fail('claim.py done after promotion: '+done.stdout+done.stderr)
        rel='coord/claims/'+item.replace('/', '__')+'.lock'
        if md.exists_at('HEAD',rel):paths.add(rel)
        note='coord/repair-notes/'+item+'.json'
        if md.exists_at('HEAD',note):paths.add(note)
    paths.add('coord/deliveries.log')
    changed=set(md.git('diff','--name-only','--',*paths).splitlines())
    if changed:
        print('staged claim paths:',sorted(changed),flush=True)
        md.git_retry('add','--',*sorted(changed))
        md.git_retry('commit','-q','-m','Release promoted stage-2 batch '+record['id'],'--',*sorted(changed))


def committed(record):
    if record.get('commit'):
        return record['commit']
    # Handles a crash after git commit but before the journal records its SHA.
    out = md.git('log', '--format=%H', '--fixed-strings', '--grep',
                 'Stage-2 batch ' + record['id'], record['base'] + '..HEAD')
    return out.splitlines()[0] if out else None


def promote_skipping(promote, sha, rid=''):
    """collide fix 2026-10-17: promote a committed side batch; a node live changed concurrently is left out
    (recorded in local/stage2/unpromoted.tsv) instead of blocking this and every later batch."""
    skipped = []
    while True:
        try:
            if skipped:
                promote(sha, skip=tuple(skipped))
            else:
                promote(sha)
            break
        except SystemExit as exc:
            rel = getattr(exc, 'rel', None)
            if not rel or rel in skipped or len(skipped) > 200:
                raise
            skipped.append(rel)
            print('LIVE PROMOTION LEAVES OUT', rel, str(exc), flush=True)
            with open(TX.parent / 'unpromoted.tsv', 'a') as fh:
                fh.write('\t'.join([time.strftime('%F %T'), sha, rid, rel, str(exc)]) + '\n')
    return skipped


def recover(promote):
    """Called under the promotion guard, before sync can see a partial batch."""
    for path in sorted(TX.glob('batch-*.json')):
        with md.merge_lock():
            record = json.loads(path.read_text())
            sha = committed(record)
            if not sha:
                restore(record['originals'])
                # Only paths owned by this journal could have reached the index.
                if record['originals']:
                    md.git('reset', '-q', 'HEAD', '--', *record['originals'])
                path.unlink()
                print('BATCH ROLLED BACK', record['id'], flush=True)
                continue
        promote_skipping(promote, sha, record['id'])
        with md.merge_lock():
            release_claims(record)
            retire(record['rows'])
            path.unlink()
        print('BATCH RECOVERED', record['id'], sha, flush=True)


class SourceIndex:
    """Exactly the ordinary lexer results, updated for each changed module."""
    def __init__(self):
        self.loaded = False
        self.decls = self.imports = self.statements = None
        self.by_module = {}
        self.scan = li.scan
        self.library_statements = li.library_statements

    def load(self):
        if self.loaded:
            return
        start = time.monotonic()
        self.decls, self.imports = self.scan()
        self.statements = self.library_statements()
        for q, modules in self.decls.items():
            for mod in modules:
                self.by_module.setdefault(mod, [set(), set()])[0].add(q)
        for statement, values in self.statements.items():
            for q, mod in values:
                self.by_module.setdefault(mod, [set(), set()])[1].add((statement, q))
        self.loaded = True
        print('BATCH SOURCE INDEX', round(time.monotonic() - start, 2), 's', flush=True)

    def refresh(self, rel):
        if not self.loaded or not rel.startswith('lean/') or not rel.endswith('.lean'):
            return
        mod = rel[5:-5].replace('/', '.')
        if mod.split('.')[0] not in li.library_dirs() and mod not in ('Challenge', 'TargetsCheck'):
            return
        old_names, old_statements = self.by_module.pop(mod, (set(), set()))
        for q in old_names:
            self.decls[q].discard(mod)
        for statement, q in old_statements:
            self.statements[statement].discard((q, mod))
        path = P / rel
        if not path.exists():
            self.imports.pop(mod, None)
            return
        text = path.read_text(errors='ignore')
        names = li.decls_in_text(text) if mod != 'Challenge' else set()
        statements = {(s, q) for q, s in li.statements_in_text(text).items() if s} if mod not in ('Challenge', 'TargetsCheck') else set()
        self.by_module[mod] = [names, statements]
        for q in names:
            self.decls[q].add(mod)
        for statement, q in statements:
            self.statements[statement].add((q, mod))
        self.imports[mod] = li.imports_of(text)

    @contextlib.contextmanager
    def use(self, rel):
        self.load()
        self.refresh(rel)
        li.scan = lambda: (self.decls, dict(self.imports))
        li.library_statements = lambda: self.statements
        try:
            yield
        finally:
            li.scan = self.scan
            li.library_statements = self.library_statements


class Tree:
    def __init__(self, batch):
        self.batch = batch
        self.originals = {}

    def remember(self, rel):
        if rel in self.originals:
            return
        if rel in self.batch.owned:
            raise md.Fail('BATCH RETRY: path also owned by an earlier delivery: ' + rel)
        if rel in self.batch.dirty and rel.startswith(('dag/nodes/', 'lean/Sheaf/', 'coord/reports/')):
            raise md.Fail('BATCH RETRY: path has pre-existing uncommitted work: ' + rel)
        path = P / rel
        data = base64.b64encode(path.read_bytes()).decode() if path.is_file() else None
        self.originals[rel] = data
        self.batch.remember(rel, data)

    def write(self, rel, text):
        self.remember(rel)
        path = P / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def restore(self):
        restore(self.originals)
        for rel in self.originals:
            self.batch.index.refresh(rel)


def split_findings(text):
    rows, item = {}, None
    for line in text.splitlines():
        if line and not line.startswith(' '):
            item = line.split(':', 1)[0]
            rows.setdefault(item, set())
        elif item and line.startswith('  '):
            rows[item].add(line.strip())
    return rows


def run_tool(name, *args):
    r = subprocess.run([sys.executable, 'tools/' + name, *args], cwd=P,
                       capture_output=True, text=True)
    if r.returncode not in (0, 1):
        raise md.Fail(name + ' failed: ' + (r.stdout + r.stderr)[-2000:])
    if r.stderr.strip():
        raise md.Fail(name + ' stderr: ' + r.stderr[-2000:])
    return r.stdout


class Batch:
    def __init__(self, rows):
        self.rows, self.staged, self.owned = rows, [], set()
        self.index = SourceIndex()
        self.id = uuid.uuid4().hex
        self.path = TX / ('batch-' + self.id + '.json')
        self.record = {'id': self.id, 'base': md.git('rev-parse', 'HEAD'), 'originals': {}, 'rows': []}
        # Git emits NUL separated paths; delivery paths cannot contain tabs/newlines.
        self.dirty = {x[3:] for x in md.git('status', '--porcelain', '-z').split('\0') if x}
        atomic(self.path, self.record)

    def remember(self, rel, data=None):
        if rel in self.record['originals']:
            return
        path = P / rel
        if data is None and path.is_file():
            data = base64.b64encode(path.read_bytes()).decode()
        self.record['originals'][rel] = data
        atomic(self.path, self.record)

    def prepare_originals(self, rels):
        """Write the complete rollback inventory once before the first mutation."""
        for rel in rels:
            if rel not in self.record['originals']:
                path=P/rel
                self.record['originals'][rel]=base64.b64encode(path.read_bytes()).decode() if path.is_file() else None
        atomic(self.path,self.record)

    def tree(self):
        return Tree(self)

    def land(self, sand, dst):
        # Keep BOTH compile passes, at the sandbox path and at the library path.
        outputs = []
        for path in (sand, dst):
            if path == dst:
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_bytes(sand.read_bytes())
            r = subprocess.run(['bash', str(P / 'tools/lean_file.sh'), str(path)], cwd=P,
                               env=dict(os.environ, SHEAF_GROUP='L'), capture_output=True, text=True)
            outputs.append(r.stdout + r.stderr)
            if r.returncode:
                return subprocess.CompletedProcess([], r.returncode, ''.join(outputs), '')
        rel = dst.relative_to(P).as_posix()
        original = self.record['originals'][rel]
        old = self.path.with_suffix('.old')
        old.write_bytes(base64.b64decode(original) if original is not None else b'')
        output = io.StringIO()
        argv = sys.argv
        try:
            sys.argv = ['import_prune_check.py', li.module_of(dst), str(old), str(dst)]
            with self.index.use(rel), contextlib.redirect_stdout(output):
                rc = prune.main()
        finally:
            sys.argv = argv
            old.unlink(missing_ok=True)
        outputs.append(output.getvalue())
        if rc == 0:
            outputs.append('Landed ' + li.module_of(dst) + ' as landing nt-batch-' + self.id + '\n')
        return subprocess.CompletedProcess([], rc, ''.join(outputs), '')

    def stage(self, o, tree, paths, nodes, ltext, msg, branch):
        self.staged.append({'o': o, 'tree': tree, 'paths': paths, 'nodes': nodes,
                            'ledger': ltext, 'message': msg, 'branch': branch, 'head': o.head})
        self.owned.update(tree.originals)
        print('BATCH STAGED', o.item, flush=True)

    def rollback(self):
        restore(self.record['originals'])
        for rel in self.record['originals']:
            self.index.refresh(rel)
        self.staged.clear()
        self.owned.clear()

    def checks(self, baseline, split_base):
        ids = {nid for row in self.staged for nid in row['nodes']}
        for row in self.staged:
            for rel in row['nodes'].values():
                row['tree'].remember(rel)
        md.backfill_blueprint(ids)
        current = run_tool('check_dag.py', '--cycles')
        bad = dag_delta.introduced(current, baseline, ids)
        split = split_findings(run_tool('review_split.py', '--stage2', *(row['o'].item for row in self.staged)))
        for item, findings in split.items():
            bad.extend(item + ': ' + f for f in sorted(findings - split_base.get(item, set())))
        print('BATCH DAG CHECK', len(self.staged), 'deliveries;', len(bad), 'findings', flush=True)
        return bad

    def finish(self):
        paths = {p for row in self.staged for p in row['paths']}
        for row in self.staged:
            o = row['o']
            rp, text, parts = md.return_entries(o.group, o.item)
            keep = [x for x in parts if not x.startswith(f'## {o.item} (')]
            if text is not None and len(keep) != len(parts):
                rel = rp.relative_to(P).as_posix()
                self.remember(rel)
                rp.write_text(''.join(keep))
                paths.add(rel)
            claim = P / 'coord/claims' / (o.item.replace('/', '__') + '.lock')
            rel = claim.relative_to(P).as_posix()
            self.remember(rel)
            self.remember('coord/repair-notes/' + o.item + '.json')
            self.remember('coord/deliveries.log')
            self.remember('coord/ledger.md')
            done = (subprocess.CompletedProcess([],0,'done (after promotion)','') if getattr(self,'defer_claims',False) else
                    subprocess.run([sys.executable, 'tools/claim.py', 'done', o.group, o.item,
                                   f'delivered by {o.group} on {row["branch"]}, merged by L (reviewer {o.reviewer})'],
                                  cwd=P, text=True, capture_output=True))
            if done.returncode and done.stdout.strip() != 'not your claim':
                raise md.Fail('claim.py done: ' + done.stdout + done.stderr)
            md.ledger_line(row['ledger'] + ('' if done.stdout.startswith('done') else '; claim: ' + done.stdout.strip()))
            if md.exists_at('HEAD', rel):
                paths.add(rel)
        # Refresh exactly once; failures abort the transaction rather than silently
        # publishing a batch whose bookkeeping could not be regenerated.
        for rel in (() if getattr(self, 'defer_queue', False) else ('coord/queue.tsv', 'coord/queue.md', 'coord/blueprint-index.tsv')):
            self.remember(rel)
            paths.add(rel)
        r = (subprocess.CompletedProcess([], 0, '', '') if getattr(self, 'defer_queue', False) else
             subprocess.run([sys.executable, 'tools/queue.py', 'write'], cwd=P, capture_output=True, text=True))
        if r.returncode:
            raise md.Fail('queue.py write: ' + r.stdout + r.stderr)
        paths = sorted(p for p in paths if (P / p).exists() or md.exists_at('HEAD', p))
        self.record['defer_claims']=getattr(self,'defer_claims',False)
        self.record['rows'] = [{'branch': r['branch'], 'head': r['head']} for r in self.staged]
        atomic(self.path, self.record)
        message = 'Stage-2 batch ' + self.id + f' ({len(self.staged)} reviewed deliveries)\n\n'
        message += '\n'.join(r['message'] for r in self.staged)
        print('staged side paths:', paths, flush=True)
        md.git_retry('add', '--', *paths)
        md.git_retry('commit', '-q', '-m', message, '--', *paths)
        sha = md.git('rev-parse', 'HEAD')
        self.record['commit'] = sha
        atomic(self.path, self.record)
        record_landings(self.staged, sha)
        return sha


def record_landings(staged, sha):
    """Merge queue (2026-10-19): the Lean files of each reviewed stage-2 delivery are one landing of its group, with the
    delivery named, so that a red build that drops it returns it to the group (tools/batch_land.py)."""
    import landing as ld
    if not ld.merge_queue():
        return
    with ld.tree_lock():
        for row in staged:
            o = row['o']
            files = {rel[len('lean/'):]: (base64.b64decode(v) if v is not None else None)
                     for rel, v in row['tree'].originals.items() if rel.startswith('lean/') and rel.endswith('.lean')}
            files = {rel: b for rel, b in files.items() if ld.sha(li.LEAN / rel) != (__import__('hashlib').sha256(b).hexdigest() if b is not None else None)}
            if files:
                ld.new_record(o.group, files, f'stage 2: {o.item} (commit {sha[:10]})',
                              extra={'delivery': {'group': o.group, 'item': o.item, 'head': o.head}, 'stage': 2})


def options(row):
    for key in ('group', 'item', 'head', 'reviewer', 'note'):
        if not isinstance(row.get(key), str) or not row[key]:
            raise ValueError('missing ' + key)
    if not re.fullmatch('[A-Z][A-Z0-9]{1,3}', row['group']) or not re.fullmatch('[0-9a-f]{40}', row['head']):
        raise ValueError('invalid group/head')
    if not re.fullmatch('[a-zA-Z0-9_-]+', row['item']):
        raise ValueError('invalid item')
    if row.get('verdict', 'PASS') not in ('PASS', 'FIX', 'RETURN'):
        raise ValueError('invalid verdict')
    return argparse.Namespace(group=row['group'], item=row['item'], head=row['head'],
                              reviewer=row['reviewer'], spot_checked=row['note'],
                              apply_fixes=row.get('apply_fixes'), drop_nodes=','.join(row.get('drop_nodes') or []),
                              revert_nodes=None, drop_files=None, revert_statement=False,
                              verdict=row.get('verdict', 'PASS'), dry_run=False)


def land(rows, promote):
    # Validate the entire manifest before the first mutation.
    opts = [options(r) for r in rows]
    if len({(o.group, o.item) for o in opts}) != len(opts):
        raise ValueError('duplicate delivery in batch')
    results, returns = {}, []
    with md.merge_lock():
        batch = Batch(rows)
        try:
            candidates = []
            for o in opts:
                ref = 'refs/heads/' + md.branch_of(o.group, o.item)
                current = md.git('rev-parse', '-q', '--verify', ref, check=False)
                if current != o.head:
                    results[o.head] = {'result': 'retired'}
                elif o.verdict == 'RETURN':
                    returns.append((o, o.spot_checked))
                else:
                    candidates.append(o)
            if candidates:
                baseline = run_tool('check_dag.py', '--cycles')
                split_base = split_findings(run_tool('review_split.py', '--stage2', *(o.item for o in candidates)))
                while candidates:
                    for o in candidates:
                        started = time.monotonic()
                        try:
                            md.cmd_merge2(o, batch=batch)
                        except md.Fail as exc:
                            reason = str(exc)
                            if 'BATCH RETRY:' in reason:
                                results[o.head] = {'result': 'retry', 'note': reason}
                            else:
                                returns.append((o, reason))
                            print('BATCH REFUSED', o.item, reason, flush=True)
                        print('BATCH LOCAL CHECK', o.item, round(time.monotonic() - started, 2), 's', flush=True)
                    if not batch.staged:
                        break
                    bad = batch.checks(baseline, split_base)
                    if not bad:
                        break
                    # Use named nodes to find an owner, never test arbitrary halves.
                    offenders = set()
                    for finding in bad:
                        owners = [r for r in batch.staged if dag_delta.mentions(finding, r['nodes'])]
                        if not owners:
                            raise md.Fail('unattributed batch check; kept all deliveries: ' + finding)
                        offenders.add(owners[-1]['head'])
                    survivors = []
                    for r in batch.staged:
                        if r['head'] in offenders:
                            returns.append((r['o'], 'batch DAG validation: ' + ' | '.join(bad)))
                        else:
                            survivors.append(r['o'])
                    batch.rollback()
                    candidates = survivors
                if batch.staged:
                    sha = batch.finish()
                    for row in batch.staged:
                        results[row['head']] = {'result': row['o'].verdict, 'side': sha}
                else:
                    sha = None
            else:
                sha = None
            if not sha:
                batch.rollback()
                batch.path.unlink()
        except BaseException:
            if not committed(batch.record):
                batch.rollback()
                if batch.record['originals']:
                    md.git('reset', '-q', 'HEAD', '--', *batch.record['originals'])
                batch.path.unlink(missing_ok=True)
            raise
    if sha:
        promote(sha)
        with md.merge_lock():
            retire(batch.record['rows'])
            batch.path.unlink()
        for row in batch.staged:
            print('MERGED', row['o'].item, sha, flush=True)
    # Returns take the ordinary merge lock and independently recheck immutable heads.
    for o, reason in returns:
        with md.merge_lock():
            current = md.git('rev-parse', '-q', '--verify', 'refs/heads/' + md.branch_of(o.group, o.item), check=False)
        if current != o.head:
            results[o.head] = {'result': 'retired'}
            continue
        md.cmd_return(o.group, o.item, 'L: independent stage-2 review returned immutable head ' + o.head[:12] + ': ' + reason)
        results[o.head] = {'result': 'RETURN', 'note': reason}
    print('BATCH_RESULT ' + json.dumps(results), flush=True)
    return results
