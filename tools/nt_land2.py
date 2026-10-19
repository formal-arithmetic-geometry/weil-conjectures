#!/usr/bin/env python3
"""Land a reviewed stage-2 delivery. One DAG (2026-10-18, tools/livedag.py): dag/nodes is the link to the live DAG, so
the merge writes and commits the live node files itself; promote() is a no-op for such a side commit and only copies
the DAG delta of an older side commit (an interrupted landing journalled before the cutover).

nt_land2.py GROUP ITEM HEAD REVIEWER NOTE [--verdict PASS|FIX] [--apply-fixes DIR] [--drop-nodes IDS] [--dry-run]
nt_land2.py return GROUP ITEM NOTE
nt_land2.py --promote SIDE_COMMIT   resumes an interrupted shared-DAG promotion.
nt_land2.py --resume-pending       promotes any side merges interrupted after the side commit.
2026-10-15: never writes live Lean, build requests, ledger, claims, or configuration.
"""
import json
import io
import os
import pathlib
import re
import subprocess
import sys
import tarfile

P = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(P / "tools"))
from mergelock import merge_lock

LIVE = P.parent / "weil-conjectures-sheaf" if P.name != "weil-conjectures-sheaf" else P
TRAILER = "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
ENV = dict(os.environ, SHEAF_LEAD="L-only", SHEAF_DAG="dag/nodes",
           SHEAF_LOCK_TIMEOUT="600", SHEAF_STAGE2_DEFER_QUEUE="1")


def git(root, *args, check=True):
    return subprocess.run(["git", "-c", "user.name=Bin Wu", "-c",
                           "user.email=844524296@qq.com", *args], cwd=root,
                          env=ENV, capture_output=True, text=True, check=check)


class Concurrent(SystemExit):
    """collide fix 2026-10-17: a live change to one node; carries the node path so callers can leave it out."""
    def __init__(self, msg, rel):
        super().__init__(msg)
        self.rel = rel


def live_conflicts(writes, expected):
    """The check of promote() before the side commit: node paths of `writes` (side text before -> after) that live
    changed in a field the delivery also changes. Such a delivery leaves the round (collide fix 2026-10-17)."""
    out = []
    for rel, new in writes.items():
        if not rel.startswith("dag/nodes/"):
            continue
        dst = LIVE / rel
        try:
            cur = json.loads(dst.read_text()) if dst.exists() else None
            after = json.loads(new)
            before = json.loads(expected.get(rel)) if expected.get(rel) else None
        except ValueError:
            continue
        if before is None:
            if cur is not None and cur != after:
                out.append(rel + ": new node exists in live")
            continue
        if cur is None:
            out.append(rel + ": gone from live")
            continue
        for k in set(before) | set(after):
            if before.get(k) != after.get(k) and cur.get(k) not in (before.get(k), after.get(k)):
                out.append(rel + ": " + k)
    return out


def promote(commit, skip=()):
    if LIVE.resolve() == P.resolve():   # 2026-10-19: one repository; the landing committed everything here
        print("PROMOTED", commit, git(P, "rev-parse", "HEAD").stdout.strip(), 0, "DAG files (one repository)")
        return
    # Hold side then live, always in this order; read immutable side commit objects.
    with merge_lock(P / "coord/.merge.lock"), merge_lock(LIVE / "coord/.merge.lock"):
        sha = git(P, "rev-parse", commit).stdout.strip()
        parent = git(P, "rev-parse", sha + "^").stdout.strip()
        files = git(P, "diff", "--name-only", parent, sha, "--", "dag/nodes").stdout.splitlines()
        if not files:
            # One DAG (2026-10-18, tools/livedag.py): the landing wrote the live DAG and committed it there
            # (merge_delivery.git); a side commit carries no DAG delta any more.
            print("PROMOTED", sha, git(LIVE, "rev-parse", "HEAD").stdout.strip(), 0, "DAG files (one DAG: written in live by the landing)")
            return
        files = [f for f in files if f not in skip]
        pending = {}
        for rel in files:
            prior = git(P, "show", parent + ":" + rel, check=False)
            before = json.loads(prior.stdout) if prior.returncode == 0 else None
            after = json.loads(git(P, "show", sha + ":" + rel).stdout)
            dst = LIVE / rel
            current = json.loads(dst.read_text()) if dst.exists() else None
            if before is None:
                if current is not None and current != after:
                    raise Concurrent("Shared DAG new-node collision: " + rel, rel)
                result = after
            else:
                if current is None:
                    raise SystemExit("Shared DAG node disappeared: " + rel)
                result = dict(current)
                keys = {k for k in set(before) | set(after) if before.get(k) != after.get(k)}
                allowed = {"lean", "reviewed_lean", "statement", "stmt_deps", "proof", "proof_deps", "statement_change", "blueprint"}
                if keys - allowed:
                    raise SystemExit("Unexpected stage-2 fields: " + repr(keys - allowed))
                for key in keys:
                    if current.get(key) not in (before.get(key), after.get(key)):
                        raise Concurrent("Shared DAG concurrent change: " + rel + ": " + key, rel)
                    if key in after:
                        result[key] = after[key]
                    else:
                        result.pop(key, None)
            if result == current:
                continue
            dirty = git(LIVE, "status", "--porcelain", "--", rel).stdout.strip()
            if dirty:
                raise SystemExit("Shared DAG path has uncommitted work: " + rel)
            pending[rel] = result
        for rel, result in pending.items():
            dst = LIVE / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(json.dumps(result, indent=1, ensure_ascii=False) + "\n")
        if pending:
            paths = list(pending)
            git(LIVE, "add", "--", *paths)
            print("staged shared DAG:", paths, flush=True)
            git(LIVE, "commit", "-q", "-m", "Stage-2 shared DAG landing " + sha[:12] + "\n\n" + TRAILER,
                "--", *paths)
        live = git(LIVE, "rev-parse", "HEAD").stdout.strip()
        journal = P / "local/stage2/shared" / (sha + ".json")
        journal.parent.mkdir(parents=True, exist_ok=True)
        journal.write_text(json.dumps({"side": sha, "live": live, "paths": files}, indent=2) + "\n")
        print("PROMOTED", sha, live, len(pending), "DAG files")


def main():
    os.environ.update(ENV)
    if len(sys.argv) > 1 and sys.argv[1] == "--prepare-archive":
        import nt_parallel2
        with tarfile.open(fileobj=io.BytesIO(sys.stdin.buffer.read()), mode="r:") as tar:
            rows = json.load(tar.extractfile("manifest.json"))
            members = [m for m in tar.getmembers() if m.name != "manifest.json"]
            for member in members:
                rel = pathlib.PurePosixPath(member.name)
                if (rel.is_absolute() or ".." in rel.parts or member.issym() or member.islnk()
                        or not member.name.startswith("local/stage2/reviews/")):
                    raise SystemExit("Invalid review archive member: " + member.name)
            tar.extractall(P, members=members, filter="data")
        plans = nt_parallel2.prepare(rows)
        print("PLANS_JSON " + json.dumps(plans), flush=True)
        return
    if len(sys.argv) > 1 and sys.argv[1] == "--parallel-commit":
        import nt_parallel2
        value = json.load(sys.stdin)
        nt_parallel2.commit(value["plans"], value["receipts"], promote, value.get("bulk", False))
        return
    if len(sys.argv) > 1 and sys.argv[1] in ("--batch", "--batch-archive"):
        import nt_batch2
        if sys.argv[1] == "--batch-archive":
            with tarfile.open(fileobj=io.BytesIO(sys.stdin.buffer.read()), mode="r:") as tar:
                rows = json.load(tar.extractfile("manifest.json"))
                members = [m for m in tar.getmembers() if m.name != "manifest.json"]
                for member in members:
                    rel = pathlib.PurePosixPath(member.name)
                    if (rel.is_absolute() or ".." in rel.parts or member.issym() or member.islnk()
                            or not member.name.startswith("local/stage2/reviews/")):
                        raise SystemExit("Invalid review archive member: " + member.name)
                tar.extractall(P, members=members, filter="data")
        else:
            rows = json.loads(pathlib.Path(sys.argv[2]).read_text()) if len(sys.argv) > 2 else json.load(sys.stdin)
        with merge_lock(P / "coord/.stage2-promotion.lock"):
            nt_batch2.recover(promote)
            nt_batch2.land(rows, promote)
        return
    if len(sys.argv) > 1 and sys.argv[1] == "--promote":
        with merge_lock(P / "coord/.stage2-promotion.lock"):
            promote(sys.argv[2])
        return
    if len(sys.argv) > 1 and sys.argv[1] == "--resume-pending":
        import nt_batch2
        pending = P / "local/stage2/pending"
        with merge_lock(P / "coord/.stage2-promotion.lock"):
            nt_batch2.recover(promote)
            for record in sorted(pending.glob("*.json")) if pending.exists() else []:
                commit = record.stem
                if record.exists():
                    promote(commit)
                    record.unlink(missing_ok=True)
        return
    if len(sys.argv) > 1 and sys.argv[1] == "return":
        if len(sys.argv) < 4:
            raise SystemExit("usage: nt_land2.py return GROUP ITEM NOTE")
        r = subprocess.run([sys.executable, "tools/nt_merge2.py", "return", sys.argv[2], sys.argv[3],
                            " ".join(sys.argv[4:])], cwd=P, env=ENV, text=True)
        raise SystemExit(r.returncode)
    if len(sys.argv) < 6:
        raise SystemExit("usage: nt_land2.py GROUP ITEM HEAD REVIEWER NOTE [--apply-fixes DIR] [--drop-nodes IDS] [--dry-run]")
    g, item, head, reviewer, note = sys.argv[1:6]
    if not re.fullmatch(r"[A-Z][A-Z0-9]{1,3}", g):
        raise SystemExit("Expected new-targets group")
    args = [sys.executable, "tools/nt_merge2.py", g, item, "--stage", "2",
            "--head", head, "--reviewer", reviewer, "--spot-checked", note]
    tail = sys.argv[6:]
    if "--apply-fixes" in tail:
        i = tail.index("--apply-fixes")
        if i + 1 >= len(tail):
            raise SystemExit("--apply-fixes needs a directory")
        args += ["--apply-fixes", tail[i + 1]]
    if "--drop-nodes" in tail:
        i = tail.index("--drop-nodes")
        if i + 1 >= len(tail):
            raise SystemExit("--drop-nodes needs a comma-separated list")
        args += ["--drop-nodes", tail[i + 1]]
    if "--verdict" in tail:
        i = tail.index("--verdict")
        if i + 1 >= len(tail) or tail[i + 1] not in ("PASS", "FIX"):
            raise SystemExit("--verdict must be PASS or FIX")
        args += ["--verdict", tail[i + 1]]
    if "--dry-run" in tail:
        args.append("--dry-run")
    # Sync must not observe the gap between the side merge and shared promotion.
    with merge_lock(P / "coord/.stage2-promotion.lock"):
        r = subprocess.run(args, cwd=P, env=ENV, capture_output=True, text=True)
        print(r.stdout, end="", flush=True)
        print(r.stderr, end="", file=sys.stderr, flush=True)
        if r.returncode:
            raise SystemExit(r.returncode)
        if "--dry-run" not in tail:
            m = re.search(r"MERGED\s+\S+\s+([0-9a-f]+)", r.stdout)
            if not m:
                raise SystemExit("No merge commit returned; check before promoting")
            sha = git(P, "rev-parse", m.group(1)).stdout.strip()
            pending = P / "local/stage2/pending"
            pending.mkdir(parents=True, exist_ok=True)
            record = pending / (sha + ".json")
            record.write_text(json.dumps({"side": sha, "group": g, "item": item, "delivery_head": head}) + "\n")
            promote(sha)
            record.unlink(missing_ok=True)


if __name__ == "__main__":
    main()
