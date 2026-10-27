#!/usr/bin/env python3
"""A commit that deletes or moves a Lean file must update the DAG nodes recording it (the human, 2026-10-24: "删模块之后
要同步修改DAG节点文件，不能不管"; a module deleted as dead on 10-20 was later back on batch 2's route while its node
still named the missing file, and nobody got the task).

It never refuses anything (the human, 2026-10-24: a check returns information or calls an agent; it does not block).
Run as the live repository's post-commit hook (.git/hooks/post-commit): it reads the commit just made, every file
under lean/ it deleted or renamed, except a move into quarantine/ (tools/rework.py takes modules out for a while and
brings them back at the same path). Each node of the new tree that still has such a path as `lean.file` is printed
as a warning and appended to local/node-refs-pending.tsv (time, commit, node, path), where the fixing agent
(~/cc1/node-refs-fix.sh) picks it up: repoint the node's `lean` to the declaration's new home (e.g. the upstream
declaration a deleted twin copied) or record the removal in the node.

    python3 tools/node_refs_check.py            the commit just made (HEAD); exit 0 always
    python3 tools/node_refs_check.py --tree     list every node of the working tree whose lean.file is missing
"""
import json, pathlib, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent


def git(*a):
    return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True).stdout


def lean_files(node):
    rec = node.get("lean")
    return [r.get("file") for r in (rec if isinstance(rec, list) else [rec]) if isinstance(r, dict) and r.get("file")]


# commits that take landed work out again: the work goes back to its worker, who delivers the same file again, so the
# node's record stays right (a replay of 10-19..10-24: most removals were these)
RETURNS = ("Drop ", "Take out batch deliveries")


def committed() -> int:
    if git("log", "-1", "--format=%s", "HEAD").startswith(RETURNS):
        return 0
    gone = []
    for line in git("show", "-M", "--name-status", "--format=", "HEAD", "--", "lean/").splitlines():
        f = line.split("\t")
        if f[0].startswith("D") and f[1].endswith(".lean"):
            gone.append(f[1])
        elif f[0].startswith("R") and f[1].endswith(".lean") and not f[2].startswith("quarantine/"):
            gone.append(f[1])
    if not gone:
        return 0
    hits = []
    pats = sum((["-e", f'"{p}"'] for p in gone), [])
    for path in git("grep", "-l", "-F", *pats, "HEAD", "--", "dag/nodes").splitlines():
        path = path.split(":", 1)[-1]
        try:
            node = json.loads(git("show", f"HEAD:{path}"))
        except ValueError:
            continue
        hits += [(node.get("id", path), lf) for lf in lean_files(node) if lf in gone]
    if not hits:
        return 0
    head = git("rev-parse", "--short=11", "HEAD").strip()
    now = git("log", "-1", "--format=%cI", "HEAD").strip()
    try:
        with open(ROOT / "local" / "node-refs-pending.tsv", "a") as fh:
            for nid, lf in hits:
                fh.write(f"{now}\t{head}\t{nid}\t{lf}\n")
    except OSError:
        pass
    print(f"note: commit {head} removed Lean files that {len(hits)} DAG node(s) still record as lean.file "
          "(listed in local/node-refs-pending.tsv for the fixing agent):", file=sys.stderr)
    for nid, lf in hits[:10]:
        print(f"  {nid}: {lf}", file=sys.stderr)
    return 0


def tree() -> int:
    n = 0
    for f in sorted((ROOT / "dag" / "nodes").glob("*/*.json")):
        try:
            node = json.loads(f.read_text())
        except ValueError:
            continue
        for lf in lean_files(node):
            if not (ROOT / lf).exists() and not (ROOT / "quarantine" / lf.removeprefix("lean/")).exists():
                print(f"{node.get('id', f.stem)}\t{node.get('status')}\t{lf}"); n += 1
    print(f"{n} lean record(s) with a missing file", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(tree() if "--tree" in sys.argv else committed())
