#!/usr/bin/env python3
"""Merge the delivery of a group on another machine (roles/maintainer.md §7, roles/remote-lead.md).

Usage (from the project root, by the maintainer only):
  tools/merge_delivery.py list                                  the delivery branches refs/heads/deliver/<group>/<item>
  tools/merge_delivery.py show <group> <item>                   print the delivery for reading (spot check), merge nothing
  tools/merge_delivery.py <group> <item> [--spot-checked NOTE]  check, cherry-pick, verify, mark reviewed, close the claim,
                                                                delete the branch, write the ledger line, commit
  tools/merge_delivery.py return <group> <item> REASONS         write the reasons into coord/returns/<group>.md and commit;
                                                                the claim and the branch stay with the group

The merge stops at the first failing step and leaves the working tree as it was. Steps: (1) the branch is based on
sheaf-dag and its base is at most SHEAF_DELIVERY_MAX_AGE_HOURS old (default 48); (2) it changes only the item's node,
new node files created by the item, the realized fields of the item's unit record, and coord/reports/<group>/<item>.md,
which must carry "## Review by <group>"; (3) the commits are cherry-picked without committing, so that
tools/review_split.py compares the delivery with the version committed here; (4) review_split.py and check_dag.py pass;
(5) `reviewed` is written with the group, the claim is closed, the branch deleted, the ledger line appended, and one
commit made with the delivery's author.
"""
import os as _os, sys as _sys
if _os.environ.get("SHEAF_LEAD") != "L-only":
    _sys.stderr.write("merge_delivery.py: refused. This tool is run only by the lead L in the lead's shell (deliveries are merged after review). Remote groups: push deliver/<group>/<item> and wait; any merge not made by L is reverted. Reported to the human in coord/HUMAN.md.\n")
    _sys.exit(2)

import datetime
import json
import pathlib
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

ROOT = li.ROOT
MAIN = "sheaf-dag"
MAX_AGE = float(li.config().get("SHEAF_DELIVERY_MAX_AGE_HOURS", "48")) * 3600


def git(*a, check=True, capture=True):
    r = subprocess.run(["git", *a], cwd=ROOT, text=True, capture_output=capture)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(a)} failed: {(r.stderr or r.stdout).strip()}")
    return (r.stdout or "").strip()


def branch_of(group, item):
    return f"deliver/{group}/{item}"


def node_path(item):
    hits = list((ROOT / "dag" / "nodes").glob(f"*/{item}.json"))
    return hits[0].relative_to(ROOT).as_posix() if hits else None


def load_json_at(ref, path):
    return json.loads(git("show", f"{ref}:{path}"))


def exists_at(ref, path):
    return subprocess.run(["git", "cat-file", "-e", f"{ref}:{path}"], cwd=ROOT, capture_output=True).returncode == 0


def ledger(line):
    with open(ROOT / "coord" / "ledger.md", "a") as f:
        f.write(f"- {datetime.date.today().isoformat()}, {line}\n")


def cmd_list():
    out = git("for-each-ref", "--format=%(refname:short)\t%(committerdate:iso-strict)\t%(objectname:short)", "refs/heads/deliver/")
    if not out:
        print("no deliveries"); return 0
    for l in out.splitlines():
        ref, date, sha = l.split("\t")
        parts = ref.split("/")
        group, item = parts[1], "/".join(parts[2:])
        lock = ROOT / "coord" / "claims" / f"{item}.lock"
        who = json.loads(lock.read_text()).get("who") if lock.exists() else "no claim"
        print(f"{ref}\t{date}\t{sha}\tclaim: {who}")
    return 0


def inspect(group, item):
    """Steps 1 and 2: returns (base, commits, files dict) or raises with the reason."""
    br = branch_of(group, item)
    if subprocess.run(["git", "rev-parse", "--verify", "-q", f"refs/heads/{br}"], cwd=ROOT, capture_output=True).returncode != 0:
        raise RuntimeError(f"no branch {br}")
    base = git("merge-base", MAIN, br)
    age = time.time() - int(git("show", "-s", "--format=%ct", base))
    if age > MAX_AGE:
        raise RuntimeError(f"base {base[:7]} is {age/3600:.0f} h behind {MAIN}: pull {MAIN}, rebase, push again")
    commits = git("rev-list", "--reverse", f"{base}..{br}").split()
    if not commits:
        raise RuntimeError("the branch has no commit beyond its base")
    if len(commits) > 3:
        raise RuntimeError(f"{len(commits)} commits: deliver one item as one commit (squash)")
    files = git("diff", "--name-only", base, br).splitlines()
    item_path = node_path(item)
    if item_path is None or not exists_at(base, item_path):
        raise RuntimeError(f"the item {item} has no node file at the base")
    unit = load_json_at(base, item_path).get("unit")
    report = f"coord/reports/{group}/{item}.md"
    kinds = {}
    for f in files:
        if f == item_path:
            kinds[f] = "item"
        elif f == report:
            kinds[f] = "report"
        elif f.startswith("dag/nodes/") and f.endswith(".json") and not exists_at(base, f):
            d = load_json_at(br, f)
            if (d.get("created") or {}).get("item") != item:
                raise RuntimeError(f"new node {f} has created.item != {item}")
            kinds[f] = "new"
        elif unit and f == f"dag/units/{unit}.json":
            a, b = load_json_at(base, f), load_json_at(br, f)
            for k in ("realized", "realized_by"):
                a.pop(k, None); b.pop(k, None)
            if a != b:
                raise RuntimeError(f"{f}: only the realized fields may change")
            kinds[f] = "unit"
        else:
            raise RuntimeError(f"file outside the item's files: {f}")
    if "item" not in kinds.values():
        raise RuntimeError("the item's node file is unchanged")
    if "report" not in kinds.values():
        raise RuntimeError(f"no report file {report}")
    if f"## Review by {group}" not in git("show", f"{br}:{report}"):
        raise RuntimeError(f"the report lacks the heading '## Review by {group}' (the group's own review)")
    dirty = git("status", "--porcelain", "--", *files)
    if dirty:
        raise RuntimeError(f"local changes on the delivery's files, resolve first:\n{dirty}")
    return base, commits, kinds


def cmd_show(group, item):
    base, commits, kinds = inspect(group, item)
    br = branch_of(group, item)
    print(f"branch {br}: {len(commits)} commit(s) on base {base[:7]}; files: {kinds}")
    print(git("show", "--stat", "--format=%an <%ae> %ci%n%s%n%b", *commits))
    print("\n===== report =====")
    print(git("show", f"{br}:coord/reports/{group}/{item}.md"))
    for f, k in kinds.items():
        if k in ("item", "new"):
            d = load_json_at(br, f)
            print(f"\n===== {k}: {f} =====\nstatus {d.get('status')}; unit {d.get('unit')}\n{d.get('statement')}")
            for i, s in enumerate(d.get("proof") or []):
                print(f"-- step {i+1} uses={s.get('uses')} elementary={s.get('elementary')}\n{s.get('text')}")
            if d.get("mathlib_match"):
                print("mathlib_match:", d["mathlib_match"])
    return 0


def undo(kinds):
    """Put the working tree back after a cherry-pick --no-commit."""
    subprocess.run(["git", "cherry-pick", "--quit"], cwd=ROOT, capture_output=True)
    for f, k in kinds.items():
        if k == "new":
            subprocess.run(["git", "rm", "-q", "--cached", "--", f], cwd=ROOT, capture_output=True)
            (ROOT / f).unlink(missing_ok=True)
        else:
            git("restore", "--staged", "--worktree", "--", f)


def cmd_merge(group, item, spot_note=None):
    base, commits, kinds = inspect(group, item)
    br = branch_of(group, item)
    r = subprocess.run(["git", "cherry-pick", "--no-commit", *commits], cwd=ROOT, text=True, capture_output=True)
    if r.returncode != 0:
        subprocess.run(["git", "cherry-pick", "--abort"], cwd=ROOT, capture_output=True)
        undo(kinds)
        raise RuntimeError(f"cherry-pick conflict on {MAIN} {git('rev-parse', '--short', MAIN)}: the group pulls, rebases and pushes again\n{r.stderr.strip()}")
    try:
        rs = subprocess.run([sys.executable, "tools/review_split.py", item], cwd=ROOT, text=True, capture_output=True)
        if rs.returncode != 0 or "FAIL" in rs.stdout:
            raise RuntimeError("review_split.py:\n" + rs.stdout + rs.stderr)
        cd = subprocess.run([sys.executable, "tools/check_dag.py"], cwd=ROOT, text=True, capture_output=True)
        # "reach:" warnings are not errors of the delivery (new nodes of other workers in progress are unreached until
        # their item is written); check_dag.py exits 1 on them, so only the listed kinds fail the merge
        bad = [l for l in (cd.stdout + cd.stderr).splitlines() if l.startswith(("error", "unit", "route", "cycle", "deps")) or "ERROR" in l]
        if bad:
            raise RuntimeError("check_dag.py:\n" + "\n".join(bad) + "\n" + (cd.stdout + cd.stderr)[-2000:])
    except Exception:
        undo(kinds)
        raise
    item_path = next(f for f, k in kinds.items() if k == "item")
    p = ROOT / item_path
    d = json.loads(p.read_text())
    d["reviewed"] = {"date": datetime.date.today().isoformat(), "by": "L", "group": group, "result": "pass",
                     "note": ("mechanical checks by tools/merge_delivery.py; mathematics reviewed by the lead of " + group)
                             + (f"; spot-checked by L: {spot_note}" if spot_note else "")}
    p.write_text(json.dumps(d, indent=1, ensure_ascii=False) + "\n")
    author = git("show", "-s", "--format=%an <%ae>", commits[-1])
    subject = git("show", "-s", "--format=%s", commits[-1])
    new = [f for f, k in kinds.items() if k == "new"]
    done = subprocess.run([sys.executable, "tools/claim.py", "done", group, item, f"delivered by {group} on {br}, merged by L"],
                          cwd=ROOT, text=True, capture_output=True)
    ledger(f"delivery of {group}: {item} merged from {br} ({len(commits)} commit(s), {len(new)} new node(s)"
           f"{', spot-checked by L: ' + spot_note if spot_note else ''}); claim {'closed' if 'done' in done.stdout else 'not held by ' + group + ' (' + done.stdout.strip() + ')'}")
    rp = ROOT / "coord" / "returns" / f"{group}.md"
    if rp.exists():
        import re as _re
        parts = _re.split(r"(?m)^(?=## )", rp.read_text())
        keep = [x for x in parts if not x.startswith(f"## {item} (")]
        if len(keep) != len(parts):
            rp.write_text("".join(keep)); git("add", "--", rp.relative_to(ROOT).as_posix())
    git("add", "--", *kinds.keys(), "coord/ledger.md")
    git("commit", "-q", f"--author={author}", "-m", f"{subject}\n\nDelivered by group {group} ({br}); merged and marked reviewed by L.")
    git("branch", "-D", br)
    print(f"merged {item} from {br}: {git('rev-parse', '--short', 'HEAD')}; new nodes: {new}")
    return 0


def cmd_return(group, item, reasons):
    br = branch_of(group, item)
    head = git("rev-parse", "--short", f"refs/heads/{br}") if subprocess.run(["git", "rev-parse", "-q", "--verify", f"refs/heads/{br}"], cwd=ROOT, capture_output=True).returncode == 0 else "no branch"
    p = ROOT / "coord" / "returns" / f"{group}.md"
    p.parent.mkdir(exist_ok=True)
    # keep the returns file exact: one entry per item, the latest
    if p.exists():
        import re as _re
        parts = _re.split(r"(?m)^(?=## )", p.read_text())
        kept = [x for x in parts if not x.startswith(f"## {item} (")]
        if len(kept) != len(parts):
            p.write_text("".join(kept).rstrip("\n") + "\n")
    with open(p, "a") as f:
        f.write(f"\n## {item} ({datetime.datetime.now(datetime.UTC).strftime('%Y-%m-%d %H:%M')} UTC, branch head {head})\n\n{reasons}\n")
    ledger(f"delivery of {group}: {item} returned ({head}): {reasons.splitlines()[0][:160]}")
    git("add", "--", p.relative_to(ROOT).as_posix(), "coord/ledger.md")
    git("commit", "-q", "-m", f"return to {group}: {item}")
    print(f"returned {item} to {group}; reasons in {p.relative_to(ROOT)}")
    return 0


def main():
    a = sys.argv[1:]
    if not a or a[0] in ("-h", "--help"):
        print(__doc__); return 0
    try:
        if a[0] == "list":
            return cmd_list()
        if a[0] == "show":
            return cmd_show(a[1], a[2])
        if a[0] == "return":
            return cmd_return(a[1], a[2], " ".join(a[3:]))
        group, item = a[0], a[1]
        note = a[a.index("--spot-checked") + 1] if "--spot-checked" in a else None
        return cmd_merge(group, item, note)
    except RuntimeError as e:
        print(f"NOT MERGED: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
