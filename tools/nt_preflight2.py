#!/usr/bin/env python3
"""Check a dry-run delivery bundle against server sources without publishing a ref.

The caller has already compiled every module and existing-declaration probe with
nt_compile. This runs the same a-e checks as preflight_delivery --stage 2, using
the current server tools and published sources, in a disposable Git object store.
"""
import copy
import pathlib
import subprocess
import sys
import tempfile

import nt_incremental2
import stage2_delivery as s2


def graph_findings(delivery, before=None):
    """Check the effective landing delta against the current server DAG.

    A delivery reader checks ownership against the branch's merge base. Landing
    preserves current metadata and only applies the owned fields, so reproduce
    those writes here rather than replacing current nodes with stale copies.
    Landing still rechecks the graph when it commits concurrent deliveries.
    """
    if delivery["node"] is None:
        return []  # The delivery reader already reports the malformed item.
    if before is None:
        # Stage-2 preflight validates the newtargets branch, whose DAG is the
        # authoritative input for this delivery.  Do not use dag_queue.load()
        # here: coord/sheaf.env intentionally points that helper at the live
        # stage-3 DAG, where published newtargets-only nodes are absent.
        before = s2.nodes_at(s2.Git(s2.ROOT), "sheaf-dag")
    item = delivery["node"]["id"]
    if item not in before:
        return [f"deps: {item}: no node on the current server DAG; rebase the delivery"]
    after = dict(before)
    node = copy.deepcopy(before[item])
    node["lean"] = delivery["rec"]
    if delivery["corrected"]:
        for key in s2.STAGE2_ITEM_CORRECTION:
            if key in delivery["node"]:
                node[key] = copy.deepcopy(delivery["node"][key])
            else:
                node.pop(key, None)
    else:
        deps = list(node.get("stmt_deps") or [])
        node["stmt_deps"] = deps + [d for d in delivery.get("added_deps", []) if d not in deps]
    after[item] = node
    changed = {item}
    for nid, extra in delivery["new"].items():
        after[nid] = copy.deepcopy(extra["node"])
        changed.add(nid)
    for nid, extra in delivery["deps"].items():
        if nid not in before:
            return [f"deps: {nid}: dependency node disappeared; rebase the delivery"]
        after[nid] = dict(before[nid], lean=extra["node"]["lean"])
        changed.add(nid)
    return nt_incremental2.local_findings(after, changed)


def main():
    group, item = sys.argv[1:]
    with tempfile.TemporaryDirectory(prefix="nt-preflight2-", dir="/dev/shm/nt-tmp") as td:
        root = pathlib.Path(td)
        bundle = root / "delivery.bundle"
        bundle.write_bytes(sys.stdin.buffer.read())
        repo = root / "repo"
        subprocess.run(["git", "init", "-q", "--bare", str(repo)], check=True)
        objects = subprocess.check_output(
            ["git", "rev-parse", "--git-path", "objects"], cwd=s2.ROOT, text=True).strip()
        (repo / "objects/info/alternates").write_text(str((s2.ROOT / objects).resolve()) + "\n")
        g = s2.Git(repo)
        tip = s2.Git(s2.ROOT).run("rev-parse", "sheaf-dag")
        g.run("update-ref", "refs/heads/sheaf-dag", tip)
        g.run("fetch", "-q", str(bundle), "HEAD:refs/heads/delivery")
        delivery = s2.read_delivery(g, "delivery", "sheaf-dag", group, item)
        for role in delivery["roles"]:
            print("  " + role)
        if delivery["corrected"]:
            bad = sum(c.get("holds") is False for c in delivery["citer_marks"])
            print(f"item corrected: {len(delivery['citers'])} citers, {bad} marked holds:false")
        for note in delivery["notes"]:
            print(" ! " + note)
        # Read the baseline from the immutable branch tree, rather than the
        # working checkout or the live DAG selected by coord/sheaf.env.
        before = s2.nodes_at(g, "sheaf-dag")
        fails = list(delivery["fails"])
        fails.extend(("b", "incremental DAG validation: " + finding)
                     for finding in graph_findings(delivery, before))
        if fails:
            print(f"preflight FAILED (stage 2), {len(fails)} reason(s); do not push:")
            for letter, finding in sorted(fails):
                print(f" ({letter}) {finding}")
            return 1
        print("preflight OK (stage 2); per-file server compile checked by caller")
        return 0


if __name__ == "__main__":
    sys.exit(main())
