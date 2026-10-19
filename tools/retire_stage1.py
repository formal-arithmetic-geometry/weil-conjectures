"""Retire a superseded stage-1 delivery without returning completed work.

Only the isolated project is written. The delivery remains reachable at
refs/superseded/<group>/<item>/<head>; the current DAG is never changed.
"""
from __future__ import annotations

import datetime
import json
import os
import pathlib
import re
import shutil
import subprocess
import time

import dag_queue
from mergelock import merge_lock

ROOT = pathlib.Path(__file__).resolve().parent.parent


class RetirementError(RuntimeError):
    pass


def git(*args, check=True):
    result = subprocess.run(
        ["git", "-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", *args],
        cwd=ROOT, capture_output=True, text=True,
        env=dict(os.environ, SHEAF_LEAD="L-only"),
    )
    if check and result.returncode:
        raise RetirementError((result.stderr or result.stdout).strip())
    return result


def retire_completed(group, item, expected_head):
    """Return True only for a completed stage-1 packet at the reviewed head.

    Unsplit nodes, Lean deliveries, replacement heads and stage-2 claims must
    survive. The merge lock covers eligibility, records and the commit; the
    final ref transaction also compares the branch head against concurrent pushes.
    """
    with merge_lock(ROOT / "coord/.merge.lock"):
        if git("branch", "--show-current").stdout.strip() != "sheaf-dag":
            raise RetirementError("retirement requires sheaf-dag")
        ref = f"refs/heads/deliver/{group}/{item}"
        archive = f"refs/superseded/{group}/{item}/{expected_head}"
        current = git("rev-parse", "--verify", "-q", ref, check=False)
        branch_exists = current.returncode == 0
        if current.returncode:
            # Sync may have archived the branch and claim but left its return.
            # Continue through record cleanup using that exact archived packet.
            saved = git("rev-parse", "--verify", "-q", archive, check=False)
            if saved.returncode or saved.stdout.strip() != expected_head:
                return False
        head = current.stdout.strip() if branch_exists else expected_head
        if head != expected_head:
            raise RetirementError(f"HEAD MOVED {item}: expected {expected_head}, found {head}")
        # This helper is a stage-1 path; never consume a stage-2 delivery.
        if git("diff", "--name-only", f"HEAD...{head}", "--", "lean").stdout.strip():
            return False
        paths = list((ROOT / "dag/nodes").glob(f"*/{item}.json"))
        if len(paths) != 1:
            return False
        rel = paths[0].relative_to(ROOT).as_posix()
        node = json.loads(git("show", "HEAD:" + rel).stdout)
        # 2026-10-18 (s1loop): completed by THE stage-1 predicate (dag_queue.stage1_completed) both on this project's copy
        # and on the node the queue reads (the live DAG, coord/sheaf.env SHEAF_DAG). Before, only this copy was asked
        # (with unfolded() alone): a re-split repaired here but never promoted to live (thm-sf-pf-proetale) and an
        # attachment live audited closed_part (lem-sfb-modobj-abelian) stayed queued while every delivery for them was
        # archived as already completed, ~60 rounds for thm-sf-pf-proetale.
        if not dag_queue.stage1_completed(node):
            return False
        queued = dag_queue.queue_node(item)
        if queued is not None and not dag_queue.stage1_completed(queued):
            return False

        returns = ROOT / "coord/returns" / f"{group}.md"
        ledger = ROOT / "coord/ledger.md"
        deliveries = ROOT / "coord/deliveries.log"
        claim = ROOT / "coord/claims" / (item.replace("/", "__") + ".lock")
        before = {p: p.read_bytes() if p.exists() else None for p in (returns, ledger, deliveries, claim)}
        records = [ledger, deliveries]
        text = (before[returns] or b"").decode()
        parts = re.split(r"(?m)^(?=## )", text)
        def matches_packet(part):
            if not part.startswith(f"## {item} ("):
                return False
            returned_head = re.search(r"branch head ([0-9a-f]{7,})", part.splitlines()[0])
            return head.startswith(returned_head.group(1)) if returned_head else branch_exists
        kept = "".join(p for p in parts if not matches_packet(p))
        if kept != text:
            records.append(returns)
        # An item can already be legitimately claimed for stage 2. Its queued
        # claim belongs to that later stage, even if an old stage-1 packet remains.
        queue = ROOT / "coord/queue.tsv"
        stages = dict(line.split("\t")[:2] for line in queue.read_text().splitlines()
                      if not line.startswith("#") and "\t" in line) if queue.exists() else {}
        remove_claim = bool(before[claim] and json.loads(before[claim]).get("who") == group
                            and stages.get(item) != "2")
        if not branch_exists and kept == text and not remove_claim:
            return True
        changed = records + ([claim] if remove_claim else [])
        for p in changed:
            rel = p.relative_to(ROOT).as_posix()
            if p == returns and git("status", "--porcelain", "--untracked-files=no", "--", rel).stdout.strip():
                # appended repair handoffs (tools/claim.py) are committed first; we hold the merge lock
                git("commit", "--only", "-m", f"Commit pending returns of {group}", "--", rel)
            if git("status", "--porcelain", "--untracked-files=no", "--", rel).stdout.strip():
                raise RetirementError(f"uncommitted bookkeeping changes: {rel}")
        stamp = str(time.time_ns())
        # 2026-10-18 (L, propagation): the copies go outside the repository (they were left under coord/, thousands of
        # untracked ledger copies in two days); ~/weil-newtargets-retire-bak/<name>.retire-stage1-<stamp>.bak
        bakdir = pathlib.Path.home() / "weil-retire-bak"; bakdir.mkdir(exist_ok=True)
        for p in changed:
            if p.exists():
                shutil.copy2(p, bakdir / (p.name + ".retire-stage1-" + stamp + ".bak"))
        # Archive before removing any records; this is also safe across a crash.
        git("update-ref", archive, head)
        now = datetime.datetime.now(datetime.timezone.utc).strftime("%FT%TZ")
        try:
            if returns in records:
                returns.write_text(kept)
            for p, line in (
                (ledger, f"- {now} L: superseded stage-1 delivery {group}/{item} at {head}; "
                 f"current completion retained; packet archived at {archive}; stale return retired.\n"),
                (deliveries, f"{now} {group} superseded {item}: stage 1 already completed; archived {head}\n"),
            ):
                with p.open("a") as stream:
                    stream.write(line)
            if remove_claim:
                claim.unlink()
            # --only excludes unrelated staged work in this shared checkout.
            rels = [p.relative_to(ROOT).as_posix() for p in records]
            if remove_claim and git("ls-files", "--", claim.relative_to(ROOT).as_posix()).stdout.strip():
                rels.append(claim.relative_to(ROOT).as_posix())
            git("commit", "--only", "-m", f"Retire superseded stage-1 delivery {item} ({group})", "--", *rels)
        except BaseException:
            for p in changed:
                if before[p] is None:
                    p.unlink(missing_ok=True)
                else:
                    p.write_bytes(before[p])
            raise
        # A push can occur without the merge lock. Archive and delete atomically
        # only if this is still the reviewed head; never delete its replacement.
        if branch_exists:
            result = subprocess.run(
                ["git", "update-ref", "--stdin"], cwd=ROOT, text=True, capture_output=True,
                input=f"start\nupdate {archive} {head}\ndelete {ref} {head}\nprepare\ncommit\n",
            )
            if result.returncode:
                raise RetirementError("HEAD MOVED during retirement: " + result.stderr.strip())
        return True
