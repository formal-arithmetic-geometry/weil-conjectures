#!/usr/bin/env python3
"""Retired 2026-10-19 with ~/weil-newtargets: there is one repository (this one, ~/weil-conjectures-sheaf) and its
dag/nodes is the DAG. This stub keeps the interface the stage-1/2 tools import; every operation is a no-op here:
active() is False, so their code paths commit DAG and Lean files in this repository like any other file."""
from __future__ import annotations
import pathlib

P = pathlib.Path(__file__).resolve().parent.parent
LIVE = P
NODES = "dag/nodes"
TRAILER = "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"


def active() -> bool:
    return False


def is_dag(rel) -> bool:
    return str(rel).replace("\\", "/").lstrip("./").startswith(NODES + "/") or str(rel) == NODES


def split(paths):
    return list(paths), []


def lean_to_live(paths):
    return []


def commit_live(paths, msg):
    raise RuntimeError("tools/livedag.py: retired (one repository); commit in this repository")


def graft():
    return None


if __name__ == "__main__":
    print("livedag: retired 2026-10-19 (one repository: this one)")
