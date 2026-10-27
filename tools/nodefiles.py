"""One parse of each node file per process (2026-10-24, cpu).

The stage-1 preflight read all ~30k node files (~0.5 GB of JSON) three times: tools/dag_inc.py, tools/blueprint_refs.py
load() and tools/review_split.py. read(p) is json.loads(p.read_text()); after enable() it returns the object parsed
before for a file whose inode, size, mtime and ctime are unchanged (a changed file is read again; a failure is raised
again as it was raised). The callers only read the parsed nodes. Off by default: a long-running process that never calls
enable() keeps no copy."""
from __future__ import annotations
import json, os

_MEMO: dict | None = None


def enable() -> None:
    global _MEMO
    if _MEMO is None:
        _MEMO = {}


def read(p):
    if _MEMO is None:
        return json.loads(p.read_text())
    try:
        st = os.stat(p)
    except OSError:
        return json.loads(p.read_text())
    key = (st.st_dev, st.st_ino)
    sig = (st.st_size, st.st_mtime_ns, st.st_ctime_ns)
    hit = _MEMO.get(key)
    if hit is not None and hit[0] == sig:
        if hit[2] is not None:
            raise hit[2]
        return hit[1]
    try:
        d = json.loads(p.read_text())
    except Exception as e:  # noqa: BLE001
        _MEMO[key] = (sig, None, e)
        raise
    _MEMO[key] = (sig, d, None)
    return d


_DAG: list = []


def dag(nodes: dict):
    """dag_queue.Dag(nodes). After enable(), the Dag built before is returned again for a dict holding the same node
    objects under the same ids in the same order (tools/dag_inc.py and tools/review_split.py, run in one preflight process,
    each built it from the same parsed files), and dag_queue's module state is set as the constructor sets it."""
    import dag_queue as dq
    if _MEMO is None:
        return dq.Dag(nodes)
    key = tuple((k, id(v)) for k, v in nodes.items())
    if _DAG and _DAG[0][0] == key:
        g = _DAG[0][1]
        dq._ASSUMED["done"] = g.assumed
        return g
    g = dq.Dag(nodes)
    _DAG[:] = [(key, g, nodes)]   # nodes kept alive: the ids in the key stay theirs
    return g
