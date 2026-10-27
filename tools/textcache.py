"""The text cache of tools/leanindex.py at a shared path (2026-10-24, cpu).

The server preflight (~/weil-preflight/run.py) runs in slots whose local/ is wiped before every run; it sets
SHEAF_LEANINDEX_CACHE to a shared path so the slots do not lex the whole library again. Since 2026-10-27 leanindex
reads that variable itself (a keyed SQLite store next to the named path, see leanindex._tc_path), so use_shared() has
nothing left to do; it stays for its callers."""
from __future__ import annotations


def use_shared() -> None:
    return None
