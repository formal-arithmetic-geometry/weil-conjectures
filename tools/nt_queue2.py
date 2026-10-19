#!/usr/bin/env python3
"""Refresh the isolated stage-2 queue in a low-priority, separately locked pass."""
import os

os.environ["SHEAF_LEAD"] = "L-only"
os.environ["SHEAF_LOCK_TIMEOUT"] = "600"

import nt_merge2  # noqa: E402
from mergelock import merge_lock  # noqa: E402


with merge_lock():
    nt_merge2.md.refresh_queue("stage 2 batch")
