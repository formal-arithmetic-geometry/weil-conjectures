#!/usr/bin/env python3
"""Exercise request admission without starting Lean or using the live build."""
import argparse
import errno
import fcntl
import io
import json
from pathlib import Path
import runpy
import tarfile
import tempfile
from unittest.mock import patch


def check(implementation):
    request = io.BytesIO()
    with tarfile.open(fileobj=request, mode="w:gz") as archive:
        data = json.dumps({"timeout": 60, "jobs": []}).encode()
        member = tarfile.TarInfo("manifest.json")
        member.size = len(data)
        archive.addfile(member, io.BytesIO(data))

    # Reproduce the old refusal deterministically: every legacy admission lock
    # is busy. No real locks or compiler processes are involved.
    attempts = []

    def busy_legacy_slot(file, operation):
        attempts.append(operation)
        assert operation & fcntl.LOCK_NB
        raise BlockingIOError(errno.EWOULDBLOCK, "legacy slot occupied")

    with tempfile.TemporaryDirectory(prefix="rset-admission-test-") as directory:
        task_home = Path(directory)
        lean = task_home / "weil-conjectures-sheaf/lean"
        lean.mkdir(parents=True)
        (lean / "lakefile.toml").write_text("[leanOptions]\n")
        (task_home / "cc1").mkdir()
        incoming = io.TextIOWrapper(io.BytesIO(request.getvalue()))
        outgoing = io.TextIOWrapper(io.BytesIO())
        with patch("pathlib.Path.home", return_value=task_home), \
             patch("fcntl.flock", side_effect=busy_legacy_slot), \
             patch("sys.stdin", incoming), patch("sys.stdout", outgoing):
            runpy.run_path(str(implementation), run_name="__main__")
        assert not attempts, "compile requests must not acquire admission slots"
        with tarfile.open(fileobj=io.BytesIO(outgoing.buffer.getvalue()), mode="r:gz") as archive:
            result = json.load(archive.extractfile("result.json"))
        assert result["results"] == [], result
        assert not list((task_home / "cc1/rset-tmp").iterdir()), "scratch directory leaked"
    print("PASS: valid reply with all legacy slots unavailable; no Lean started")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("implementation", nargs="?", type=Path,
                        default=Path(__file__).resolve().parents[1] / "remote_compile_set.py")
    check(parser.parse_args().implementation.resolve())
