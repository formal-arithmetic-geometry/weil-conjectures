#!/usr/bin/env python3
"""Stage a CI build for upload to the Lake cache, without holding any credential.

  stage_lake_cache.py snapshot <project> <snapshot.json>
      Right after `lake cache get` and before any project code runs: record, for every
      downloaded output record, input hash -> archive name. These are the modules whose
      outputs are already in the remote cache.

  stage_lake_cache.py stage <project> <map.jsonl> <snapshot.json> <outdir>
      After `lake build -o <map.jsonl>`: write <outdir>/map.jsonl, the upload map, and copy
      into <outdir>/artifacts/ only the archives that are not in the remote cache yet.
      An entry whose input hash was downloaded keeps the archive it was downloaded as (same
      inputs, same outputs; the bulk restore makes Lake re-describe such modules locally, and
      the remote has only the archive). Every other entry must name an archive Lake produced
      in the local cache, which is then staged.

The upload itself happens in a separate job that never runs project code (see
.github/workflows/lean_action_ci.yml): Lean executes code at elaboration time, so a key in
reach of `lake build` is a key in reach of whatever landed on master.
"""

import json
from pathlib import Path
import re
import shutil
import sys

HASH = re.compile(r"[0-9a-f]{16}")
ARCHIVE = re.compile(r"[0-9a-f]{16}\.ltar")


def package_name(project: Path) -> str:
    import tomllib
    return tomllib.loads((project / "lakefile.toml").read_text())["name"]


def snapshot(project: Path, out: Path) -> None:
    outputs = project / ".lake/cache/outputs" / package_name(project)
    snap = {}
    for path in sorted(outputs.glob("*.json")) if outputs.is_dir() else []:
        try:
            data = json.loads(path.read_text()).get("data")
        except (OSError, ValueError):
            continue
        if HASH.fullmatch(path.stem) and isinstance(data, str) and ARCHIVE.fullmatch(data):
            snap[path.stem] = data
    out.write_text(json.dumps(snap))
    print(f"stage-lake-cache: {len(snap)} downloaded module archives recorded")


def stage(project: Path, map_path: Path, snap_path: Path, outdir: Path) -> None:
    snap = json.loads(snap_path.read_text())
    lines = map_path.read_text().splitlines()
    if not lines:
        raise SystemExit("empty map")
    header, entries = lines[0], lines[1:]
    store = project / ".lake/cache/artifacts"
    (outdir / "artifacts").mkdir(parents=True, exist_ok=True)
    out_lines, staged, reused = [header], 0, 0
    for line in entries:
        if not line.strip():
            continue
        key, value = json.loads(line)
        if not isinstance(key, str) or not HASH.fullmatch(key):
            raise SystemExit(f"bad map key {key!r}")
        if key in snap:
            value = snap[key]
            reused += 1
        elif isinstance(value, str) and ARCHIVE.fullmatch(value):
            src = store / value
            if not src.is_file():
                raise SystemExit(f"archive {value} is not in the local cache")
            dst = outdir / "artifacts" / value
            if not dst.exists():
                shutil.copyfile(src, dst)
                staged += 1
        else:
            raise SystemExit(f"entry {key} is neither downloaded nor an archive: {value!r}")
        out_lines.append(json.dumps([key, value], separators=(",", ":")))
    (outdir / "map.jsonl").write_text("\n".join(out_lines) + "\n")
    print(f"stage-lake-cache: {len(out_lines) - 1} mappings, {reused} reused, "
          f"{staged} new archives staged")


if __name__ == "__main__":
    cmd, *args = sys.argv[1:]
    if cmd == "snapshot":
        snapshot(Path(args[0]).resolve(), Path(args[1]))
    elif cmd == "stage":
        stage(Path(args[0]).resolve(), Path(args[1]), Path(args[2]), Path(args[3]))
    else:
        raise SystemExit(f"unknown command {cmd}")
