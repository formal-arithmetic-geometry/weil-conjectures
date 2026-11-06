#!/usr/bin/env python3
"""Bulk-restore a freshly fetched Lake artifact cache in CI.

Adapted from TauCeti's `scripts/bulk-unpack-cache.py`
(https://github.com/TauCetiProject/TauCeti, Apache-2.0).

Why: after `lake cache get`, every module of the project is a `.ltar` archive in the
private cache, and stock Lake unpacks them one at a time as the build reaches each module,
on the build's job pool (`LEAN_NUM_THREADS`, 2 on GitHub's hosted runners). That made a
build that compiles nothing take most of an hour. This script extracts all archives with
a single `leantar -x -j -` call instead, installs the outputs into `.lake/build`, and
removes the corresponding output records so that Lake checks the restored outputs through
its normal local-build path (trace hashes) rather than unpacking them again. On TauCeti's
17.6k modules that was 38 s against 88 s.

Temporary: remove when the toolchain has `lake cache get --unpack`
(https://github.com/leanprover/lean4/pull/15868).

Scope: only CI's fresh, private cache (LAKE_CACHE_DIR == <project>/.lake/cache, with
LAKE_ARTIFACT_CACHE and LAKE_RESTORE_ARTIFACTS on) and a project with no `.lake/build`
yet. Anything unexpected falls back to stock Lake restoration, which is always correct:
nothing is deleted until every output is installed.
"""

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import tomllib

HASH = re.compile(r"[0-9a-f]{16}")
ARCHIVE = re.compile(r"[0-9a-f]{16}\.ltar")
SCHEMA = "2026-02-25"
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def fallback(reason: str) -> int:
    print(f"::warning::bulk-unpack-cache: {reason}; using stock Lake restoration", flush=True)
    return 0


def source_dirs(project: Path, config: dict) -> list[Path]:
    """The source directories of the root package's libraries, or raise if the layout is not
    the default one this script knows how to install into."""
    if config.get("name") is None or (project / "lakefile.lean").exists():
        raise ValueError("unsupported Lake configuration")
    for key, default in (("buildDir", ".lake/build"), ("leanLibDir", "lib/lean"),
                         ("irDir", "ir"), ("srcDir", ".")):
        if config.get(key, default) != default:
            raise ValueError(f"non-default {key}")
    libs = config.get("lean_lib", [])
    if not isinstance(libs, list) or not libs:
        raise ValueError("no lean_lib")
    dirs = []
    for lib in libs:
        if not isinstance(lib, dict):
            raise ValueError("malformed lean_lib")
        d = (project / lib.get("srcDir", ".")).resolve()
        if project not in (d, *d.parents):
            raise ValueError("srcDir outside the project")
        if d not in dirs:
            dirs.append(d)
    return dirs


def unpack(project: Path) -> int:
    started = time.monotonic()
    project = project.resolve()
    build = project / ".lake/build"
    cache = project / ".lake/cache"
    try:
        config = tomllib.loads((project / "lakefile.toml").read_text())
        dirs = source_dirs(project, config)
    except (OSError, ValueError, TypeError, tomllib.TOMLDecodeError) as error:
        return fallback(str(error))
    outputs = cache / "outputs" / config["name"]
    if build.exists() or build.is_symlink() or not outputs.is_dir():
        print("bulk-unpack-cache: no fresh cache; using stock Lake restoration", flush=True)
        return 0

    records, record_paths, archives = [], [], set()
    try:
        for path in sorted(outputs.glob("*.json")):
            if not HASH.fullmatch(path.stem) or path.is_symlink() or not path.is_file():
                raise ValueError("unexpected cache record")
            record = json.loads(path.read_text())
            if not isinstance(record, dict) or record.get("schemaVersion") != SCHEMA:
                raise ValueError("unknown cache schema")
            archive = record.get("data")
            if not isinstance(archive, str) or not ARCHIVE.fullmatch(archive):
                raise ValueError("cache is not an archive-only revision")
            if archive in archives:
                raise ValueError("overlapping cache entries")
            archives.add(archive)
            artifact = cache / "artifacts" / archive
            if artifact.is_symlink() or not artifact.is_file():
                raise ValueError(f"missing archive {archive}")
            records.append({"file": str(artifact), "hash": path.stem})
            record_paths.append(path)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        return fallback(str(error))
    if not records:
        return 0

    with tempfile.TemporaryDirectory(prefix="bulk-unpack-", dir=project / ".lake") as tmp:
        staging = Path(tmp)
        # Archives store basenames, not module paths: extract each into its own base and read
        # the module's full name from its .ilean before installing.
        for record in records:
            base = staging / record["hash"]
            record["base"] = [str(base / "lib"), str(base / "ir")]
        sysroot = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        leantar = Path(sysroot) / "bin/leantar"
        print(f"bulk-unpack-cache: extracting {len(records)} archives in one leantar call",
              flush=True)
        try:
            subprocess.run([str(leantar), "-x", "-j", "-"], input=json.dumps(records),
                           text=True, check=True)
        except (OSError, subprocess.CalledProcessError) as error:
            return fallback(str(error))
        moves, modules = [], set()
        try:
            for record in records:
                base = staging / record["hash"]
                (ilean,) = (base / "lib").glob("*.ilean")
                info = json.loads(ilean.read_text())
                module = info.get("module")
                if (info.get("version") != 5 or not isinstance(module, str)
                        or not MODULE.fullmatch(module) or module in modules):
                    raise ValueError("unknown or overlapping module identity")
                modules.add(module)
                parts = module.split(".")
                if ilean.name != parts[-1] + ".ilean":
                    raise ValueError("archive basename disagrees with module identity")
                # A module whose source is gone must not become importable from an old archive.
                if not any(d.joinpath(*parts).with_suffix(".lean").is_file() for d in dirs):
                    continue
                for directory, destination, extensions in (
                        ("lib", "lib/lean", ("trace", "olean", "olean.server", "olean.private",
                                             "ilean", "ir", "ir.sig")),
                        ("ir", "ir", ("c", "bc"))):
                    if not (base / directory).is_dir():
                        continue
                    for source in (base / directory).iterdir():
                        if (source.is_symlink() or not source.is_file()
                                or source.name not in {parts[-1] + "." + e for e in extensions}):
                            raise ValueError("unexpected archive output")
                        moves.append((source, build.joinpath(destination, *parts[:-1],
                                                             source.name)))
        except (OSError, ValueError, TypeError, AttributeError, json.JSONDecodeError) as error:
            return fallback(str(error))
        for source, target in moves:
            target.parent.mkdir(parents=True, exist_ok=True)
            source.replace(target)
    # Lake prefers archive mappings even when matching outputs exist: drop exactly these
    # records so it validates the restored traces and outputs through its local-build path.
    # The archives themselves stay in the cache.
    for path in record_paths:
        path.unlink()
    print(f"bulk-unpack-cache: restored {len(records)} modules in "
          f"{time.monotonic() - started:.1f}s", flush=True)
    return len(records)


def main(project: Path) -> None:
    try:
        expected = project.resolve() / ".lake/cache"
        configured = os.environ.get("LAKE_CACHE_DIR", "")
        if (not configured or Path(configured).resolve() != expected
                or os.environ.get("LAKE_ARTIFACT_CACHE") != "true"
                or os.environ.get("LAKE_RESTORE_ARTIFACTS") != "true"):
            print("bulk-unpack-cache: private CI cache not enabled; using stock Lake restoration")
        else:
            unpack(project)
    except Exception as error:  # never fail the build: stock Lake restoration is correct
        fallback(repr(error))


if __name__ == "__main__":
    main(Path(sys.argv[1]) if len(sys.argv) > 1 else Path.cwd())
