"""Supply committed imports absent from the last green build in a private request tree."""
from pathlib import PurePosixPath
import subprocess


class DependencySourceError(RuntimeError):
    pass


def missing_dependencies(jobs, root, lb, published, lean, repo, header_imports):
    """Return missing repository modules in import order, without publishing anything.

    Requested modules and caller artifacts take precedence. All other sources come
    from one committed snapshot, and must still match the live source tree. This
    lets workers use a newly landed statement while its global build is pending.
    """
    planned = {str(PurePosixPath(j["rel"]).with_suffix("")).replace("/", ".")
               for j in jobs}
    visiting, done, dependencies = set(), set(), []
    snapshot = None

    def visit(mod):
        nonlocal snapshot
        if mod in planned or mod in done:
            return
        # These are repository roots, not arbitrary package or filesystem paths.
        parts = mod.split(".")
        if parts[0] not in ("Sheaf", "WeilConjectures", "Comparator") or not all(
                part and part not in (".", "..") and "/" not in part and "\\" not in part
                for part in parts):
            return
        rel = PurePosixPath(*parts).with_suffix(".lean")
        if (lb / rel.with_suffix(".olean")).is_file() or (
                published / rel.with_suffix(".olean")).is_file():
            done.add(mod)
            return
        source = lean / rel
        if not source.is_file():
            return  # Lean supplies the ordinary missing-module diagnostic.
        if mod in visiting:
            raise DependencySourceError(f"unpublished dependency import cycle at {mod}")
        if snapshot is None:
            snapshot = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
        committed = subprocess.run(
            ["git", "show", f"{snapshot}:lean/{rel}"], cwd=repo,
            capture_output=True)
        if committed.returncode:
            raise DependencySourceError(
                f"unpublished dependency {mod} has no source committed at {snapshot}")
        if source.read_bytes() != committed.stdout:
            raise DependencySourceError(
                f"unpublished dependency {mod} differs from committed source at {snapshot}; "
                "commit or finish the source change before compiling its dependents")
        destination = root / rel
        if destination.exists():
            raise DependencySourceError(
                f"unpublished dependency {mod} has an unscheduled caller source; "
                "include it in the compile jobs")
        visiting.add(mod)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(committed.stdout)
        for dep in header_imports(destination):
            visit(dep)
        visiting.remove(mod)
        done.add(mod)
        dependencies.append({"rel": str(rel), "out": True, "probe": "",
                             "upstream": parts[0] != "Sheaf", "dependency": mod,
                             "source_commit": snapshot})

    for job in jobs:
        for mod in header_imports(root / job["rel"]):
            visit(mod)
    return dependencies
