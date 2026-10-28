"""Supply committed or completed landing imports in a private request tree."""
import hashlib
import json
from pathlib import PurePosixPath
import subprocess


class DependencySourceError(RuntimeError):
    pass


def _published_imports(published, rel):
    """Read the imports used by the published object, not its newer source plan."""
    try:
        trace = json.loads((published / rel.with_suffix(".trace")).read_text())
    except (OSError, ValueError):
        return []
    imports = []

    def walk(value):
        if not isinstance(value, list):
            return
        if len(value) == 2 and isinstance(value[0], str) and value[0].endswith(":importArts"):
            imports.append(value[0][:-len(":importArts")])
        else:
            for child in value:
                walk(child)

    if isinstance(trace, dict):
        walk(trace.get("inputs", []))
    return imports


def _landing_sources(repo):
    """Snapshot the latest completed request for each path in the merge candidate."""
    sources = {}
    for path in (repo / "local/builds/requests").glob("*.json"):
        try:
            record = json.loads(path.read_text())
        except (OSError, ValueError):
            continue
        if not isinstance(record, dict):
            continue
        rid = record.get("id")
        if (rid != path.stem or not record.get("landed") or
                not isinstance(record.get("seq"), int) or
                not isinstance(record.get("files"), list)):
            continue
        rank = (record["seq"], rid)
        for entry in record["files"]:
            if not isinstance(entry, dict) or not isinstance(entry.get("path"), str):
                continue
            rel = entry["path"]
            if rel not in sources or rank > sources[rel][0]:
                sources[rel] = (rank, entry)
    return sources


def _staged_source(repo, rel, live, sources):
    """Use recorded bytes only when the staged copy, digest and live source agree."""
    record = sources.get(str(rel))
    if record is None:
        return None
    (_, rid), entry = record
    if entry.get("deleted") or entry.get("sha") != hashlib.sha256(live).hexdigest():
        return None
    try:
        staged = (repo / "local/builds/staged" / rid / rel).read_bytes()
    except OSError:
        return None
    return (staged, rid) if staged == live else None


def missing_dependencies(jobs, root, lb, published, lean, repo, header_imports):
    """Return missing or invalidated modules in private compile order.

    Requested modules and caller artifacts take precedence. Other sources match
    one committed snapshot or a hash-checked, completed merge-queue landing. A
    landing is intentionally not committed until its global build succeeds. An
    arbitrary live edit is never compiled, and publication is never written.

    Published objects can predate a declaration relocation: traverse their
    current imports too, and rebuild direct importers of newly supplied modules,
    including requested modules and caller objects absent from publication.
    Otherwise an old owner and a newly split data module declare the same names.
    """
    planned = {str(PurePosixPath(j["rel"]).with_suffix("")).replace("/", ".")
               for j in jobs}
    visiting, done, dependencies = set(), set(), []
    checked_published = set()
    # A new owner supplied by the caller needs the same invalidation as one we
    # discover below. Skipping planned modules in visit() must not hide it.
    new_modules = {mod for mod in planned
                   if not (published / PurePosixPath(*mod.split(".")).with_suffix(".olean")).is_file()}
    # Replacing an existing module can change the kernel types in every compiled
    # importer, even when those importers' source texts have not changed. Their
    # old objects cannot be mixed with the caller's replacement via --setup.
    replaced_modules = planned - new_modules
    for artifact in lb.rglob("*.olean"):
        rel = artifact.relative_to(lb)
        mod = ".".join(rel.with_suffix("").parts)
        if not (published / rel).is_file():
            new_modules.add(mod)
        else:
            replaced_modules.add(mod)
    snapshot = None
    landings = None

    def visit(mod, force=False):
        nonlocal snapshot, landings
        if mod in planned or mod in done:
            return
        # These are repository roots, not arbitrary package or filesystem paths.
        parts = mod.split(".")
        if parts[0] not in ("Sheaf", "WeilConjectures", "Comparator") or not all(
                part and part not in (".", "..") and "/" not in part and "\\" not in part
                for part in parts):
            return
        rel = PurePosixPath(*parts).with_suffix(".lean")
        has_published = (published / rel.with_suffix(".olean")).is_file()
        if (lb / rel.with_suffix(".olean")).is_file():
            return
        if has_published and not force:
            # A published importer can outlive a quarantined dependency's object.
            # Its Lake trace records the imports that Lean will actually load;
            # using live source headers here would pull in unverified proof plans.
            if mod not in checked_published:
                checked_published.add(mod)
                for dep in _published_imports(published, rel):
                    visit(dep)
            return
        source = lean / rel
        if not source.is_file():
            return  # Lean supplies the ordinary missing-module diagnostic.
        if mod in visiting:
            raise DependencySourceError(f"unpublished dependency import cycle at {mod}")
        visiting.add(mod)
        if snapshot is None:
            snapshot = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
        committed = subprocess.run(
            ["git", "show", f"{snapshot}:lean/{rel}"], cwd=repo,
            capture_output=True)
        live = source.read_bytes()
        content, origin = committed.stdout, snapshot
        if committed.returncode or live != content:
            if landings is None:
                landings = _landing_sources(repo)
            staged = _staged_source(repo, rel, live, landings)
            if staged is not None:
                content, rid = staged
                origin = f"{snapshot}+landing:{rid}"
            elif committed.returncode:
                raise DependencySourceError(
                    f"unpublished dependency {mod} has no source committed at {snapshot}; "
                    "no matching completed landing")
            else:
                raise DependencySourceError(
                    f"unpublished dependency {mod} differs from committed source at {snapshot}; "
                    "commit or finish the source change before compiling its dependents "
                    "(no matching completed landing)")
        destination = root / rel
        if destination.exists():
            raise DependencySourceError(
                f"unpublished dependency {mod} has an unscheduled caller source; "
                "include it in the compile jobs")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(content)
        for dep in header_imports(destination):
            visit(dep)
        visiting.remove(mod)
        done.add(mod)
        if not has_published:
            new_modules.add(mod)
        dependencies.append({"rel": str(rel), "out": True, "probe": "",
                             "upstream": parts[0] != "Sheaf", "dependency": mod,
                             "source_commit": origin})

    for job in jobs:
        for mod in header_imports(root / job["rel"]):
            visit(mod)
    if not new_modules and not replaced_modules:
        return dependencies

    # Look through published importers without importing their newer proof plans
    # into this request. An edge to a newly supplied module invalidates an old
    # owner that may still contain definitions moved into that module.
    # For existing replacements, rebuild the whole affected ancestor chain in
    # this request's import closure. Unaffected published objects stay in place.
    graph, compiled_imports = {}, {}
    todo = [mod for job in jobs for mod in header_imports(root / job["rel"])]
    while True:
        while todo:
            mod = todo.pop()
            if mod in graph or mod in planned:
                continue
            parts = mod.split(".")
            if parts[0] not in ("Sheaf", "WeilConjectures", "Comparator") or not all(
                    part and part not in (".", "..") and "/" not in part and "\\" not in part
                    for part in parts):
                continue
            rel = PurePosixPath(*parts).with_suffix(".lean")
            # A caller object has precedence and its source need not be in this tar.
            if (lb / rel.with_suffix(".olean")).is_file():
                continue
            source = root / rel if mod in done else lean / rel
            if not source.is_file():
                continue
            # Stop at unrelated missing objects; their proof plans are not used by
            # the published objects this request actually loads.
            if mod not in done and not (published / rel.with_suffix(".olean")).is_file():
                continue
            graph[mod] = header_imports(source)
            compiled_imports[mod] = _published_imports(published, rel)
            todo.extend(graph[mod] + compiled_imports[mod])

        previous = set(new_modules), set(replaced_modules)
        for mod, imports in graph.items():
            affected = bool(replaced_modules.intersection(imports + compiled_imports[mod]))
            if mod not in done and (affected or new_modules.intersection(imports)):
                visit(mod, force=True)
            if affected:
                replaced_modules.add(mod)
        if previous == (new_modules, replaced_modules):
            break

        todo.extend((new_modules - previous[0]) | (replaced_modules - previous[1]))

    # A newly supplied module can itself import an old owner selected above.
    # Put the whole overlay in import order after the invalidation pass.
    by_module = {job["dependency"]: job for job in dependencies}
    ordered, active, emitted = [], set(), set()

    def emit(mod):
        if mod in emitted or mod not in by_module:
            return
        if mod in active:
            raise DependencySourceError(f"unpublished dependency import cycle at {mod}")
        active.add(mod)
        job = by_module[mod]
        for dep in header_imports(root / job["rel"]):
            emit(dep)
        active.remove(mod)
        emitted.add(mod)
        ordered.append(job)

    for job in dependencies:
        emit(job["dependency"])
    return ordered


def compile_order(jobs, dependencies, root, header_imports):
    """Interleave caller jobs and private dependencies in source import order.

    A rebuilt published importer may use a new owner supplied as a caller job.
    It cannot compile in a separate dependency prefix before that owner exists.
    """
    by_module = {str(PurePosixPath(job["rel"]).with_suffix("")).replace("/", "."): job
                 for job in dependencies + jobs}
    ordered, active, emitted = [], set(), set()

    def emit(mod):
        if mod in emitted or mod not in by_module:
            return
        if mod in active:
            raise DependencySourceError(f"private compile import cycle at {mod}")
        active.add(mod)
        job = by_module[mod]
        for dep in header_imports(root / job["rel"]):
            emit(dep)
        active.remove(mod)
        emitted.add(mod)
        ordered.append(job)

    # Keep rebuilt transitive importers ahead of all consumers: a published
    # intermediary can still import them without appearing in by_module.
    for job in dependencies + jobs:
        emit(str(PurePosixPath(job["rel"]).with_suffix("")).replace("/", "."))
    return ordered
