"""Checks of a delivery that fixes a quarantined rework root (coord/rework.tsv), before it lands.

2026-10-27 (the human): the root Sheaf.AlgebraicGeometry.SfP1ProjectionTraceFalseTail was in quarantine with ~6000
importers. A2 delivered a text byte-identical to the quarantined text that had failed; it was judged against that
quarantined text (no diff: AUTO), landed, tools/batch_land.restore_after_fix put the importers back in the same batch
(14:42, ba045dca0bb) and the next global build failed on the same line: ~6000 modules out again and one more build round
(up to 4400 s). Since then a landing that writes a quarantined rework root:

  1. `unchanged_failing`: is refused when the root's text is the quarantined text that failed (error root of
     coord/rework.tsv, or the blob local/rework-tried.json recorded); tools/stage3_delivery.read_delivery makes it a
     static fail, so review_class never classes it AUTO-passable and tools/batch_land.check returns it to its writer
     with the build error;
  2. `verify` (tools/batch_land.check, in the check-one process): the root, as it would land, is compiled alone against
     the current live build (SHEAF_GROUP=M LEAN_NUM_THREADS=1 tools/lean_file.sh on a scratch copy under
     lean/.sandbox/rootfix/, -j1, the 60 s rule and run limit of coord/sheaf.env). A compile error or a compile over the
     limit refuses the landing (back to the writer with the compiler's message); only a root that compiles lands, and
     only its landing triggers the cluster restore. A root that imports quarantined modules restored in the same
     delivery cannot be compiled alone: as before, the cluster lands and the global build verifies it. An import
     without an .olean yet (landed after the last published build) or a failure of the compile tool makes the delivery
     wait, at most SHEAF_ROOTFIX_WAIT seconds (default 3 h), after which it lands and the global build decides."""
import hashlib, json, os, pathlib, re, shutil, subprocess, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
TRIED = ROOT / "local" / "rework-tried.json"
STATE = ROOT / "local" / "rootfix-checks"
MISSING_OLEAN = re.compile(r"object file .* does not exist|unknown module prefix|file not found|No such file", re.I)
ERROR_LINE = re.compile(r": error|^error", re.M)


def error_root(cause: str) -> bool:
    """the row's cause is a build/compile failure of the module itself (tools/rework.cluster_set's error roots)"""
    c = cause or ""
    return c.startswith("error:") or "does not compile alone within" in c


def sha1(text: str) -> str:
    return hashlib.sha1(text.encode()).hexdigest()


def tried() -> dict:
    try:
        return json.loads(TRIED.read_text())
    except (OSError, ValueError):
        return {}


def unchanged_failing(module: str, text: str | None, quarantined: list[str | None], cause: str,
                      tried_blobs: dict | None = None) -> str | None:
    """The refusal message when `text` is the failing quarantined text of the rework root `module`: equal to one of the
    `quarantined` texts (the copy at the delivery's base, the copy now) while the row's `cause` is an error, or equal to
    the blob local/rework-tried.json records as compiled without success. None otherwise."""
    if text is None:
        return None
    tb = tried() if tried_blobs is None else tried_blobs
    norm = lambda t: "\n".join(l.rstrip() for l in t.strip().split("\n"))  # noqa: E731
    same = error_root(cause) and any(q is not None and (q == text or norm(q) == norm(text)) for q in quarantined)
    if not same and tb.get(module) != sha1(text):
        return None
    return (f"{module}: the delivered text is the quarantined text that failed (unchanged), so it is not a fix of the "
            f"rework root; AUTO review does not apply to it. The build error of that text: {cause or '(see coord/rework.tsv)'}"
            "\nChange the module so that it compiles alone against the current library (tools/lean_file.sh), then deliver.")


def _rows() -> dict:
    import rework
    return rework.load()


def targets(D: dict, item: str, rows: dict) -> list[dict]:
    """the modules of the delivery that fix a quarantined rework root: the item when it is a rework row, and every other
    delivered module that is an error root of coord/rework.tsv"""
    return [m for m in D["modules"] if m.get("text") is not None and m["module"] in rows
            and (m["module"] == item or error_root(rows[m["module"]].get("cause") or ""))]


def _imports(text: str) -> set[str]:
    import leanindex as li
    return set(li.imports_of(text))


def compile_alone(module: str, text: str) -> tuple[str, str]:
    """('ok'|'error'|'missing'|'infra', output) of `text` compiled alone as a scratch copy against the live build"""
    rel = pathlib.Path(*module.split(".")).with_suffix(".lean")
    box = (LEAN / ".sandbox" / "rootfix" / f"{os.getpid()}-{time.time_ns()}").resolve()
    assert str(box).startswith(str((LEAN / ".sandbox" / "rootfix").resolve()) + "/")
    dst = box / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(text)
    env = dict(os.environ, SHEAF_GROUP="M", LEAN_NUM_THREADS="1")
    env.pop("SHEAF_TOOL_TIMEOUT", None)
    run_limit = float(env.get("SHEAF_FILE_RUN_LIMIT") or 120)
    try:
        r = subprocess.run(["bash", str(ROOT / "tools" / "lean_file.sh"), str(dst)], cwd=ROOT, capture_output=True,
                           text=True, env=env, timeout=2 * run_limit + 300)
        rc, out = r.returncode, (r.stdout + r.stderr).replace(str(box) + "/", "")
    except subprocess.TimeoutExpired:
        rc, out = -1, "the compile tool did not return"
    finally:
        shutil.rmtree(box, ignore_errors=True)
    if rc == 0 and not ERROR_LINE.search(out):
        return "ok", out
    if rc == 124:
        return "error", out
    err = ERROR_LINE.search(out)
    if err and MISSING_OLEAN.search(out[err.start():]) and "environment already contains" not in out:
        return "missing", out
    if err:
        return "error", out
    return "infra", out


def _state(head: str) -> dict:
    try:
        return json.loads((STATE / f"{head}.json").read_text())
    except (OSError, ValueError):
        return {}


def _save_state(head: str, st: dict) -> None:
    try:
        STATE.mkdir(parents=True, exist_ok=True)
        tmp = STATE / f".{head}.{os.getpid()}.tmp"
        tmp.write_text(json.dumps(st)); tmp.replace(STATE / f"{head}.json")
    except OSError:
        pass


def _published() -> str:
    try:
        return json.loads((ROOT / "local" / "builds" / "published.json").read_text()).get("commit") or ""
    except (OSError, ValueError):
        return ""


def verify(D: dict, item: str, head: str, Refuse, Wait, rows: dict | None = None, compile_fn=None,
           compile: bool = True) -> dict:
    """Raises Refuse (back to the writer) or Wait; returns {module: 'compiled' | 'with its restored imports'} for the
    rework roots of the delivery that may land (empty: the delivery fixes no rework root)."""
    rows = _rows() if rows is None else rows
    ts = targets(D, item, rows)
    if not ts:
        return {}
    compile_fn = compile_fn or compile_alone
    tb = tried()
    # the identity check again on the text that would land (after a merge agent, the current quarantined copy)
    for m in ts:
        cause = rows[m["module"]].get("cause") or ""
        q = ROOT / (rows[m["module"]].get("quarantine") or ("quarantine/" + m["module"].replace(".", "/") + ".lean"))
        msg = unchanged_failing(m["module"], m["text"], [m.get("old"), q.read_text() if q.is_file() else None], cause, tb)
        if msg:
            raise Refuse(msg)
    if not compile:
        return {m["module"]: "not compiled yet (the batch's check compiles it)" for m in ts}
    pending = {x["module"] for x in D["modules"] if x.get("text") is not None
               and not (LEAN / pathlib.Path(*x["module"].split(".")).with_suffix(".lean")).is_file()}
    st = _state(head)
    pub = _published()
    out_status, waits = {}, []
    for m in ts:
        mod, text = m["module"], m["text"]
        if _imports(text) & (pending - {mod}):
            out_status[mod] = "with its restored imports"   # compiled together by the global build, as before
            continue
        key = f"{mod}:{sha1(text)}:{pub}"
        if (st.get("done") or {}).get(key) == "ok":
            out_status[mod] = "compiled"; continue
        res, out = compile_fn(mod, text)
        if res == "ok":
            st.setdefault("done", {})[key] = "ok"; _save_state(head, st)
            out_status[mod] = "compiled"; continue
        if res == "error":
            lines = out.strip().splitlines()
            k = next((i for i, l in enumerate(lines) if ERROR_LINE.search(l)), max(0, len(lines) - 12))
            raise Refuse(f"{mod} is a quarantined rework root (coord/rework.tsv) and does not compile alone against the "
                         "current library (SHEAF_GROUP=M LEAN_NUM_THREADS=1 tools/lean_file.sh, -j1, the 60 s rule); "
                         "it is not landed, and its quarantined importers stay out:\n" + "\n".join(lines[k:k + 25])[:2400]
                         + "\nFix the module, compile it alone, deliver again.")
        waits.append(f"{mod}: {res}: " + " ".join(out.strip().splitlines()[-2:])[:200])
    if waits:
        first = st.setdefault("first_wait", time.time()); _save_state(head, st)
        if time.time() - first < float(os.environ.get("SHEAF_ROOTFIX_WAIT", "10800")):
            raise Wait("rework root fix not compiled alone yet (an import without .olean or the compile tool failed): "
                       + "; ".join(waits))
        for w in waits:
            out_status[w.split(":")[0]] = "not compiled (wait limit reached)"
    return out_status
