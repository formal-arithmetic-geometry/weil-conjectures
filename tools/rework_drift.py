#!/usr/bin/env python3
"""Drift check before a rework restore (the owner, 2026-10-28 02:10): a quarantined module whose dependencies changed
their interface while it sat in quarantine/ is compiled alone before the cluster restore puts it back; only those that
compile go back.

Why: on 10-27/28 restored modules failed again and again in the verifying global build because their imports had
changed meanwhile (DiagonalScalarRestrictionComposition, SfQbarLocalizationCommonStage, TowerClassPositiveUnitSquare,
CoefficientTowerShriekInterfaces, IntegralDirectImageTowerData); each such failure took thousands of importers out
again (01:43 b0d3df954be: 1004 landings dropped, 2733 importers quarantined), about one hour per round.

Drift candidates (name-based, no Lean; the logic of tools/related_modules.py) of a planned restore (rework.cluster_set):
  - reference: the last verified main (refs/heads/sheaf-verified reflog) at or before the row's quarantine time, or,
    once the module has a compile result here, the published build that result was compiled against;
  - changed: every module whose text (lean/ or quarantine/) differs between the reference and now and whose change
    alters its interface (related_modules.interface_changed);
  - a planned module is a candidate when its own quarantined text changed since the reference, when it imports a
    changed module directly, when its source mentions a declaration a changed module of its import closure added,
    removed or restated, or a class whose instances/attributes changed (related_modules.related, parts 1-3), and every
    error root put back (a root whose text was never compiled as it is).
Pre-compile (`run`, a detached process started by the restore): each candidate alone against the current published
build, with its quarantined imports compiled first in the same call (tools/remote_compile_set.py through
importer_compile._call: the project's compile slots, `lean -j1`, LEAN_NUM_THREADS=1, the 60 s rule, 120 s run limit;
SHEAF_DRIFT_PARALLEL calls at once), in dependency order. Results are durable (local/rework-drift.json: module ->
quarantined text hash, published build, status, compiler output) and reused while the text and the published build
are unchanged (or no drift since that build), so an attempt cut short resumes.
Restore (hold(), called by rework.cluster_restore): everything planned comes back except
  - a candidate without a result yet, for at most SHEAF_DRIFT_CAP (2700 s) after it was first held (then it comes back
    and the build decides: restores never stall), and
  - a module that FAILS (its own compiler error): it becomes an error root (coord/rework.tsv cause `error: <message>`,
    its text marked tried: rework.cluster_set blocks it and its importers; the queue dispatches it to the rework lane).
  - the quarantined importers of both.
INFRA and SLOW results do not block (an INFRA without a slot is retried once).

    tools/rework_drift.py status           the planned restore, its candidates and their results
    tools/rework_drift.py run              the pre-compile (one at a time: local/rework-drift.lock)
    tools/rework_drift.py measure          candidates and pre-compile of every quarantined module that is no confirmed
                                           root, as if the roots were fixed (results in local/rework-drift-measure.json;
                                           marks nothing)
"""
from __future__ import annotations
import collections, fcntl, hashlib, json, os, pathlib, re, subprocess, sys, threading, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

ROOT = li.ROOT
TOOLS = pathlib.Path(__file__).resolve().parent
STATE = ROOT / "local" / "rework-drift.json"
STATE_LOCK = ROOT / "local" / "rework-drift.state.lock"
RUN_LOCK = ROOT / "local" / "rework-drift.lock"
LOG = ROOT / "local" / "rework-drift.log"
IFACE = ROOT / "local" / "rework-drift-iface.json"
CAP = int(os.environ.get("SHEAF_DRIFT_CAP", "2700"))
PARALLEL = int(os.environ.get("SHEAF_DRIFT_PARALLEL", "8"))
INFRA_TRIES = 2
SKIP_DIRS = ("Comparator/", ".sandbox/", ".lake/")


def log(msg: str) -> None:
    print(f"{time.strftime('%F %T')} rework drift: {msg}", flush=True)


def sha(b: bytes) -> str:
    return hashlib.sha1(b).hexdigest()


# ---------------------------------------------------------------- durable state

def _jload(p: pathlib.Path) -> dict:
    try:
        d = json.loads(p.read_text())
        return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def _jsave(p: pathlib.Path, d: dict) -> None:
    tmp = p.with_name(p.name + f".tmp{os.getpid()}")
    tmp.write_text(json.dumps(d))
    os.replace(tmp, p)


class _StateLock:
    def __enter__(self):
        self.f = open(STATE_LOCK, "a"); fcntl.flock(self.f, fcntl.LOCK_EX); return self

    def __exit__(self, *a):
        fcntl.flock(self.f, fcntl.LOCK_UN); self.f.close()


def update_state(fn, path: pathlib.Path = STATE):
    with _StateLock():
        d = _jload(path)
        d.setdefault("results", {}); d.setdefault("since", {})
        r = fn(d)
        _jsave(path, d)
        return r


def published() -> str:
    return _jload(ROOT / "local" / "builds" / "published.json").get("commit") or ""


# ---------------------------------------------------------------- texts and references

def git(*a, input_=None, check=True) -> str:
    r = subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True, input=input_)
    if check and r.returncode:
        raise RuntimeError(f"git {' '.join(a[:3])}: {r.stderr.strip()[:300]}")
    return r.stdout


def verified_reflog() -> list[tuple[int, str]]:
    """[(unix time, commit)] of refs/heads/sheaf-verified, oldest first"""
    out = []
    for l in git("log", "-g", "--format=%H %gd", "--date=unix", "refs/heads/sheaf-verified", check=False).splitlines():
        m = re.match(r"([0-9a-f]{40}) \S+@\{(\d+)\}", l)
        if m:
            out.append((int(m.group(2)), m.group(1)))
    return sorted(out)


def _utc(s: str) -> int | None:
    try:
        import calendar
        return calendar.timegm(time.strptime(s, "%Y-%m-%dT%H:%M:%SZ"))
    except (ValueError, TypeError):
        return None


def ref_at(t: str, reflog: list) -> str | None:
    """the last verified main at or before the quarantine time `t` (else the last commit of HEAD before it)"""
    u = _utc(t)
    if u is None:
        return None
    best = None
    for ts, c in reflog:
        if ts <= u:
            best = c
    if best:
        return best
    c = git("log", "-1", "--format=%H", f"--before={t}", "HEAD", check=False).strip()
    return c or None


def _mod_of_path(p: str) -> str | None:
    if not p.endswith(".lean"):
        return None
    for pre in ("lean/", "quarantine/"):
        if p.startswith(pre):
            rel = p[len(pre):]
            if rel.startswith(SKIP_DIRS) or "/.sandbox/" in rel or "/.lake/" in rel:
                return None
            return rel[:-5].replace("/", ".")
    return None


def current_text(m: str) -> str | None:
    rel = m.replace(".", "/") + ".lean"
    for p in (ROOT / "lean" / rel, ROOT / "quarantine" / rel):
        try:
            return p.read_text(errors="ignore")
        except OSError:
            continue
    return None


def blob_texts(oids: set) -> dict[str, str]:
    """object id -> text"""
    oids = sorted(o for o in oids if o)
    if not oids:
        return {}
    p = subprocess.run(["git", "cat-file", "--batch"], cwd=ROOT, input="".join(o + "\n" for o in oids).encode(),
                       capture_output=True)
    buf, k, out = p.stdout, 0, {}
    for o in oids:
        nl = buf.index(b"\n", k)
        head = buf[k:nl].split(); k = nl + 1
        if len(head) < 3 or head[1] == b"missing":
            continue
        n = int(head[2]); out[o] = buf[k:k + n].decode(errors="ignore"); k += n + 1
    return out


_TREES: dict = {}


def module_blobs(rev: str) -> dict[str, str]:
    """module -> git blob of its text at commit `rev` (lean/ path, else quarantine/ path)"""
    hit = _TREES.get(rev)
    if hit is not None:
        return hit
    lean, quar = {}, {}
    for l in git("ls-tree", "-r", rev, "--", "lean", "quarantine").splitlines():
        meta, _, path = l.partition("\t")
        f = meta.split()
        if len(f) < 3 or f[1] != "blob":
            continue
        m = _mod_of_path(path)
        if m:
            (lean if path.startswith("lean/") else quar)[m] = f[2]
    quar.update(lean)
    if len(_TREES) > 8:
        _TREES.clear()
    _TREES[rev] = quar
    return quar


def changed_since(rev: str, head: str = "HEAD") -> dict[str, tuple[str | None, str | None]]:
    """module -> (git blob of its text at rev, at head) for every library module whose text, wherever it is (lean/ or
    quarantine/: a move between them is no change), differs between the two commits"""
    a, b = module_blobs(rev), module_blobs(head)
    return {m: (a.get(m), b.get(m)) for m in set(a) | set(b) if a.get(m) != b.get(m)}


# ---------------------------------------------------------------- what a change means for its importers

def _h(*xs) -> str:
    return sha(json.dumps(xs, ensure_ascii=False).encode())[:16]


def change_entries(old: str | None, new: str | None) -> dict:
    """What one module's change means for the modules importing it (tools/related_modules.py, per declaration so that
    a declaration moved unchanged between two changed modules can be recognised): {"itf": interface changed,
    "e": [[sign, key, literals, classes, added-instance [classes, constants] or None]]}. sign + added, - removed,
    ~ restated; key identifies an added/removed declaration or relevant command with its text."""
    import related_modules as rm
    itf = rm.interface_changed(old, new) if old is not None else new is not None
    out = {"itf": bool(itf), "e": []}
    if not itf:
        return out
    a, b = rm._iface(old), rm._iface(new)
    for k in a:
        if k not in b:
            out["e"].append(["-", _h("n", k, a[k]), [rm._literal(k)], [], None])
        elif a[k] != b[k]:
            out["e"].append(["~", "", [rm._literal(k)], [], None])
    for k in b:
        if k not in a:
            out["e"].append(["+", _h("n", k, b[k]), [rm._literal(k)], [], None])
    ca = {rm._ident(c): c for c in rm._cmds(old) if rm._relevant(c)}
    cb = {rm._ident(c): c for c in rm._cmds(new) if rm._relevant(c)}
    for k in sorted(set(ca) | set(cb), key=str):
        x, y = ca.get(k), cb.get(k)
        if x and y and (x.get("head"), x["text"]) == (y.get("head"), y["text"]):
            continue
        c = y or x
        sign = "+" if x is None else "-" if y is None else "~"
        key = _h("c", list(k), c.get("head"), c["text"]) if sign != "~" else ""
        inst = c["kind"] == "instance" or bool(re.search(r"\binstance\b", c.get("head") or ""))
        if inst:
            got = rm.classes_of(c.get("statement") or "")
        elif c["kind"] in ("class", "structure"):
            got = {c["name"].split(".")[-1]}
        elif c["kind"] == "other":
            m = re.match(r"attribute\s*\[[^\]]*\]\s*(.*)$", c["text"])
            toks = re.split(r"\s+in\b", m.group(1))[0].split() if m else []
            got = {t.split(".")[-1] for t in toks if re.match(r"[^\W\d]", t)}
        else:
            got = {c["name"].split(".")[-1]} if c["name"] else set()
        got = sorted(t for t in got if t and t not in rm._STOP)
        if inst and sign == "+" and got:
            out["e"].append([sign, key, [], [], [got, sorted(rm.constants_of(c.get("statement") or "", set(got)))]])
        elif got:
            out["e"].append([sign, key, [], got, None])
    return out


def _strip(t: str) -> str:
    return re.sub(r"/-.*?-/|--[^\n]*", " ", t, flags=re.S)


_IDENT = re.compile(r"[^\W\d][\w'₀-₉!?]*(?:\.[^\W\d][\w'₀-₉!?]*)*")
_TOKENS: dict = {}


def tokens(text: str) -> set:
    """what a mention of a literal can match in the text: every component of a dotted identifier and every pair of
    consecutive components (a literal is a last name component, or the last two when the last is short)"""
    k = sha(text.encode())
    hit = _TOKENS.get(k)
    if hit is not None:
        return hit
    out = set()
    for x in _IDENT.findall(_strip(text)):
        seg = x.split(".")
        out.update(seg)
        out.update(f"{seg[i]}.{seg[i + 1]}" for i in range(len(seg) - 1))
    if len(_TOKENS) > 5000:
        _TOKENS.clear()
    _TOKENS[k] = out
    return out


def graph(rows: dict) -> tuple[dict, dict]:
    """(imports of the library with the quarantined copies' imports, rework.rework_imports of the live rows)"""
    import rework
    _, imports = li.scan()
    live = {m: rows[m] for m in rows if not rework.landed(m)}
    rimp = rework.rework_imports(live)
    g = dict(imports); g.update(rimp)
    return g, rimp


def blob_of(m: str, rows: dict) -> str | None:
    import rework
    p = ROOT / ((rows.get(m) or {}).get("quarantine") or rework.qpath(m))
    try:
        return sha(p.read_bytes())
    except OSError:
        return None


def reach_bits(starts, g: dict, index: dict) -> dict:
    """module -> bitset (int) of the modules of `index` ({module: bit}) in its import closure (itself excluded);
    computed only over the project's modules (the rest import none of them)"""
    memo: dict = {}
    proj = ("Sheaf.", "WeilConjectures.", "Weil.", "Comparator.")
    for s in starts:
        if s in memo:
            continue
        stack = [(s, iter(sorted(g.get(s, ()))))]
        acc = {s: 0}
        while stack:
            m, it = stack[-1]
            nxt = None
            for i in it:
                if not i.startswith(proj):
                    continue
                if i in memo:
                    acc[m] |= memo[i] | (1 << index[i] if i in index else 0)
                elif i in acc:
                    continue                       # an import cycle: what is reached through it is counted once
                else:
                    nxt = i; break
            if nxt is not None:
                acc[nxt] = 0
                stack.append((nxt, iter(sorted(g.get(nxt, ())))))
                continue
            stack.pop()
            memo[m] = acc.pop(m)
            if stack:
                p = stack[-1][0]
                acc[p] |= memo[m] | (1 << index[m] if m in index else 0)
    return memo


def candidates(rows: dict, scope, results: dict, pub: str, g: dict | None = None, timing: dict | None = None,
               head: str | None = None, text_of=None) -> dict:
    """{module in scope: why it is a drift candidate} for the modules of `scope` that need a compile before they go
    back, and {module: "FAIL"} for those whose result for their present text is a failure. A module with a result for
    its present text compiled against the published build `pub` needs none (the best this build can say); one with a
    result against an older build is a candidate only when something drifted since that build."""
    t0 = time.time()
    if g is None:
        g, _ = graph(rows)
    reflog = verified_reflog()
    out: dict[str, str] = {}
    by_ref: dict[str, list[str]] = collections.defaultdict(list)
    for m in sorted(scope):
        b = blob_of(m, rows)
        r = results.get(m)
        if r and r.get("blob") == b:
            st = r.get("status")
            if st == "FAIL":
                out[m] = "FAIL"; continue
            if st == "INFRA" and r.get("tries", 1) < INFRA_TRIES:
                out[m] = f"retry after INFRA ({(r.get('out') or '')[:80]})"; continue
            if r.get("pub") == pub:
                continue
            ref = r.get("pub")
        else:
            cause = (rows.get(m) or {}).get("cause") or ""
            if cause.startswith("error:") or "does not compile alone within" in cause:
                out[m] = "error root put back without a compile of its present text"; continue
            ref = ref_at((rows.get(m) or {}).get("time") or "", reflog)
        if not ref:
            out[m] = "no reference build for its quarantine time"; continue
        by_ref[ref].append(m)
    cache = _jload(IFACE)
    head = head or git("rev-parse", "HEAD").strip()
    text_of = text_of or current_text
    nchg = 0
    for ref, mods in sorted(by_ref.items()):
        try:
            ch = changed_since(ref, head)
        except (RuntimeError, ValueError) as exc:
            for m in mods:
                out[m] = f"changes since {ref[:10]} unreadable ({exc!r})"[:200]
            continue
        nchg += len(ch)
        need = {f"{a or '-'}:{b or '-'}": (a, b) for a, b in ch.values()}
        miss = {k: v for k, v in need.items() if k not in cache}
        if miss:
            txt = blob_texts({x for v in miss.values() for x in v})
            for k, (a, b) in miss.items():
                cache[k] = change_entries(txt.get(a) if a else None, txt.get(b) if b else None)
        info = {x: cache[f"{a or '-'}:{b or '-'}"] for x, (a, b) in ch.items()}
        itf = sorted(x for x, i in info.items() if i["itf"])
        # a declaration or relevant command removed from one changed module and added unchanged to another: moved
        plus = {e[1] for x in itf for e in info[x]["e"] if e[0] == "+"}
        minus = {e[1] for x in itf for e in info[x]["e"] if e[0] == "-"}
        index = {x: k for k, x in enumerate(itf)}
        lit_bits: dict[str, int] = collections.defaultdict(int)
        added = []
        for x in itf:
            for sign, key, lits, cls, ad in info[x]["e"]:
                if (sign == "-" and key in plus) or (sign == "+" and key in minus):
                    continue
                for t in lits + cls:
                    lit_bits[t] |= 1 << index[x]
                if ad:
                    added.append((set(ad[0]), set(ad[1]), 1 << index[x]))
        bits = reach_bits(mods, g, index)
        for m in mods:
            if m in ch:
                out[m] = f"own text changed since {ref[:10]}"; continue
            rb = bits.get(m, 0)
            if not rb:
                continue
            direct = [i for i in sorted(g.get(m, ())) if i in index]
            if direct:
                out[m] = f"imports {direct[0]} (interface changed since {ref[:10]})" + (f" +{len(direct) - 1}" if len(direct) > 1 else "")
                continue
            tk = tokens(text_of(m) or "")
            hit = sorted(t for t in tk & set(lit_bits) if lit_bits[t] & rb)
            for cl, co, bit in added:
                if bit & rb and tk & cl and (not co or tk & co):
                    hit += sorted(tk & cl)
            if hit:
                hit = sorted(set(hit))
                by = [x for x in itf if rb >> index[x] & 1 and any(lit_bits.get(t, 0) >> index[x] & 1 for t in hit)]
                out[m] = f"mentions {', '.join(hit[:4])} changed since {ref[:10]} in {', '.join(by[:3])}" + (f" +{len(by) - 3}" if len(by) > 3 else "")
    if len(cache) > 60000:
        cache = dict(list(cache.items())[-40000:])
    try:
        _jsave(IFACE, cache)
    except OSError:
        pass
    if timing is not None:
        timing.update(seconds=round(time.time() - t0, 1), refs=len(by_ref), changed=nchg)
    return out


# ---------------------------------------------------------------- the restore's hold

def importers_within(seeds: set, rimp: dict, among: set) -> set:
    rev = collections.defaultdict(set)
    for m, ims in rimp.items():
        for i in ims:
            if i != m:
                rev[i].add(m)
    out, st = set(seeds), list(seeds)
    while st:
        for p in rev.get(st.pop(), ()):
            if p in among and p not in out:
                out.add(p); st.append(p)
    return out


def runner_alive() -> bool:
    try:
        f = open(RUN_LOCK, "a")
    except OSError:
        return False
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        f.close(); return True
    fcntl.flock(f, fcntl.LOCK_UN); f.close()
    return False


def spawn_runner() -> None:
    if runner_alive():
        return
    env = dict(os.environ, SHEAF_LEAD=os.environ.get("SHEAF_LEAD", "L-only"))
    with open(LOG, "a") as lf:
        subprocess.Popen([sys.executable, str(TOOLS / "rework_drift.py"), "run"], cwd=str(ROOT), stdin=subprocess.DEVNULL,
                         stdout=lf, stderr=subprocess.STDOUT, start_new_session=True, env=env)


def hold(rows: dict, put: list[str], spawn: bool = True) -> tuple[set, str]:
    """(modules of `put` that stay in quarantine/ this time, a log note). Called by rework.cluster_restore."""
    if not put:
        return set(), ""
    pub = published()
    g, rimp = graph(rows)
    st = update_state(lambda d: d)
    tm: dict = {}
    c = candidates(rows, put, st["results"], pub, g, tm)
    fail = {m for m, w in c.items() if w == "FAIL"}
    pend = {m: w for m, w in c.items() if w != "FAIL"}
    now = time.time()
    blobs = {m: blob_of(m, rows) for m in pend}

    def mark(d):
        s = d["since"]
        for m in pend:
            if not (isinstance(s.get(m), list) and s[m][0] == blobs[m]):
                s[m] = [blobs[m], now]
        for m in [m for m in s if m not in rows]:
            s.pop(m, None)
        return dict(s)
    # a dry run (status, cluster-restore --dry-run) does not start the clock
    since = update_state(mark) if spawn else mark({"since": dict(st.get("since") or {}), "results": {}})
    waiting = {m for m in pend if now - since[m][1] < CAP}
    released = sorted(set(pend) - waiting)
    held = importers_within(waiting | fail, rimp, set(put))
    if waiting and spawn:
        spawn_runner()
    note = (f"drift check: {len(c)} candidate(s) of {len(put)} ({tm.get('seconds')} s, {tm.get('changed')} changed modules "
            f"since {tm.get('refs')} reference build(s)); {len(waiting)} wait for their compile, {len(fail)} failed, "
            f"{len(released)} past the {CAP // 60}-min cap go back unchecked; {len(held)} stay in quarantine/ this time")
    return held, note


# ---------------------------------------------------------------- the pre-compile

_MISSING = re.compile(r"object file .* of module (\S+) does not exist")


def classify(r: dict, failed_jobs: set) -> str:
    rc, out = r.get("rc"), r.get("out") or ""
    if rc == 0:
        return "OK"
    if rc is None:
        return "NOT RUN" if r.get("budget") else "INFRA"
    if "Dependency source unavailable" in out or "failed in the private compile overlay" in out:
        return "INFRA"
    m = _MISSING.search(out)
    if m:
        return "DEP" if m.group(1) in failed_jobs else "INFRA"
    if "environment already contains" in out:
        return "INFRA"
    if rc == 124:
        return "SLOW"
    return "FAIL"


def message(out: str) -> str:
    out = re.sub(r"/\S*?/rset-tmp/c-[^/]+/lean/", "", out or "")
    lines = out.splitlines()
    k = next((i for i, l in enumerate(lines) if ": error" in l or l.startswith("error")), None)
    msg = " | ".join(x.strip() for x in lines[k:k + 4]) if k is not None else (lines[-1] if lines else "?")
    return re.sub(r"\s+", " ", msg)


def topo(mods: set, g: dict) -> list[str]:
    """`mods` in import order (an import first)"""
    order, seen = [], set()

    def visit(m, stack=()):
        if m in seen or m in stack:
            return
        for i in sorted(g.get(m, ())):
            if i in mods:
                visit(i, stack + (m,))
        seen.add(m); order.append(m)
    for m in sorted(mods):
        visit(m)
    return order


def mark_failed(fails: dict) -> int:
    """fails {module: (blob, message)}: error roots (cause, tried) in coord/rework.tsv, one commit"""
    import rework, mergelock
    if not fails:
        return 0
    n = 0
    with mergelock.merge_lock():
        rows = rework.load()
        tried, tb = _jload(rework.TRIED), _jload(rework.TRIED_BUILD)
        pub = published()
        for m, (b, msg) in sorted(fails.items()):
            if m not in rows or rework.landed(m) or blob_of(m, rows) != b:
                continue
            rows[m]["cause"] = ("error: " + msg + " (drift check: compiled alone before the restore)")[:300]
            tried[m] = b; tb[m] = pub; n += 1
        if not n:
            return 0
        rework.save(rows)
        _jsave(rework.TRIED, tried); _jsave(rework.TRIED_BUILD, tb)
        git("add", "--", "coord/rework.tsv")
        git("-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m",
            f"rework drift check: {n} quarantined module(s) fail alone against the published build; error roots, not "
            "restored: " + ", ".join(sorted(fails))[:300] + "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>",
            "--", "coord/rework.tsv", check=False)
    return n


def precompile_calls(rows: dict, cands: list[str], g: dict, deadline: float, state_path: pathlib.Path = STATE,
               mark: bool = True, parallel: int = PARALLEL) -> dict:
    """compile each candidate (with its quarantined imports first, in the same call) against the published build;
    candidates in dependency order (one whose quarantined imports contain another candidate waits for it); results
    written to `state_path` as they arrive. Returns {status: count}."""
    import importer_compile as ic
    import rework
    live = {m for m in rows if not rework.landed(m)}
    memo: dict = {}
    qcl = {m: (li.closure(m, g, memo) & live) - {m} for m in cands}
    cset = set(cands)
    done: dict[str, str] = {}
    counts = collections.Counter()
    lock = threading.Lock()
    todo = list(topo(cset, g))
    # 2026-10-28 (maintainer): the candidates most quarantined modules wait for go first. In plain import order the
    # roots under Sheaf.SixFunctors/Sheaf.Targets (219 and 213 waiting importers) came after ~200 Sheaf.Paper leaves
    # and kept the freeze up. A module's weight (its quarantined importers) exceeds each importer's, so the order stays
    # an import order; ready() still waits for dependencies.
    wt = collections.Counter()
    for x in live:
        for d in (li.closure(x, g, memo) & live) - {x}:
            wt[d] += 1
    todo.sort(key=lambda m: -wt[m])
    running: set = set()
    pub = published()
    prev = _jload(state_path).get("results") or {}

    def ready(m):
        dep = qcl[m] & cset
        return all(d in done for d in dep) and not (dep & running)

    failed_now: set = set()      # modules (candidates or their quarantined imports) failing in this run

    def blocked(m):
        return bool(qcl[m] & failed_now) or any(done.get(d) in ("FAIL", "DEP") for d in qcl[m] & cset) or any(
            (prev.get(d) or {}).get("status") == "FAIL" and (prev.get(d) or {}).get("blob") == blob_of(d, rows)
            for d in qcl[m])

    def work():
        while True:
            with lock:
                if time.time() > deadline - 60:
                    return
                pick = None
                for m in todo:
                    if m not in running and ready(m):
                        pick = m; break
                if pick is None:
                    if not todo:
                        return
                    if not running:
                        pick = todo[0]       # a cycle or stale order: go on rather than stall
                wait = pick is None
                if not wait:
                    todo.remove(pick); running.add(pick)
            if wait:
                time.sleep(2); continue
            m = pick
            if blocked(m):
                with lock:
                    done[m] = "DEP"; running.discard(m); counts["DEP"] += 1
                continue
            mods = topo(qcl[m] | {m}, g)
            jobs = []
            for x in mods:
                q = ROOT / ((rows.get(x) or {}).get("quarantine") or rework.qpath(x))
                try:
                    jobs.append((ic.rel_of(x), q.read_text(), True))
                except OSError:
                    pass
            t1 = time.time()
            res = ic._call(jobs, max(120, int(deadline - time.time())), deadline)
            secs = round(time.time() - t1, 1)
            got = {r["rel"][:-5].replace("/", "."): r for r in res or []}
            failed_jobs: set = set()
            stat = {}
            for x in mods:          # in import order: a job failing on a failed earlier job is DEP
                r = got.get(x)
                if r is None:
                    continue
                s = classify(r, failed_jobs)
                if s in ("FAIL", "DEP", "SLOW"):
                    failed_jobs.add(x)
                stat[x] = (s, r)
            fails = {}
            blobs = {x: blob_of(x, rows) for x in stat}

            def put_res(d):
                for x, (s, r) in stat.items():
                    if s in ("NOT RUN", "DEP") or (x != m and s not in ("OK", "FAIL", "SLOW")):
                        continue
                    old = d["results"].get(x) or {}
                    tries = (old.get("tries", 0) + 1) if old.get("blob") == blobs[x] and old.get("status") == "INFRA" else 1
                    d["results"][x] = {"blob": blobs[x], "pub": pub, "status": s, "secs": r.get("secs"),
                                       "time": time.strftime("%FT%TZ", time.gmtime()), "tries": tries,
                                       "out": (r.get("out") or "")[-3000:], "via": m if x != m else ""}
            update_state(put_res, state_path)
            for x, (s, r) in stat.items():
                if s == "FAIL":
                    fails[x] = (blobs[x], message(r.get("out") or ""))
            with lock:
                failed_now.update(fails)
            if mark and fails:
                try:
                    n = mark_failed(fails)
                    log(f"{n} error root(s) marked: {', '.join(sorted(fails))}"[:600])
                except Exception as exc:  # noqa: BLE001
                    log(f"marking failed roots failed ({exc!r})"[:400])
            s_m = stat.get(m, ("NOT RUN", {}))[0]
            log(f"{m}: {s_m} ({len(jobs)} job(s) in {secs} s)" + (f" | {message(stat[m][1].get('out') or '')[:300]}" if s_m in ("FAIL", "SLOW", "INFRA") else "")
                + (f" | failing quarantined import(s): {', '.join(sorted(x for x in fails if x != m))}" if set(fails) - {m} else ""))
            with lock:
                done[m] = s_m; running.discard(m); counts[s_m] += 1
    ths = [threading.Thread(target=work) for _ in range(max(1, parallel))]
    for t in ths:
        t.start()
    for t in ths:
        t.join()
    counts["NOT RUN"] += len(todo)
    return dict(counts)



# ---------------------------------------------------------------- the shared pre-compile (2026-10-28)
# 2026-10-28 09:20 (lead): the per-candidate calls (precompile_calls) sent each candidate with its whole quarantined
# import chain, so a chain of ~100 quarantined modules went through the compile service once per candidate (~85 s per
# call even with the service's result cache: closure keys, tar transfer and artifact copies for every job), and 683
# blocked modules trickled back over an hour. The shared pre-compile compiles the union of the candidates' quarantined
# closures ONCE, in import order, several files at a time (each `lean -j1`, LEAN_NUM_THREADS=1, the 60 s rule, the
# 120 s run limit), into one output tree per published build, local/rework-drift-cache/<published>/build. A module's
# compiled files are reused, in this run and in later runs against the same published build, while its key is
# unchanged: the hash of its text and of the keys of the modules of the tree it imports (<rel>.dkey next to the .olean).
# Committed library modules whose compiled files the published build lacks are compiled into the same tree first.
SHARED = os.environ.get("SHEAF_DRIFT_SHARED", "1") != "0"
SHARED_PARALLEL = int(os.environ.get("SHEAF_DRIFT_SHARED_PARALLEL", "16"))
CACHE_DIR = ROOT / "local" / "rework-drift-cache"
ACCEPT = int(os.environ.get("SHEAF_FILE_TIMEOUT", "60"))
RUN_LIMIT = max(ACCEPT, int(os.environ.get("SHEAF_FILE_RUN_LIMIT", "120")))
LEAN = ROOT / "lean"
PUB = LEAN / ".lake" / "build" / "lib" / "lean"


def _lean_opts() -> list[str]:
    """the [leanOptions] of lean/lakefile.toml, as tools/remote_compile_set.py passes them"""
    out, on = [], False
    try:
        lines = (LEAN / "lakefile.toml").read_text().split("\n")
    except OSError:
        return out
    for l in lines:
        if l.startswith("[leanOptions]"):
            on = True; continue
        if l.startswith("["):
            on = False
        m = re.match(r"([A-Za-z][\w.]*)\s*=\s*([^#]*)", l) if on else None
        if m:
            out.append(f"-D{m.group(1)}={m.group(2).strip().strip(chr(34))}")
    return out


def _upstream(rel: str) -> bool:
    return rel.startswith("WeilConjectures/") or rel.startswith("Comparator/")


def _rel(m: str) -> str:
    return m.replace(".", "/") + ".lean"


def _run_lean(rel: str, src_root: pathlib.Path, out_root: pathlib.Path) -> dict:
    """compile src_root/rel into out_root (olean and companions): {rc, out, secs}; rc 124 when stopped at RUN_LIMIT"""
    o = out_root / rel[:-5]
    o.parent.mkdir(parents=True, exist_ok=True)
    for x in o.parent.glob(o.name + ".*"):
        x.unlink()
    lp = ":".join([str(out_root), str(PUB)] + sorted(str(x) for x in (LEAN / ".lake" / "packages").glob("*/.lake/build/lib/lean")))
    thp = [str(TOOLS / "thp-off")] if os.access(TOOLS / "thp-off", os.X_OK) else []
    cmd = ["nice", "-n", "19", *thp, str(pathlib.Path.home() / ".elan" / "bin" / "lean"), "-j1", *_lean_opts(),
           *([] if _upstream(rel) else ["-DautoImplicit=false"]), "-R", str(src_root),
           "-o", str(o) + ".olean", "-i", str(o) + ".ilean", str(src_root / rel)]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, cwd=str(LEAN), env=dict(os.environ, LEAN_PATH=lp, LEAN_NUM_THREADS="1"),
                           capture_output=True, text=True, timeout=RUN_LIMIT)
        rc, out = p.returncode, (p.stdout or "") + (p.stderr or "")
    except subprocess.TimeoutExpired as e:
        rc = 124
        out = (e.stdout.decode(errors="ignore") if isinstance(e.stdout, bytes) else (e.stdout or "")) + \
            f"\nNOT ACCEPTED: stopped after {RUN_LIMIT} s\n"
    secs = round(time.time() - t0, 1)
    if rc == 0 and secs > ACCEPT:
        out += f"\nNOT ACCEPTED: compiled in {secs} s > {ACCEPT} s, the limit for one file\n"
    return {"rc": rc, "out": out, "secs": secs}


def shared_plan(cands, rows: dict, g: dict, live: set, has_pub=None, lean_text=None) -> tuple[list[str], dict]:
    """(modules to compile in import order, {module: source path}): the candidates, their quarantined imports (live
    rework rows) and the committed library modules on the way that the published build lacks"""
    import rework
    has_pub = has_pub or (lambda m: (PUB / (_rel(m)[:-5] + ".olean")).is_file())
    lean_text = lean_text or (lambda m: (LEAN / _rel(m)).is_file())
    src: dict = {}
    st = list(cands)
    while st:
        m = st.pop()
        if m in src:
            continue
        if m in live:
            src[m] = ROOT / ((rows.get(m) or {}).get("quarantine") or rework.qpath(m))
        elif not has_pub(m) and lean_text(m) and m.startswith(("Sheaf.", "WeilConjectures.", "Weil.", "Comparator.")):
            src[m] = LEAN / _rel(m)
        else:
            continue
        st.extend(i for i in g.get(m, ()) if i not in src)
    return topo(set(src), g), src


def shared_compile(order: list[str], src: dict, g: dict, tree: pathlib.Path, deadline: float,
                   parallel: int = SHARED_PARALLEL, run=None, on_result=None) -> dict:
    """compile `order` (import order) into tree/build from copies in tree/src, `parallel` files at a time, reusing a
    module whose <rel>.dkey matches its key. Returns {module: {status, rc, out, secs, reused}}; status OK, FAIL, SLOW
    (compiled, over the 60 s rule), DEP (an import of the tree failed), INFRA, NOT RUN (deadline)."""
    run = run or _run_lean
    build, srcroot = tree / "build", tree / "src"
    inset = set(order)
    deps = {m: {i for i in g.get(m, ()) if i in inset} for m in order}
    res: dict = {}
    keys: dict = {}
    lock = threading.Lock()
    todo = list(order)
    running: set = set()
    # most dependents first among the ready ones (an import order is kept by ready())
    wt = collections.Counter()
    for m in order:
        for d in deps[m]:
            wt[d] += 1
    todo.sort(key=lambda m: -wt[m])

    def key_of(m):
        h = hashlib.sha256(m.encode())
        try:
            h.update(src[m].read_bytes())
        except OSError:
            return None
        for d in sorted(deps[m]):
            h.update((d + ":" + str(keys.get(d))).encode())
        return h.hexdigest()

    def work():
        while True:
            with lock:
                if not todo:
                    return
                pick = next((m for m in todo if all(d in res for d in deps[m])), None)
                if pick is None:
                    wait = True
                else:
                    wait = False; todo.remove(pick); running.add(pick)
            if wait:
                time.sleep(0.5); continue
            m = pick
            bad = [d for d in deps[m] if res[d]["status"] in ("FAIL", "DEP", "INFRA", "NOT RUN")
                   or (res[d]["status"] == "SLOW" and res[d].get("rc") != 0)]
            rel = _rel(m)
            if bad:
                r = {"status": "DEP" if any(res[d]["status"] in ("FAIL", "DEP", "SLOW") for d in bad) else "INFRA",
                     "rc": None, "out": f"import {sorted(bad)[0]} did not compile", "secs": 0, "reused": False}
            elif time.time() > deadline - 60:
                r = {"status": "NOT RUN", "rc": None, "out": "", "secs": 0, "reused": False}
            else:
                with lock:
                    k = key_of(m)
                kf = build / (rel[:-5] + ".dkey")
                ol = build / (rel[:-5] + ".olean")
                r = None
                try:
                    if k and ol.is_file() and kf.read_text().split()[0] == k:
                        r = {"status": "OK", "rc": 0, "out": "", "secs": float(kf.read_text().split()[1]),
                             "reused": True}
                except (OSError, IndexError, ValueError):
                    r = None
                if r is None:
                    sp = srcroot / rel
                    sp.parent.mkdir(parents=True, exist_ok=True)
                    try:
                        sp.write_bytes(src[m].read_bytes())
                        x = run(rel, srcroot, build)
                    except OSError as e:
                        x = {"rc": None, "out": f"source unreadable: {e!r}", "secs": 0}
                    if x.get("rc") is None:
                        st = "INFRA"
                    elif x["rc"] == 0:
                        st = "SLOW" if x["secs"] > ACCEPT else "OK"
                    elif x["rc"] == 124:
                        st = "SLOW"
                    else:
                        mm = _MISSING.search(x.get("out") or "")
                        st = "INFRA" if mm or "environment already contains" in (x.get("out") or "") else "FAIL"
                    r = dict(x, status=st, reused=False)
                    try:
                        if st == "OK" and k:
                            kf.write_text(f"{k} {x['secs']}\n")
                        elif kf.exists():
                            kf.unlink()
                    except OSError:
                        pass
                with lock:
                    keys[m] = k if r["status"] in ("OK", "SLOW") and r.get("rc") == 0 else None
            with lock:
                res[m] = r; running.discard(m)
            if on_result:
                on_result(m, r)
    ths = [threading.Thread(target=work) for _ in range(max(1, parallel))]
    for t in ths:
        t.start()
    for t in ths:
        t.join()
    return res


def _prune_cache(keep: str) -> None:
    """keep the output trees of the current and the previous published build"""
    try:
        trees = sorted((p for p in CACHE_DIR.iterdir() if p.is_dir()), key=lambda p: p.stat().st_mtime)
    except OSError:
        return
    import shutil
    for p in trees[:-2]:
        if p.name != keep and p.resolve().parent == CACHE_DIR.resolve():
            shutil.rmtree(p, ignore_errors=True)


def precompile_shared(rows: dict, cands: list[str], g: dict, deadline: float, state_path: pathlib.Path = STATE,
                      mark: bool = True, parallel: int = SHARED_PARALLEL) -> dict:
    """the candidates and their quarantined closures compiled once (shared_plan, shared_compile); every module of the
    rework rows gets its result in `state_path`; a module failing on its own text becomes an error root (mark_failed)"""
    import rework
    live = {m for m in rows if not rework.landed(m)}
    pub = published()
    order, src = shared_plan(cands, rows, g, live)
    tree = CACHE_DIR / (pub[:12] or "none")
    tree.mkdir(parents=True, exist_ok=True)
    os.utime(tree)
    _prune_cache(tree.name)
    cset = set(cands)
    counts = collections.Counter()
    t0 = time.time()
    log(f"shared pre-compile: {len(cands)} candidate(s), {len(order)} module(s) to compile once "
        f"({sum(1 for m in order if m in live)} quarantined) into {tree.relative_to(ROOT)}")

    def on_result(m, r):
        s = r["status"]
        if m in cset:
            counts[s] += 1
        if m in rows and s in ("OK", "FAIL", "SLOW", "INFRA"):
            b = blob_of(m, rows)

            def put(d):
                old = d["results"].get(m) or {}
                tries = (old.get("tries", 0) + 1) if old.get("blob") == b and old.get("status") == "INFRA" else 1
                d["results"][m] = {"blob": b, "pub": pub, "status": s, "secs": r.get("secs"),
                                   "time": time.strftime("%FT%TZ", time.gmtime()), "tries": tries,
                                   "out": (r.get("out") or "")[-3000:], "via": "" if m in cset else "shared"}
            update_state(put, state_path)
        if s == "FAIL" and m in rows and mark:
            try:
                n = mark_failed({m: (blob_of(m, rows), message(r.get("out") or ""))})
                log(f"{n} error root(s) marked: {m}")
            except Exception as exc:  # noqa: BLE001
                log(f"marking failed roots failed ({exc!r})"[:400])
        if not r.get("reused"):
            log(f"{m}: {s} ({r.get('secs')} s, shared)" + (f" | {message(r.get('out') or '')[:300]}"
                                                           if s in ("FAIL", "SLOW", "INFRA") else ""))
    res = shared_compile(order, src, g, tree, deadline, parallel, on_result=on_result)
    reused = sum(1 for r in res.values() if r.get("reused"))
    log(f"shared pre-compile done in {time.time() - t0:.0f} s: {len(res)} module(s), {reused} reused, "
        f"candidates {dict(counts)}")
    return dict(counts)


def precompile(rows: dict, cands: list[str], g: dict, deadline: float, state_path: pathlib.Path = STATE,
               mark: bool = True, parallel: int = PARALLEL) -> dict:
    """the shared pre-compile (precompile_shared); SHEAF_DRIFT_SHARED=0: one compile-service call per candidate"""
    if SHARED:
        return precompile_shared(rows, cands, g, deadline, state_path, mark)
    return precompile_calls(rows, cands, g, deadline, state_path, mark, parallel)


def run(measure: bool = False) -> int:
    import rework
    f = open(RUN_LOCK, "a")
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        print("rework drift: another run holds local/rework-drift.lock"); return 0
    T0 = time.time(); deadline = T0 + CAP
    path = ROOT / "local" / "rework-drift-measure.json" if measure else STATE
    total = collections.Counter()
    rounds, last = 0, None
    while time.time() < deadline - 60:
        rows = rework.load()
        put, seeds = rework.cluster_set(rows)
        if measure:
            live = {m for m in rows if not rework.landed(m)}
            put = sorted(live - seeds)
        g, _ = graph(rows)
        st = _jload(path)
        tm: dict = {}
        c = candidates(rows, put, st.get("results") or {}, published(), g, tm)
        todo = sorted(m for m, w in c.items() if w != "FAIL")
        if rounds == 0 or todo:
            log(f"{'measure: ' if measure else ''}{len(put)} planned, {len(c)} candidate(s) ({len(todo)} to compile, "
                f"{len(c) - len(todo)} failed before); analysis {tm.get('seconds')} s over {tm.get('changed')} changed "
                f"module(s) since {tm.get('refs')} reference build(s)")
            for m in todo[:2000]:
                log(f"  candidate {m}: {c[m]}"[:400])
        if not todo or todo == last:
            break                     # nothing left, or the same set again (no progress possible in this run)
        last = todo
        cnt = precompile(rows, todo, g, deadline, path, mark=not measure)
        total.update(cnt)
        rounds += 1
        log(f"round {rounds}: {dict(cnt)} in {time.time() - T0:.0f} s")
        if measure:
            break
    log(f"{'measure ' if measure else ''}done in {time.time() - T0:.0f} s: {dict(total)}")
    fcntl.flock(f, fcntl.LOCK_UN); f.close()
    return 0


def status() -> int:
    import rework
    rows = rework.load()
    put, seeds = rework.cluster_set(rows)
    held, note = hold(rows, put, spawn=False)
    print(f"planned restore: {len(put)} module(s); {len(seeds)} confirmed unfixed roots")
    print(note or "drift check: nothing planned")
    st = _jload(STATE)
    cnt = collections.Counter(r.get("status") for r in (st.get("results") or {}).values())
    print(f"results kept: {dict(cnt)}; runner {'running' if runner_alive() else 'idle'}")
    return 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["run"]:
        sys.exit(run())
    if a[:1] == ["measure"]:
        sys.exit(run(measure=True))
    if a[:1] == ["status"]:
        sys.exit(status())
    print(__doc__); sys.exit(2)
