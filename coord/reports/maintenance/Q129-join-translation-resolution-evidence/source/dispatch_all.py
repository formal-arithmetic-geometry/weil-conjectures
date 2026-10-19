#!/usr/bin/env python3
"""One dispatcher for every batch and every stage (the human, 2026-10-15).

    nohup python3 ~/weil-launcher-all/dispatch_all.py > /dev/null 2>&1 &        stop: kill $(cat ~/weil-launcher-all/dispatch.pid)
    python3 ~/weil-launcher-all/dispatch_all.py --dry                             one pass, prints what it would do, changes nothing

Groups carry no stage. The stage belongs to the item: it is read from the item's project queue (tools/claim.py
queue_stage) and decides the brief, the sandbox, the timeout and the stage rules the worker gets. The order of work is
one queue, written to queue-all.tsv on every pass: batch 1 before batch 2 (config.json), within a batch stage 1, then 2,
then 3, within a stage the project's own order. `total_slots` bounds all workers of all groups together; a group runs
at most `slots_per_group`. Every 15 s: reap ended workers and act on their one-line answer; then hand out free slots in
queue order: open returns and claimed items first, then new claims (tools/claim.py next on the item's project).

Merged on 2026-10-15 from ~/weil-launcher/dispatch.py (stage 3) and ~/weil-launcher-nt/dispatch.py (stages 1 and 2);
every dated rule of both is kept. Review and landing stay with the review loops of each project and stage
(xreview.py, review_stage2.py, review.py), which work on delivery branches, not on groups.
"""
import concurrent.futures, fcntl, json, os, pathlib, re, shlex, shutil, signal, subprocess, sys, time

H = pathlib.Path.home(); A = H / "weil-launcher-all"; RUN = A / "run"
SERVER = "ubuntu@the project server"; KEY = str(H / "weil_formal.pem"); CODEX = str(H / ".local/bin/codex")
CFG = json.loads((A / "config.json").read_text())
TOTAL = int(CFG["total_slots"]); PER_GROUP = int(CFG["slots_per_group"]); CLAIMS = int(CFG["claims_per_group"])
MAXTRY = int(CFG.get("maxtry", 1000)); MAINT_AT = int(CFG.get("maint_at", 5)); MODEL = CFG.get("model", "gpt-6.1-sol")
TIMEOUT = {k: int(v) * 60 for k, v in CFG["timeout_min"].items()}
DRY = "--dry" in sys.argv
SSH = ["ssh", "-i", KEY, "-o", "StrictHostKeyChecking=no", "-o", "ConnectTimeout=20", SERVER]
GIT_ENV = dict(os.environ, GIT_SSH_COMMAND=f"ssh -i {KEY} -o StrictHostKeyChecking=no -o ServerAliveInterval=10")
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)
DEEP = 8
sys.path.insert(0, str(H / "weil-launcher-nt"))
MAINT_PROMPT = """You are the maintenance engineer of the Weil SHEAF pipeline. The item {item} (stage {stage}, project {project},
group {group}) has failed {n} times (dispatcher key {key}). Failures are only counted, never a reason to stop dispatching it,
so a repeated failure means something is wrong with the pipeline (a tool, a permission, a brief, the environment) or with
the data (the node, its module, its records). Find the cause and fix it.

Where to look: the dispatcher state {state} (notes, tries), the worker runs under {runs}/{item}.* (prompt and log of each
attempt), the worker sandbox {sandbox}, the dispatcher log /home/ubuntu/weil-launcher-all/dispatch.log, the batch tools {tools},
and the project on the weil server (ssh -i /home/ubuntu/weil_formal.pem ubuntu@the project server, {project}; coord/returns,
coord/deliveries.log, the landing logs ~/cc1/*.log). Last note of the dispatcher: {note}

Rules: fix the cause where it lies (tool code, brief, record, module), keep a .bak of every file you change, commit on the
server under the merge lock (SHEAF_LEAD=L-only flock coord/.merge.lock git -c user.name="Bin Wu" -c user.email=844524296@qq.com
commit ...), compile Lean files one at a time (tools/lean_file.sh, 60 s), never a lake build, never kill processes you did not
start. Do not do the item's mathematics yourself unless that is the only fix. End with REPORT.md in your working directory:
the cause, what you changed (paths, commits), and what the next worker on the item should know.
"""
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent)); import sharedrepo   # noqa: E402
import stage2_wait                         # noqa: E402  (unstated statement dependencies of a stage-2 item)
import stage1_handoff                      # noqa: E402  (durable stage-1 dry-run handoff)
from codex_capacity import ProviderCapacity, maintenance_pids, provider_failure
from group_state import load_group_state

CAPACITY = None  # initialized in main, after alive() and the saved worker state are available


def is_compile_limit(stage, message):
    """A stage-1 DAG scope failure is never a Lean compiler time limit."""
    if str(stage) not in ("2", "3"):
        return False
    if re.search(r"worktree|slot|lock|ssh|fetch|push|clone|capacity|exit code 143|terminated", message, re.I):
        return False
    limit = re.search(r"60\s*[- ]?\s*(?:s\b|seconds?\b)|time ?limit|timed? ?out|timeout", message, re.I)
    compiler = re.search(r"compil|\blean\b|lean_file|60\s*[- ]?\s*(?:s\b|seconds?\b)", message, re.I)
    return bool(limit and compiler)


def parse_returns(text):
    """Read review (branch head) and batch take-out (head) return headers."""
    returns = {}
    for match in re.finditer(r"^## (\S+) \(([^)]*)\)\n(.*?)(?=^## |\Z)", text, re.M | re.S):
        item, header, body = match.groups()
        head = re.search(r"\b(?:branch\s+)?head\s+([0-9a-f]{7,40})\b", header)
        if head or "." in item or re.match(r"(lem|lemma|def|prop|thm|cor|rem)", item):
            returns[item] = (head.group(1) if head else "", body.strip())
    return returns


def noanswer_detail(last_file):
    """Keep fatal worker diagnostics when Codex exits without writing its answer."""
    try:
        p = pathlib.Path(last_file).with_name("log.txt")
        with p.open("rb") as f:
            f.seek(0, os.SEEK_END)
            f.seek(max(0, f.tell() - 65536))
            tail = f.read().decode(errors="replace")
    except OSError:
        return ""
    errors = [line.strip() for line in tail.splitlines() if re.match(r"^ERROR:", line)]
    return errors[-1] if errors else ""


def worker_codex_command(readc, last, budget, effort, session=None):
    cmd = ["timeout", str(budget + 60), CODEX, "exec"]
    if session:
        cmd.append("resume")
    cmd += ["-c", "model_providers.OpenAI.request_max_retries=30", "-c", "model_providers.OpenAI.stream_max_retries=30",
            "-c", f"model_reasoning_effort={effort}", "-m", MODEL,
            "--dangerously-bypass-approvals-and-sandbox", "--skip-git-repo-check"]
    if not session:
        cmd += ["-C", readc]
    cmd += ["-o", str(last)]
    if session:
        cmd.append(session)
    return cmd + ["-"]


def log(*a):
    with open(A / "dispatch.log", "a") as f:
        f.write(time.strftime("%F %T ") + " ".join(str(x) for x in a) + "\n")


def ssh(cmd, timeout=60):
    if DRY and re.search(r"claim\.py (next|take|release|renew)|attach\.py|nt_stage2\.py", cmd):
        log("DRY would run:", cmd[:200]); return ""
    try:
        return subprocess.run(SSH + [cmd], capture_output=True, text=True, timeout=timeout).stdout
    except Exception as e:
        log("ssh failed:", e); return None


def git(clone, *a, timeout=120):
    stale = pathlib.Path(clone) / ".git" / "index.lock"
    if stale.exists() and time.time() - stale.stat().st_mtime > 180:
        if subprocess.run(["fuser", "-s", str(stale)]).returncode != 0:
            try: stale.unlink()
            except FileNotFoundError: pass
    return subprocess.run(["git", *a], cwd=clone, env=GIT_ENV, capture_output=True, text=True, timeout=timeout)


def stop_worker(pid):
    """Stop a worker this dispatcher started: its whole process group (started with start_new_session), after checking
    that the leader is a `timeout ... codex exec` of one of our clones. Never a pattern kill."""
    try:
        cmdline = pathlib.Path(f"/proc/{pid}/cmdline").read_bytes().replace(b"\0", b" ").decode()
    except OSError:
        return
    if "codex" not in cmdline or not any(b["clone_prefix"] in cmdline for b in CFG["batches"]):
        log("refused to stop", pid, "(not one of our workers):", cmdline[:120]); return
    try: os.killpg(pid, signal.SIGTERM)
    except ProcessLookupError: pass


def alive(pid):
    try:
        os.kill(pid, 0); return not open(f"/proc/{pid}/stat").read().split(") ")[1].startswith("Z")
    except Exception:
        return False


class Batch:
    """One project: its server repository, clones, tools (briefs, delivery and compile tools) and groups."""
    def __init__(s, i, c):
        s.i = i; s.c = c; s.name = c["name"]; s.project = c["project"]; s.main = c["main"]
        s.tools = pathlib.Path(c["tools"]); s.briefs = A / "briefs" / s.name
        s.groups = (A / c["groups_file"]).read_text().split()
        s.skip = {}
        f = s.tools / "skip3.txt"
        for l in f.read_text().split("\n") if f.exists() else []:
            if l.strip() and not l.startswith("#"):
                s.skip[l.split("\t")[0].strip()] = l.split("\t", 1)[1].strip() if "\t" in l else ""
        s.ours = {"sha": None, "set": set()}
        s.queue = []      # [(stage, item)] in the project's order
        s.depth_cache = s.tools / "depth-cache.json"

    def sandbox(s, stage): return pathlib.Path(s.c["sandbox"][stage])

    def env(s, stage):
        e = dict(os.environ, WEIL_LAUNCHER=str(s.tools), WEIL_PROJECT=s.project, WEIL_CLONE_PREFIX=s.c["clone_prefix"],
                 WEIL_MAIN_BRANCH=s.main, WEIL_STAGE=stage, WEIL_SANDBOX=str(s.sandbox(stage)))
        for k, v in s.c["stage_env"].get(stage, {}).items():
            if k.startswith("-"): e.pop(k[1:], None)
            else: e[k] = v
        return e

    def brief(s, stage, kind):
        role = {"check": "check", "attcheck": "attach"}.get(kind, "worker")
        return (s.briefs / f"stage{stage}-{role}.md").read_text()

    def read_queue(s):
        tf = s.c.get("tags_file")
        out = ssh(f"cd {s.project} && cat coord/queue.tsv" + (f"; echo @@@; cat {tf} 2>/dev/null" if tf else ""))
        if out is None: return
        qtext, _, ttext = out.partition("@@@")
        tags = {}
        for l in ttext.splitlines():
            r = l.split("\t")
            if len(r) == 2 and not l.startswith("#"): tags[r[0].strip()] = r[1].strip()
        q = []
        for l in qtext.splitlines():
            r = l.split("\t")
            if l.startswith("#") or len(r) < 2 or r[1] not in ("1", "2", "3"): continue
            q.append((r[1], r[0]))
        s.queue = q; s.tags = tags

    def tag(s, item):   # 2026-10-16: an item the tag file does not list yet is untagged (no lane serves it) until the next tag refresh; it used to default to the project name (batch1)
        return getattr(s, "tags", {}).get(item, "untagged" if s.c.get("tags_file") else s.name)

    def not_ours(s, item, clone, stage):
        """"" when the item is this team's work; the reason when it is the other team's (skip3.txt, or reached by the
        targets only through skip3.txt); None when the clone does not have the module yet. Stage 3 only."""
        if stage != "3" or not s.skip: return ""
        if item in s.skip: return s.skip[item]
        if not s.c.get("skip_closure"): return ""
        def src(m):
            r = subprocess.run(["git", "show", f"origin/{s.main}:lean/" + m.replace(".", "/") + ".lean"], cwd=clone, capture_output=True, text=True)
            return r.stdout if r.returncode == 0 else None
        sha = subprocess.run(["git", "rev-parse", f"origin/{s.main}"], cwd=clone, capture_output=True, text=True).stdout.strip()
        if s.ours["sha"] != sha:
            seen = set(); st = [m for m in IMPORT.findall(src("TargetsCheck") or "") if m not in s.skip]
            while st:
                x = st.pop()
                if x in seen or x in s.skip: continue
                seen.add(x); st += [i for i in IMPORT.findall(src(x) or "") if i.split(".")[0] in ("WeilConjectures", "Sheaf")]
            if not seen: return None
            s.ours.update(sha=sha, set=seen)
        if item in s.ours["set"]: return ""
        if src(item) is None: return None
        return "the targets reach it only through " + ", ".join(sorted(m.split(".")[-1] for m in s.skip)) + " (skip3.txt)"

    def split_depth(s, clone, item, limit=40):
        """How often the obligation of a stage-3 item has been split off (chain of `Prove <parent>` commits, 2026-10-14)."""
        try: cache = json.loads(s.depth_cache.read_text())
        except Exception: cache = {}
        chain, cur, base = [], item, None
        while len(chain) < limit:
            if cur in cache: base = cache[cur]; break
            p = "lean/" + cur.replace(".", "/") + ".lean"
            out = subprocess.run(["git", "log", "--diff-filter=A", "--format=%s", f"origin/{s.main}", "--", p], cwd=clone, capture_output=True, text=True, timeout=120).stdout.strip().splitlines()
            m = re.match(r"Prove (\S+) ", out[-1]) if out else None
            chain.append(cur)
            if not m or m.group(1) == cur or m.group(1) in chain: base = -1; break
            cur = m.group(1)
        base = 0 if base is None else base
        for i, x in enumerate(reversed(chain)): cache[x] = base + 1 + i
        try: s.depth_cache.write_text(json.dumps(cache))
        except Exception: pass
        return cache.get(item, 0)


class Group:
    def __init__(s, g, b):
        s.g = g; s.b = b; s.clone = H / f"{b.c['clone_prefix']}-{g}"; s.dir = RUN / g; s.dir.mkdir(parents=True, exist_ok=True)
        s.sf, s.st = load_group_state(s.dir, b.name, b.c["clone_prefix"])
        for k in ("running", "tries", "notes", "stage"): s.st.setdefault(k, {})
        s.last_refresh = 0; s.srv = None

    def save(s):
        if not DRY: s.sf.write_text(json.dumps(s.st, indent=1))

    def live(s): return sum(1 for v in s.st["running"].values() if alive(v["pid"]))

    def stage(s, item):
        """The item's stage: from its project queue (server), else the stage it was started with, else by its form."""
        return s.st["stage"].get(item) or ("3" if "." in item else "2")

    def timeout(s, item): return TIMEOUT[s.stage(item)]

    def server(s):
        """(held items, delivery branches, open returns) of this group in its project; the stage of each held item is
        recorded from tools/claim.py queue_stage."""
        script = ("import sys; sys.path.insert(0, 'tools'); import claim\n"
                  f"for x in claim.held_by({s.g!r}): print(x, claim.queue_stage(x) or '-', sep='\\t')")
        out = ssh(f"cd {s.b.project} && python3 -c {shlex.quote(script)}; echo @@@; git for-each-ref --format='%(refname:short) %(objectname)' refs/heads/deliver/{s.g}; echo @@@; cat coord/returns/{s.g}.md 2>/dev/null")
        if out is None or out.count("@@@") < 2: return None
        a, b, c = out.split("@@@", 2)
        mine = []
        for l in a.strip().split("\n"):
            if not l.strip(): continue
            item, _, stg = l.partition("\t")
            mine.append(item.strip())
            if stg.strip() in ("1", "2", "3"): s.st["stage"][item.strip()] = stg.strip()
        br = {l.split()[0].split("/", 2)[2]: l.split()[1] for l in b.split("\n") if len(l.split()) == 2}
        ret = parse_returns(c)
        s.srv = (mine, br, ret)
        return s.srv

    def in_work(s):
        """Held items not yet delivered (2026-10-16: a delivery waiting for review does not count toward the claim cap)."""
        br = s.srv[1] if getattr(s, "srv", None) else {}
        return len([x for x in (getattr(s, "mine_all", None) or []) if x not in br])

    def adopt_shared(s):
        """2026-10-16: replace the group's own clone by a symlink to ~/<prefix>-shared once no process works in it."""
        c = s.clone
        if c.is_symlink() or not sharedrepo.shared(s.b.c["clone_prefix"]).is_dir(): return
        if c.exists():
            t = str(c.resolve())
            for proc in pathlib.Path("/proc").iterdir():
                if proc.name.isdigit():
                    try:
                        cwd = os.readlink(proc / "cwd")
                        if cwd == t or cwd.startswith(t + "/"): return
                    except OSError: pass
            old = c.with_name(c.name + ".old-clone"); c.rename(old); shutil.rmtree(old, ignore_errors=True)
        c.symlink_to(sharedrepo.shared(s.b.c["clone_prefix"]))
        log(s.g, "now reads the shared clone", sharedrepo.shared(s.b.c["clone_prefix"]))

    def refresh(s):
        if DRY or time.time() - s.last_refresh < 45: return
        if s.clone.is_symlink(): s.last_refresh = time.time(); return   # 2026-10-16: the shared clone is refreshed by refresh_shared.sh
        try:
            with open(s.clone / ".git" / "deliver.lock", "w") as lk:
                fcntl.flock(lk, fcntl.LOCK_EX | fcntl.LOCK_NB)
                git(s.clone, "fetch", "-q", "origin"); git(s.clone, "checkout", "-q", "-f", s.b.main); git(s.clone, "reset", "-q", "--hard", "origin/" + s.b.main)
                s.last_refresh = time.time()
        except BlockingIOError: pass
        except Exception as e: log(s.g, "refresh failed:", e)

    def release(s, item, reason):
        r = ssh(f"cd {s.b.project} && python3 tools/claim.py release {s.g} {shlex.quote(item)} {shlex.quote(reason[:300])}")
        log(s.g, "release", item, "|", reason[:120], "->", (r or "").strip()[:80])

    def park(s, item, why, delivered):
        """Not this team's part: stop its worker, pass the claim to ORCHESTRA (kept by the group, unworked, if it cannot take it)."""
        w = s.st["running"].pop(item, None)
        if w and alive(w["pid"]) and not DRY:
            try: stop_worker(w["pid"])
            except Exception: pass
        q = shlex.quote; note = ("abandon: " if delivered else "") + "not this team's part: " + why
        r = ssh(f"cd {s.b.project} && python3 tools/claim.py release {s.g} {q(item)} {q(note[:300])} >/dev/null; python3 tools/claim.py take ORCHESTRA {q(item)} >/dev/null; "
                f"if python3 tools/claim.py mine ORCHESTRA | grep -qFx {q(item)}; then echo HELD; else python3 tools/claim.py take {s.g} {q(item)} >/dev/null; echo KEPT; fi") or ""
        if "HELD" not in r: s.st.setdefault("kept", []).append(item)
        s.save(); log(s.g, "parked", item, "|", "HELD" if "HELD" in r else "KEPT, not worked", "|", why[:200])

    def maint(s, item, key):
        """The human, 2026-10-16: failure counts are only counted, never block. When an item's count reaches 5, 10, 20, 40, ...
        a maintenance Codex looks for the cause (tool, permission, brief or data) and fixes it; one per item at a time."""
        n = s.st["tries"].get(key, 0)
        if n < MAINT_AT: return
        level = MAINT_AT
        while level * 2 <= n: level *= 2
        done = s.st.setdefault("maint", {})
        if done.get(key, 0) >= level: return
        d = A / "maint" / f"{s.g}-{item}-{int(time.time())}"
        for old in (A / "maint").glob(f"{s.g}-{item}-*"):
            try:
                if alive(int((old / "pid").read_text())): return
            except Exception: pass
        admission = CAPACITY.acquire(maintenance=True) if not DRY else None
        if not DRY and not admission: return
        if DRY: log("DRY would start maintenance", s.g, item); return
        with admission:
            s.start_maintenance(item, key, n, level, d, admission)

    def start_maintenance(s, item, key, n, level, d, admission):
        d.mkdir(parents=True, exist_ok=True)
        prompt = MAINT_PROMPT.format(item=item, group=s.g, n=n, key=key, stage=s.stage(item), project=s.b.project,
                                     tools=s.b.tools, state=s.sf, runs=s.dir, sandbox=s.b.sandbox(s.stage(item)) / s.g / item,
                                     note=str(s.st["notes"].get(item, ""))[:1500])
        (d / "prompt.txt").write_text(prompt)
        with open(d / "prompt.txt") as fin, open(d / "log.txt", "w") as fout:
            p = subprocess.Popen(["timeout", "5400", CODEX, "exec", "-m", MODEL, "-c", "model_reasoning_effort=xhigh",
                                  "--dangerously-bypass-approvals-and-sandbox", "--skip-git-repo-check", "-C", str(d), "-"],
                                 stdin=fin, stdout=fout, stderr=subprocess.STDOUT, start_new_session=True)
        admission.started(p.pid)
        (d / "pid").write_text(str(p.pid)); s.st.setdefault("maint", {})[key] = level; s.save()
        log(s.g, "MAINTENANCE started for", item, f"({n} failures)", "pid", p.pid, "dir", d)

    def wait_for(s, item, dependencies, reason):
        """Stage 2: park the item until its unstated statement dependencies land; claim those that are ready first."""
        return False   # the human, 2026-10-16: no dispatch restrictions; the worker states missing dependencies itself
        out = ssh(f"cd {s.b.project} && python3 tools/nt_stage2.py " + " ".join(shlex.quote(x) for x in [item, *dependencies]), timeout=180)
        try: result = json.loads((out or "").splitlines()[-1])
        except (ValueError, IndexError):
            log(s.g, "dependency wait registration failed", item, (out or "")[-200:]); return False
        if result.get("cycle"):
            cycle = " -> ".join(result["cycle"])
            s.st["notes"][item] = f"WAITING was rejected because it creates a dependency cycle: {cycle}. Repair the already recorded dependency interface under §1(B) and supply the canonical helper in its owning module. A definition must not wait on a downstream theorem about its own map. Do not answer WAITING for this cycle again."
            s.save(); log(s.g, "DEPENDENCY CYCLE", item, cycle); return True
        if not result["missing"]: return False
        s.st.setdefault("waiting", {})[item] = {"dependencies": result["missing"], "reason": reason, "since": time.time()}
        s.st.get("blocked", {}).pop(item, None); s.st["notes"].pop(item, None)
        s.save(); log(s.g, "WAITING", item, "for", ", ".join(result["missing"]))
        for dep in result["ready"]:
            if s.live() >= PER_GROUP: break
            ssh(f"cd {s.b.project} && python3 tools/claim.py take {s.g} {shlex.quote(dep)}")
        return True

    def reap(s):
        for item, w in list(s.st["running"].items()):
            stage = s.stage(item)
            if alive(w["pid"]):
                if time.time() - w["t"] > w.get("budget", s.timeout(item)) and not DRY:   # 2026-10-15: the worker's own budget
                    try: stop_worker(w["pid"])
                    except Exception: pass
                    log(s.g, "timeout, stopped", item)
                    if stage == "3":
                        s.st["notes"][item] = ("TIMEOUT: the previous worker used its whole budget without delivering; its work is in your sandbox. "
                            "Do not start over. First run the dry run on the sandbox as it is; within 40 minutes make it pass (state what is still open as "
                            "split-off theorems with full proofs in words) and deliver. A delivery with split-offs is far better than a third lost session.")
                        s.st.setdefault("timedout", {})[item] = time.time()
                    s.save()
                continue
            if DRY: continue
            lm = pathlib.Path(w["last"]); txt = lm.read_text().strip() if lm.exists() else ""
            m = re.search(r"\b(DELIVERED|READY|ATTACH|CONFIRM|REJECT|ABANDON|BLOCKED|WAITING)\b(.*)", txt, re.S)
            kind = m.group(1) if m else "NOANSWER"; rest = (m.group(2) if m else txt).strip().replace("\n", " ")[:260]
            if kind == "NOANSWER":
                receipt = stage1_handoff.ready_receipt(s.b.sandbox(stage) / s.g / item, s.g, item, w)
                if receipt:
                    kind, rest = "READY", f"{item}: recovered server preflight at {receipt['head']}; independent second reading required"
            if kind == "NOANSWER":
                failure = provider_failure(lm.with_name("log.txt"))
                if failure:
                    kind, rest = "PROVIDER_RATE_LIMIT", failure
                    CAPACITY.rate_limited()
            elif kind in ("DELIVERED", "READY", "ATTACH", "CONFIRM", "REJECT", "ABANDON", "BLOCKED", "WAITING"):
                CAPACITY.success()
            if kind == "NOANSWER" and not rest:
                rest = noanswer_detail(lm)[:260]
            log(s.g, "worker ended", item, f"(stage {stage}, {w['kind']}, {int((time.time()-w['t'])/60)} min):", kind, rest[:160])
            del s.st["running"][item]
            sb = s.b.sandbox(stage) / s.g / item
            dependencies = stage2_wait.blockers(s.clone, item, txt) if stage == "2" and kind in ("BLOCKED", "WAITING") else []
            if dependencies and s.wait_for(item, dependencies, txt):
                pass
            elif kind == "ATTACH" and w["kind"] != "attcheck" and stage == "1":
                # a second worker tests the claim; if it confirms, the server's tools/attach.py checks sorry-freeness and records it
                with open(s.b.sandbox(stage) / s.g / "ATTACH.md", "a") as f: f.write(f"- {time.strftime('%F %T')} {item}: {rest}\n")
                s.start(item, "attcheck", w["key"], claimed=rest)
            elif kind == "CONFIRM" and w["kind"] == "attcheck":
                body = rest.split(":", 1)[1] if ":" in rest.split("|")[0] else rest
                names, _, why = body.partition("|")
                decls = [x for x in re.split(r"[,\s]+", names.strip()) if re.fullmatch(r"[A-Za-z_][\w'.!?]*", x) and not x.endswith(".lean")]
                out = ssh(f"cd {s.b.project} && python3 tools/attach.py {s.g} {shlex.quote(item)} {' '.join(shlex.quote(x) for x in decls)} --note {shlex.quote(why.strip()[:400])}", timeout=120) if decls else "REFUSED: no declaration name in the confirmation"
                out = (out or "no answer from the server").strip().replace("\n", " ")
                log(s.g, "attach", item, "->", out[:200])
                if out.startswith("ATTACHED"): shutil.rmtree(sb, ignore_errors=True)
                else:
                    s.st["tries"][w["key"]] = s.st["tries"].get(w["key"], 0) + 1
                    s.st["notes"][item] = f"A Lean attachment was proposed for this item ({names.strip()[:200]}) and the server refused it: {out[:300]}. Do not answer ATTACH again: split the item (you may cite what the Lean proves only through DAG nodes)."
            elif kind == "REJECT" and w["kind"] == "attcheck":
                s.st["tries"][w["key"]] = s.st["tries"].get(w["key"], 0) + 1
                s.st["notes"][item] = f"A Lean attachment was proposed for this item and a second worker rejected it: {rest[:300]}. Do not answer ATTACH again: if it says 'Mathlib leaf', make the item a Mathlib leaf and deliver it; otherwise split the item."
            elif kind == "ABANDON" and stage == "3" and time.time() - w["t"] < s.timeout(item) / 2:
                s.st["tries"][w["key"]] = s.st["tries"].get(w["key"], 0) + 1
                s.st["notes"][item] = f"ABANDON after {int((time.time()-w['t'])/60)} of {s.timeout(item)//60} minutes, which is not accepted: {rest} -- Finding no short proof is not a reason. Do what the brief asks at the least: make the node's plan into Lean (your statement proved from the stated declarations of the nodes the steps use, their modules imported, `sorry` there is intended), and state as intermediate theorems the steps you cannot close."
            elif kind == "ABANDON":
                s.st.get("handoff", {}).pop(item, None)
                s.release(item, "abandon: " + rest)
                if sb.exists():
                    archive = A / "abandoned" / s.g / (item + "." + str(int(time.time())))
                    archive.parent.mkdir(parents=True, exist_ok=True); shutil.move(str(sb), str(archive))
            elif kind == "DELIVERED":
                s.st.get("handoff", {}).pop(item, None)
                for k in ("blocked", "retry_after"): s.st.get(k, {}).pop(item, None)
                s.st["notes"].pop(item, None)
            elif kind == "READY":
                s.st.setdefault("handoff", {})[item] = {"stage": stage, "key": w["key"]}
                s.save()
                s.start(item, "check", w["key"])
            elif kind == "PROVIDER_RATE_LIMIT":
                s.st["tries"][w["key"]] = s.st["tries"].get(w["key"], 0) + 1
                s.st["notes"][item] = ("PROVIDER_RATE_LIMIT: " + rest +
                    ". The provider rejected the session; resume the preserved sandbox. "
                    "This is an infrastructure failure, not a mathematical verdict.")
            elif kind == "BLOCKED" and is_compile_limit(stage, rest):
                # Only compiler diagnostics from a Lean stage imply a definition repair.
                s.st["tries"][w["key"]] = s.st["tries"].get(w["key"], 0) + 1
                s.st["notes"][item] = ("NOT a tool failure: the previous worker stopped at the 60-second compile limit (" + rest[:300] +
                    "). The cause is a definition the file uses: find it, change it (or make it @[no_expose] with characterizing lemmas), "
                    "adapt its users in the same delivery, and deliver. Do not answer BLOCKED for this.")
            elif kind == "BLOCKED" and s.st.setdefault("blocked", {}).get(item, 0) < 5:
                s.st["blocked"][item] = s.st["blocked"].get(item, 0) + 1
                s.st["notes"][item] = f"BLOCKED (a tool failure, try {s.st['blocked'][item]} of 5; the work in the sandbox is kept): {rest}"
            else:
                s.st["tries"][w["key"]] = s.st["tries"].get(w["key"], 0) + 1
                if not (kind == "NOANSWER" and str(s.st["notes"].get(item, "")).startswith("TIMEOUT")):
                    s.st["notes"][item] = f"{kind}: {rest}"
            s.save()

    def sandbox_from_branch(s, item, stage):
        sb = s.b.sandbox(stage) / s.g / item
        # A retry resumes local work. Reloading the rejected branch here erased
        # repaired Lean, nodes and reports on every stage-2/3 repair restart.
        if any(sb.glob("dag/nodes/*/*.json")) or any(sb.glob("lean/**/*.lean")):
            log(s.g, "preserving repair sandbox", item, "(resume and rebase existing work)")
            return
        # 2026-10-16: fetched into a ref of its own in the shared clone (serialised), never FETCH_HEAD
        ref = f"refs/launcher/{s.g}/{item}"
        r = sharedrepo.fetch(s.b.c["clone_prefix"], f"+refs/heads/deliver/{s.g}/{item}:{ref}")
        if r.returncode: return
        for f in git(s.clone, "diff", "--name-only", f"origin/{s.b.main}...{ref}").stdout.split():
            body = git(s.clone, "show", f"{ref}:{f}").stdout
            if f.startswith("dag/nodes/") or f.startswith("lean/") or f.startswith("coord/changes/"): d = sb / f
            elif f.startswith(f"coord/reports/{s.g}/"): d = sb / "report.md"
            else: continue
            d.parent.mkdir(parents=True, exist_ok=True); d.write_text(body)

    def start(s, item, kind, key, extra="", claimed=""):
        stage = s.stage(item)
        if DRY:
            log("DRY would start", s.g, f"stage {stage}", kind, item); return True
        admission = CAPACITY.acquire()
        if not admission:
            s.st.setdefault("pending", {})[item] = dict(kind=kind, key=key, extra=extra, claimed=claimed)
            s.save()
            return False
        with admission:
            return s.start_admitted(item, kind, key, extra, claimed, admission)

    def start_admitted(s, item, kind, key, extra, claimed, admission):
        stage = s.stage(item)
        recovery = s.st.get("resume", {}).pop(item, None)
        session = recovery["session"] if recovery and all(
            recovery.get(k) == v for k, v in (("key", key), ("kind", kind), ("stage", stage))) else None
        sb = s.b.sandbox(stage) / s.g / item; sb.mkdir(parents=True, exist_ok=True)
        if kind == "repair": s.sandbox_from_branch(item, stage)
        for name, text in (('.brief2', 'started with the brief that requires citations.json\n'), ('.brief3', 'started with the brief that requires searches made with msearch.py\n'),
                           ('.brief4', 'started with the brief that has the duplicate check\n'), ('.brief5', 'split by a worker that hands over to a second reader\n')):
            (sb / name).write_text(text)
        handoff = s.st.setdefault("handoff", {})
        round_id = {"stage": stage, "key": key}
        resuming_check = kind == "check" and handoff.get(item) == round_id and (sb / '.check').exists()
        if kind == "check":
            handoff[item] = round_id
            (sb / '.check').write_text('second reader started\n')
            rp = sb / "report.md"   # the second reader writes its own section; an older one does not count
            if not resuming_check and rp.exists() and f"## Second reading by {s.g}" in rp.read_text():
                rp.write_text(rp.read_text().replace(f"## Second reading by {s.g}", "## Earlier second reading (a previous round; superseded)"))
        else:
            handoff.pop(item, None)
            if (sb / '.check').exists(): (sb / '.check').unlink()
        if resuming_check:
            extra += ("\n\nResume the interrupted second reading in the retained sandbox. "
                      "Keep its review section, recheck any changed files, finish validation and deliver.\n")
        budget = s.timeout(item); effort = "high"
        brief = s.b.brief(stage, kind)
        sh_ = sharedrepo.shared(s.b.c["clone_prefix"]); readc = str(sh_ if sh_.is_dir() else s.clone)   # 2026-10-16: workers read the shared clone
        for a, b in ((f"/home/ubuntu/{s.b.c["clone_prefix"]}-GROUP", readc), ("/home/ubuntu/weil-newtargets-stage2-sandbox", str(s.b.sandbox(stage)))):
            brief = brief.replace(a, b)
        brief = brief.replace("GROUP", s.g).replace("ITEM", item).replace("CLAIMED", claimed).replace("BUDGET", str(budget // 60))
        brief += "\n\nYou were started by a dispatcher script, not by a lead: there is nobody to ask. Do not start other agents. Your last message must be exactly one of the answers above, on one line, beginning with the word.\n" + extra
        rn = s.b.tools / "route-notes" / f"{item}.md"     # 2026-10-14: a route-finder's study of the item's split chain
        if kind != "check" and rn.exists():
            brief += "\n\n## Route note for this item (a strong reader studied its whole split chain; follow it unless you find it wrong)\n\n" + rn.read_text()[:12000]
        if session:
            brief += ("\n\nThis resumes the exact session interrupted by Codex HTTP 429, not a mathematical failure. "
                      "Retain your prior reading and sandbox work. Check any delivery process you already started "
                      "before launching another. Continue from your last unfinished step.\n")
        if stage == "2" and kind != "check" and any(sb.glob("lean/**/*.lean")) and any(sb.glob("dag/nodes/*/*.json")):
            brief += ("\n\nA previous attempt left a stage-2 packet. First inspect report.md and run deliver2.py "
                      "for this group/item with --no-push on that saved packet. If it passes, retain the work, "
                      "finish only the required self-check, and answer READY for the separate second reader. "
                      "Use a failed dry run's concrete diagnostic to choose the repair; do not restart the whole investigation.\n")
        if stage == "3" and kind != "check":
            try: depth = s.b.split_depth(s.clone, item)
            except Exception: depth = 0
            if depth >= DEEP: budget = int(budget * 1.5); effort = "xhigh"
            (sb / ".budget").write_text(json.dumps({"start": time.time(), "budget": budget, "repair": kind == "repair", "depth": depth}))
            brief = brief.replace(f"{s.timeout(item) // 60} minutes", f"{budget // 60} minutes") + (
                f"\n\n## Keep going after a split (launcher, 2026-10-14)\n\nThis obligation has already been split off {depth} times, each time by a different group "
                "that started from nothing. Do not hand it on again early: a theorem you split off is in YOUR sandbox, so prove it yourself in this session, "
                "and its split-offs in turn, from Mathlib, the library and intermediate theorems of your own. The dry run refuses a delivery that adds `sorry` "
                "before 60 % of your budget is used. Deliver with split-offs only near the end, and then name in report.md what each one still needs.\n"
                + f"\nHard stop: you are killed {budget // 60} minutes after the start ({time.strftime('%H:%M', time.localtime(time.time() + budget))} on this machine; `date` tells the time), and work not delivered by then is lost. At minute {int(budget * 0.85) // 60} at the latest, stop proving: make the sandbox pass the dry run as it stands (split off what is still open) and answer.\n"
                + ("\nThis chain is deep: before writing more glue, ask whether the route itself is wrong (a Mathlib theorem, a different argument, a "
                   "statement that is false or more general than needed). A shorter route that closes the whole chain is the best possible delivery.\n" if depth >= DEEP else ""))
        if stage == "2":
            assigned = s.st.setdefault("assigned", [])
            if item not in assigned: assigned.append(item)
        wd = s.dir / f"{item}.{int(time.time())}"; wd.mkdir(parents=True, exist_ok=True); (wd / "prompt.txt").write_text(brief)
        cmd = worker_codex_command(readc, wd / "last.txt", budget, effort, session)
        p = subprocess.Popen(cmd, stdin=open(wd / "prompt.txt"), stdout=open(wd / "log.txt", "w"), stderr=subprocess.STDOUT,
                             cwd=readc, start_new_session=True, env=s.b.env(stage))
        admission.started(p.pid)
        s.st.setdefault("pending", {}).pop(item, None)
        s.st["running"][item] = {"pid": p.pid, "t": time.time(), "kind": kind, "key": key, "last": str(wd / "last.txt"), "budget": budget, "stage": stage}
        s.st["stage"][item] = stage
        s.save(); log(s.g, "started", f"stage {stage}", kind, item, "pid", p.pid)
        return True

    def work(s):
        """This group's own candidate work on items it already holds: [(stage, item, kind, key, extra)]."""
        # Only reap removes ended records; a reader can exit without last.txt
        # between reap and work, and still needs its answer/role accounted for.
        sv = s.server()
        if sv is None: return []
        mine, br, ret = sv; run = s.st["running"]; tries = s.st["tries"]
        gone = s.st.setdefault("gone", {})
        for item in list(gone):
            if item in mine or item not in run: gone.pop(item, None)
        for item, w in list(run.items()):      # a worker whose item the group no longer holds (landed, parked or released)
            # 2026-10-16: one server read can miss a claim (a lock file being rewritten); stop only after 150 s of absence
            if item not in mine and time.time() - gone.setdefault(item, time.time()) < 150: continue
            if item not in mine and time.time() - w["t"] > 90 and alive(w["pid"]) and not DRY:
                try: stop_worker(w["pid"])
                except Exception: pass
                del run[item]; s.save(); log(s.g, "stopped the", w["kind"], "worker of", item, "(the group no longer holds the item)")
        gave = s.st.setdefault("gaveup", [])
        mine_all = mine; mine = [x for x in mine if x not in s.b.skip]   # 2026-10-16: no give-up list
        s.mine_all = mine_all
        s.adopt_shared(); s.refresh()
        for item, wait in list(s.st.get("waiting", {}).items()):          # stage 2: parked on unstated dependencies
            if item not in mine_all:
                del s.st["waiting"][item]; s.save(); continue
            if any(stage2_wait.unstated(s.clone, d) for d in wait["dependencies"]): continue
            out = ssh(f"cd {s.b.project} && python3 tools/nt_stage2.py " + " ".join(shlex.quote(x) for x in [item, *wait["dependencies"]]), timeout=180)
            try: resolved = not json.loads((out or "").splitlines()[-1])["missing"]
            except (ValueError, IndexError): resolved = False
            if resolved:
                del s.st["waiting"][item]; s.st["notes"].pop(item, None); s.st.get("retry_after", {}).pop(item, None)
                s.save(); log(s.g, "RESUMED", item, "dependencies landed")
        s.st["waiting"] = {}; s.st["retry_after"] = {}   # 2026-10-16: no waits and no back-off
        for x in list(mine):                                                 # the other team's part: parked, never worked
            if x in s.st.get("kept", []): mine.remove(x); continue
            why = s.b.not_ours(x, s.clone, s.stage(x))
            if why is None:
                mine.remove(x)
                if s.stage(x) == "3":
                    miss = s.st.setdefault("missing", {}); miss.setdefault(x, time.time())
                    if time.time() - miss[x] > 1200 and x not in ret:      # 2026-10-14: taken out with its batch
                        del miss[x]; s.save(); s.release(x, "the module is not on the main branch (taken out with its batch); released by the dispatcher")
            elif why: mine.remove(x); s.park(x, why, x in br or x in ret)
        todo = []
        pending = s.st.setdefault("pending", {})
        for item, request in list(pending.items()):
            if item not in mine:
                del pending[item]
            elif item not in run:
                # Keep the exact second-reader/attachment transition across
                # capacity waits and dispatcher restarts. No worker budget has
                # begun while the request is queued.
                todo.append((s.stage(item), item, request["kind"], request["key"], request["extra"]))
        for item, (h, text) in ret.items():                                 # open returns first
            if item in run or item in pending or item not in mine: continue
            if item in br and h and not br[item].startswith(h[:7]): continue   # re-pushed, waiting for review
            key = f"{item}@{h[:9]}"
            s.maint(item, key)
            repair_checks = "dry-run" if s.stage(item) == "1" else "compile, dry-run"
            note = ("\n\n## This is a REPAIR of a returned delivery\n\nYour sandbox holds the delivered version (node files and report.md). The maintainer returned it with the entry below. Repair every numbered point exactly as it asks, in the sandbox, then " + repair_checks + " and answer as the brief says. A rebase or an unchanged re-push is not a repair. If a point cannot be repaired, answer ABANDON with the reason.\n\n" + text[:6000])
            if item in s.st["notes"]:
                note += f"\n\nThe previous worker on this item ended with: {s.st['notes'][item]}\n"
            note += ("\n\nExisting sandbox work is retained across repair retries. Compare it with "
                     "the returned head and current main branch; continue and rebase that work.\n")
            handoff = s.st.get("handoff", {}).get(item, {})
            kind = "check" if handoff == {"stage": s.stage(item), "key": key} else "repair"
            todo.append((s.stage(item), item, kind, key, note))
        for item in mine:                                                    # claimed, never delivered
            if item in run or item in pending or item in br or item in ret: continue
            stage = s.stage(item)
            # The server queue is bottom-up, but held claims may predate a repaired
            # stmt_deps edge. Recheck those edges before relaunching (N1 maintenance).
            # Failure counts and proof-only prerequisites never gate this work.
            if stage == "2" and stage2_wait.blockers(s.clone, item):
                continue
            if stage == "3":   # 2026-10-14: an item finished meanwhile (no sorry left) and not a listed repair is given back
                fp = s.clone / "lean" / (item.replace(".", "/") + ".lean")
                try:
                    done_now = fp.is_file() and "sorry" not in re.sub(r"--[^\n]*|/-.*?-/", "", fp.read_text(), flags=re.S)
                    listed = any(l.split()[:1] == [item] for l in (s.clone / "coord" / "repairs.txt").read_text().splitlines())
                except Exception:
                    done_now, listed = False, True
                if done_now and not listed and any(item in str(t) for _, t in ret.values()): continue
                if done_now and not listed: s.release(item, "finished meanwhile: the module has no sorry on the main branch (dispatcher)"); continue
                if not fp.is_file() and not listed:
                    miss = s.st.setdefault("missing", {}); miss.setdefault(item, time.time()); s.save()
                    if time.time() - miss[item] > 1200: del miss[item]; s.save(); s.release(item, "the module is not on the main branch (taken out with its batch); released by the dispatcher")
                    continue
            key = f"{item}@new"
            s.maint(item, key)
            extra = ""
            sb = s.b.sandbox(stage) / s.g / item
            if list(sb.glob("dag/nodes/*/*.json")) or list(sb.glob("lean/**/*.lean")): extra = "\n\nYour sandbox holds work from an earlier attempt. Retain it, check it against current sources, and start with the required dry run when the item and report are present. Repair its diagnostics, then finish with the answer required by your role's brief.\n"
            if item in s.st["notes"]: extra += f"\nThe previous worker on this item ended with: {s.st['notes'][item]}\n"
            if stage == "3":
                try: rl = [l for l in (s.clone / "coord" / "repairs.txt").read_text().splitlines() if l.split()[:1] == [item]]
                except Exception: rl = []
                if rl:
                    extra += ("\n\n## This item is a REPAIR listed in coord/repairs.txt\n\n" + "\n".join(rl) +
                              "\n\nThe module may contain no `sorry`: the task is this repair (a false or weakened statement to correct, a duplicate to remove "
                              "with its callers re-pointed to the existing declaration, or undetermined data to make concrete). Deliver the repaired module(s) "
                              "as usual; a corrected statement is a statement change and follows the rules for those.\n")
            handoff = s.st.get("handoff", {}).get(item, {})
            kind = "check" if handoff == {"stage": stage, "key": key} else "new"
            todo.append((stage, item, kind, key, extra))
        for d in (s.b.sandbox("2") / s.g, s.b.sandbox("1") / s.g, s.b.sandbox("3") / s.g):   # sandboxes of items no longer ours
            if d.exists() and not DRY:
                for x in d.iterdir():
                    if x.is_dir() and x.name not in mine_all and x.name not in run and time.time() - x.stat().st_mtime > 1800: shutil.rmtree(x, ignore_errors=True)
        return todo


def lanes(batches):
    """[(batch, tag)] in dispatch order (config `lanes`, else one lane per batch with its own name as tag)."""
    by = {b.name: b for b in batches}
    if "lanes" in CFG: return [(by[l["batch"]], l.get("tag")) for l in CFG["lanes"]]
    return [(b, None) for b in batches]


def lane_index(batches, b, item):
    for i, (lb, tag) in enumerate(lanes(batches)):
        if lb is b and (tag is None or b.tag(item) == tag): return i
    return len(CFG.get("lanes", [])) + b.i


def write_queue(batches, groups):
    """queue-all.tsv: the one dispatch order, with each item's state."""
    held = {}; deliv = {}
    for g in groups:
        if g.srv:
            for x in g.srv[0]: held[(g.b.name, x)] = g.g
            for x in g.srv[1]: deliv[(g.b.name, x)] = g.g
    rows = ["# lane\tstage\titem\tproject\tstate (written by dispatch_all.py; order = dispatch order)"]
    for b, tag in lanes(batches):
        for stg in ("1", "2", "3"):
            for st, item in b.queue:
                if st != stg or (tag is not None and b.tag(item) != tag): continue
                state = ("delivered by " + deliv[(b.name, item)]) if (b.name, item) in deliv else ("held by " + held[(b.name, item)]) if (b.name, item) in held else "open"
                rows.append(f"{tag or b.name}\t{stg}\t{item}\t{b.project}\t{state}")
    if not DRY: (A / "queue-all.tsv").write_text("\n".join(rows) + "\n")
    return rows


def main():
    global CAPACITY
    lock = open(A / "dispatch.lock", "a")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    batches = [Batch(i, c) for i, c in enumerate(CFG["batches"])]
    groups = [Group(g, b) for b in batches for g in b.groups]
    CAPACITY = ProviderCapacity(TOTAL, alive, initial=int(CFG.get("provider_start_slots", 16)),
                                cooldown=int(CFG.get("provider_cooldown_s", 60)))
    CAPACITY.adopt(w["pid"] for g in groups for w in g.st["running"].values())
    CAPACITY.adopt(maintenance_pids(A / "maint"), maintenance=True)
    if not DRY: (A / "dispatch.pid").write_text(str(os.getpid()))
    log("dispatcher started", "dry" if DRY else "", "| total slots", TOTAL, "per group", PER_GROUP, "claims", CLAIMS, "|",
        ", ".join(f"{b.name}: {len(b.groups)} groups" for b in batches))
    pool = concurrent.futures.ThreadPoolExecutor(max_workers=16)
    while True:
        t0 = time.time()
        for b in batches: b.read_queue()
        list(pool.map(lambda g: g.reap(), groups))
        def own(g):
            try: return g, g.work()
            except Exception as e: log(g.g, "error:", repr(e)[:300]); return g, []
        cand = list(pool.map(own, groups))
        live = sum(g.live() for g in groups)
        free = min(TOTAL - live, CAPACITY.available())
        # 1. work on items already held, in dispatch order (batch, then stage)
        pending = sorted(((lane_index(batches, g.b, item), int(stg), g, item, kind, key, extra) for g, todo in cand for stg, item, kind, key, extra in todo), key=lambda r: (r[0], r[1]))
        started = 0
        for bi, stg, g, item, kind, key, extra in pending:
            if free <= 0: break
            if g.live() >= PER_GROUP or item in g.st["running"]: continue
            request = g.st.get("pending", {}).get(item, {})
            if g.start(item, kind, key, extra, claimed=request.get("claimed", "")):
                free -= 1; started += 1
        # 2. new claims, lane by lane (batch, tag), stage 1 then 2 then 3
        claimed = 0
        taken = {(g.b.name, x) for g in groups if g.srv for x in list(g.srv[0]) + list(g.srv[1])}
        for b, tag in lanes(batches):
            for stg in ("1", "2", "3"):
                if free <= 0: break
                open_items = [it for st, it in b.queue if st == stg and (tag is None or b.tag(it) == tag)]
                if not open_items: continue
                if tag is not None:      # exact items, in queue order (2026-10-15: batch 1 before batch 2 in the same project)
                    for it in open_items:
                        if free <= 0 or (b.name, it) in taken: continue
                        gs = [g for g in groups if g.b is b and getattr(g, "mine_all", None) is not None and g.live() < PER_GROUP and g.in_work() < CLAIMS]
                        if not gs:
                            log("lane", b.name, tag, "stage", stg, ": no group can claim (all at their claim or slot cap)"); break
                        g = min(gs, key=lambda g: (g.live(), g.in_work()))
                        out = ssh(f"cd {b.project} && python3 tools/claim.py take {g.g} {shlex.quote(it)}") or ""
                        # 2026-10-16: take prints the item on success (the old test missed it, so nothing was started)
                        ok = DRY or out.strip().splitlines()[-1:] == [it]   # take prints exactly the item on success; refusals start with it too
                        if not ok: log(g.g, "take", it, "refused:", out.strip()[-120:])
                        if ok:
                            sv = g.server()
                            if sv and it in sv[0]:
                                g.st["stage"][it] = stg; g.mine_all = sv[0]; taken.add((b.name, it))
                                if g.start(it, "new", f"{it}@new"):
                                    free -= 1; claimed += 1
                    continue
                for g in sorted((g for g in groups if g.b is b), key=lambda g: g.live()):
                    if free <= 0: break
                    held = getattr(g, "mine_all", None)
                    if held is None or g.live() >= PER_GROUP or g.in_work() >= CLAIMS: continue
                    want = min(PER_GROUP - g.live(), CLAIMS - g.in_work(), free)
                    out = ssh(f"cd {b.project} && python3 tools/claim.py next {g.g} --stage {stg} --count {want}") or ""
                    if "nothing to claim" in out: break       # this stage of this batch is exhausted for now
                    sv = g.server()
                    if not sv: continue
                    new = [x for x in sv[0] if x not in held and x not in b.skip]   # 2026-10-16: no give-up list
                    for item in new[:free]:
                        g.st["stage"][item] = g.st["stage"].get(item) or stg
                        why = b.not_ours(item, g.clone, g.stage(item))
                        if why is None: continue
                        if why: g.park(item, why, False)
                        elif g.start(item, "new", f"{item}@new"):
                            free -= 1; claimed += 1
                    g.mine_all = sv[0]
        write_queue(batches, groups)
        log("pass", f"{time.time() - t0:.0f}s", "| live", live, "+", started + claimed, "started (", started, "held,", claimed, "new ) | free", free)
        if DRY: return
        time.sleep(15)


if __name__ == "__main__":
    main()
