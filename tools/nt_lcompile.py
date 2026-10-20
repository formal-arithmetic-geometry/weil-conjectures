#!/usr/bin/env python3
"""Side-project copy (2026-10-17, stage-2 compiles moved to the server) of ~/weil-review-svc/lcompile.py, the server port
of the Codex machine's ~/weil-launcher/lcompile.py: compiles against the live published build
~/weil-conjectures-sheaf/lean/.lake/build (read only), at nice 19, at most NT_LCOMPILE_SLOTS (24) at once (own slot
files in ~/weil-nt-overlay/slots), never remote. Otherwise identical. Used by tools/nt_srv_compile.py.

    lcompile.py <file.lean>                    one file
    lcompile.py <a.lean> <b.lean> [...]        several files of one sandbox that import one another (a new module and the
                                               module that imports it): compiled in import order, each written as a compiled
                                               module to <sandbox>/.lbuild, where the later ones find it
    lcompile.py --all <sandbox directory>      every .lean file under <sandbox>/lean, the same way

A file that lies under a directory named lean/ (…/lean/Sheaf/Foo/Bar.lean) is compiled as the module Sheaf.Foo.Bar. A single
file also sees the modules already compiled into its sandbox's .lbuild (the output says so; compile the set again after
changing one of them). The .lbuild directory contains only sandbox outputs; Lean --setup resolves those modules
explicitly, and LEAN_PATH resolves the shared library and packages without a link farm. Every file is a file of Lean's module system (`module`, `public import`, `@[expose] public section`).

Prints the compiler's messages: errors, warnings, and the goals at an unfinished proof ("unsolved goals"; a `sorry` left
shows as "declaration uses sorry" only with -Dwarn.sorry=true, which this command does not set: grep your file). Seconds per
file. The server compile (scompile.py, and the one inside deliver3.py) stays the final check: a module landed in the last two
minutes may not be here yet. The options are those of lean/lakefile.toml; `autoImplicit = false` is added for every file that
is not of the source library (a path with /WeilConjectures/ or /Comparator/, or a file name starting with WeilConjectures_),
as the server's tools/lean_file.sh does."""
import json, os, pathlib, re, subprocess, sys, tempfile, time
H = pathlib.Path.home(); P = pathlib.Path(os.environ.get("LCOMPILE_LEAN", str(H / "weil-conjectures-sheaf" / "lean"))); BUILD = P / ".lake/build/lib/lean"
ENV = dict(os.environ, PATH=str(H / ".elan" / "bin") + ":" + os.environ.get("PATH", ""))
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*$", re.M)
def base_opts():
    out = []; on = False
    for l in (P / "lakefile.toml").read_text().split("\n"):
        if l.startswith("[leanOptions]"): on = True; continue
        if l.startswith("["): on = False
        m = re.match(r"([A-Za-z][\w.]*)\s*=\s*([^#]*)", l) if on else None
        if m: out.append(f"-D{m.group(1)}={m.group(2).strip().strip(chr(34))}")
    return out
def upstream(f):
    s = str(pathlib.Path(f).resolve())
    return "/WeilConjectures/" in s or "/Comparator/" in s or pathlib.Path(f).name.startswith("WeilConjectures_")
def lean_root(f):
    """The directory named lean/ above the file (the root its module name is read from), or None."""
    parts = pathlib.Path(f).resolve().parts
    ks = [k for k, x in enumerate(parts[:-1]) if x == "lean"]
    return pathlib.Path(*parts[:ks[-1] + 1]) if ks else None
def modname(f):
    r = lean_root(f)
    return ".".join(pathlib.Path(f).resolve().relative_to(r).with_suffix("").parts) if r else pathlib.Path(f).stem
def lean_path(first=None):
    ps = ([str(first)] if first else []) + [str(BUILD)] + sorted(str(x) for x in (P / ".lake/packages").glob("*/.lake/build/lib/lean"))
    return ":".join(ps)
def output_parent(lb, rel):
    """Make only the output's ancestors real; never write through old farm links."""
    dst = pathlib.Path(lb)
    for part in rel.parts[:-1]:
        dst = dst / part
        if dst.is_symlink(): dst.unlink()
        dst.mkdir(exist_ok=True)

def local_artifacts(lb):
    """Index only real sandbox modules, without following any library symlinks.

    Lean 4.33 selects whole package roots in LEAN_PATH. --setup overrides just
    these local modules (including transitive imports), leaving shared imports
    on the normal search path. Keep every available module/IR companion.
    """
    arts = {}
    def visit(directory):
        with os.scandir(directory) as entries:
            for entry in entries:
                if entry.is_symlink(): continue
                if entry.is_dir(follow_symlinks=False):
                    visit(pathlib.Path(entry.path))
                elif entry.name.endswith(".olean"):
                    p = pathlib.Path(entry.path)
                    name = ".".join(p.relative_to(lb).with_suffix("").parts)
                    oleans = [str(p)]
                    for suffix in (".olean.server", ".olean.private"):
                        q = p.with_suffix(suffix)
                        if not q.is_file(): break
                        oleans.append(str(q))
                    ir = []
                    for suffix in (".ir.sig", ".ir"):
                        q = p.with_suffix(suffix)
                        if not q.is_file(): break
                        ir.append(str(q))
                    arts[name] = [oleans, ir]
    if lb: visit(pathlib.Path(lb))
    return arts

import contextlib, fcntl, shlex
SLOTS = int(os.environ.get("NT_LCOMPILE_SLOTS", "24"))   # measured ~1.2 cores each on this 64-core machine
LOCAL_WAIT = float(os.environ.get("LCOMPILE_LOCAL_WAIT", "3"))   # seconds to wait for a local slot before going remote
SERVER = "ubuntu@the project server"; SSH_KEY = str(pathlib.Path.home() / "weil_formal.pem")
def take_slot():
    """A free local compile slot (a locked file), or None. At most SLOTS compiles at once on this machine."""
    d = pathlib.Path.home() / "weil-nt-overlay" / "slots"; d.mkdir(parents=True, exist_ok=True)
    for i in range(SLOTS):
        f = open(d / f"{i}", "w")
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB); return f
        except OSError:
            f.close()
    return None
def remote(rel, text, timeout):
    """Compile on the project server against its published build (~/cc1/rcompile.py; the human, 2026-10-13: when the
    local slots are full). One multiplexed ssh connection is shared by all workers (no connection storm). Returns
    (exit code, output), or None when the server is busy or unreachable."""
    # sshd allows 10 sessions per connection (MaxSessions): spread over MUX connections
    cp = str(pathlib.Path.home() / ".ssh" / f"cm-weil-rcompile-{os.getpid() % int(os.environ.get('LCOMPILE_MUX', '3'))}")
    cmd = ["ssh", "-i", SSH_KEY, "-o", "StrictHostKeyChecking=no", "-o", "ConnectTimeout=20", "-o", "ControlMaster=auto",
           "-o", f"ControlPath={cp}", "-o", "ControlPersist=600", "-o", "ServerAliveInterval=30", SERVER,
           f"python3 ~/cc1/rcompile.py {shlex.quote(str(rel))} {int(timeout)}"]
    try:
        p = subprocess.run(cmd, input=text, capture_output=True, text=True, timeout=timeout + 90)
    except subprocess.TimeoutExpired:
        return None
    if p.returncode in (75, 255) or "rcompile" not in p.stdout + p.stderr and p.returncode != 0 and not p.stdout:
        return None
    return p.returncode, p.stdout + p.stderr

def run(f, timeout=60, out=None, probe=""):
    """Compile one file. `out`: the directory compiled modules of the sandbox are written to and read from (the file is
    written there too, as a module others can import). `probe`: text appended to a temporary copy (deliver3.py)."""
    f = pathlib.Path(f).resolve(); root = lean_root(f); t = time.time()
    lb = pathlib.Path(out) if out else (root.parent / ".lbuild" if root and (root.parent / ".lbuild").is_dir() else None)
    cmd = ["lean", *base_opts()] + ([] if upstream(f) else ["-DautoImplicit=false"])
    src = f
    if probe:
        src = f.with_name(f.stem + "__probe.lean"); src.write_text(f.read_text() + probe)
    elif root: cmd += ["-R", str(root)]
    if out and root and not probe:
        o = pathlib.Path(out) / f.relative_to(root).with_suffix(".olean"); output_parent(pathlib.Path(out), f.relative_to(root))
        for x in o.parent.glob(o.stem + ".*"): x.unlink()
        cmd += ["-o", str(o), "-i", str(o.with_suffix(".ilean"))]
    arts = local_artifacts(lb)
    setup = None
    try:
        if arts:
            with tempfile.NamedTemporaryFile(mode="w", suffix=".json", prefix="lcompile-", delete=False) as sf:
                setup = pathlib.Path(sf.name)
                json.dump({"name": modname(src), "isModule": False, "importArts": arts, "dynlibs": [], "plugins": [], "options": {}}, sf)
            cmd += ["--setup", str(setup)]
        lock = take_slot(); go_remote = False
        waited = time.time()
        while lock is None:
            if go_remote and time.time() - waited > LOCAL_WAIT:
                r = remote(src.relative_to(root), src.read_text(), timeout)
                if r is not None:
                    return r[0], r[1]
                waited = time.time() + 7                       # the server is busy too: try it again in about 10 s
            time.sleep(1); lock = take_slot()
        try:
            p = subprocess.run(["nice", "-n", "19"] + cmd + [str(src)], cwd=P, env=dict(ENV, LEAN_PATH=lean_path(), LEAN_NUM_THREADS="1"), capture_output=True, text=True, timeout=timeout)
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN); lock.close()
    except subprocess.TimeoutExpired as exc:
        # communicate() retains output collected before the deadline (as bytes,
        # even with text=True). Keep earlier Lean errors and profiler messages.
        partial = "".join(value.decode(errors="replace") if isinstance(value, bytes) else value or ""
                          for value in (exc.stdout, exc.stderr))
        return 124, partial + ("\n" if partial and not partial.endswith("\n") else "") + \
            f"timeout after {timeout} s: the fault is usually a definition that is expensive to unfold, not the limit"
    finally:
        if setup: setup.unlink(missing_ok=True)
        if probe: src.unlink(missing_ok=True)
    note = f"(with the modules compiled into {lb}) " if lb and not out and arts else ""
    return p.returncode, (p.stdout + p.stderr) + f"\n{note}[{time.time()-t:.1f} s]"
def order(files):
    """The files, a module after the siblings it imports."""
    mods = {modname(f): pathlib.Path(f) for f in files}
    imp = {m: [d for d in IMPORT.findall(p.read_text()) if d in mods and d != m] for m, p in mods.items()}
    out = []; left = dict(imp)
    while left:
        ready = sorted(m for m, ds in left.items() if not [d for d in ds if d in left])
        if not ready: raise SystemExit("the modules import one another in a cycle: " + ", ".join(left))
        for m in ready: out.append(mods[m]); del left[m]
    return out
def run_set(files, timeout=60):
    """Compile several files of one sandbox in import order; returns (exit code, output, [(file, exit code)])."""
    files = [pathlib.Path(f).resolve() for f in files]; roots = {lean_root(f) for f in files}
    if len(roots) != 1 or None in roots: return 2, "the files must lie under one directory named lean/ (the sandbox mirrors the repository)", []
    lb = roots.pop().parent / ".lbuild"; lb.mkdir(exist_ok=True)
    rc = 0; text = []; per = []
    for f in order(files):
        r, o = run(f, timeout, out=lb); per.append((f, r)); rc = rc or r
        text.append(f"== {modname(f)} ({'compiled' if r == 0 else 'NOT compiled'})\n{o.strip()}")
        if r: text.append("(stopped here: the modules after this one may import it)"); break
    return rc, "\n".join(text), per
if __name__ == "__main__":
    fs = sys.argv[1:]
    if not fs: raise SystemExit(__doc__)
    if fs[0] == "--all":
        fs = sorted(str(x) for x in (pathlib.Path(fs[1]) / "lean").rglob("*.lean") if not x.name.endswith("__probe.lean"))
        if not fs: raise SystemExit("no .lean file under " + sys.argv[2] + "/lean")
    if len(fs) > 1: rc, out, _ = run_set(fs)
    else: rc, out = run(fs[0])
    print(out[-12000:]); print(f"[exit code {rc}: {'compiled' if rc == 0 else 'NOT compiled'}]"); sys.exit(rc)
