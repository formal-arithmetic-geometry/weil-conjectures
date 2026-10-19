"""coord/.merge.lock with a timeout (default 120 s, env SHEAF_LOCK_TIMEOUT).

A tool that takes the lock itself (merge_delivery.py, attach.py) must never be run under `flock coord/.merge.lock`:
the outer flock holds the lock on another descriptor and the tool would wait for itself. With the timeout the tool
gives up instead and names the holder, read from /proc/locks (inode and device of the lock file)."""
from __future__ import annotations
import contextlib, fcntl, os, pathlib, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
LOCK = ROOT / "coord" / ".merge.lock"


class LockTimeout(RuntimeError):
    pass


def timeout() -> float:
    try:
        return float(os.environ.get("SHEAF_LOCK_TIMEOUT", "120"))
    except ValueError:
        return 120.0


def holder(path: pathlib.Path) -> str:
    """'pid <n>: <command line>' of the process holding a lock on path, from /proc/locks; 'pid unknown' if none found."""
    try:
        st = os.stat(path)
        maj, mnr = os.major(st.st_dev), os.minor(st.st_dev)
        for ln in open("/proc/locks"):
            f = ln.split()
            if len(f) < 6 or f[1] == "->":  # a waiter, not a holder
                continue
            try:
                dmaj, dmin, ino = f[5].split(":")
                if int(ino) != st.st_ino or int(dmaj, 16) != maj or int(dmin, 16) != mnr:
                    continue
            except ValueError:
                continue
            pid = f[4]
            if pid == str(os.getpid()):
                cmd = "this process (another descriptor)"
            else:
                try:
                    cmd = pathlib.Path(f"/proc/{pid}/cmdline").read_bytes().replace(b"\0", b" ").decode(errors="replace").strip()
                except OSError:
                    cmd = "(command line unreadable)"
            return f"pid {pid}: {cmd}"
    except OSError:
        pass
    return "pid unknown"


def acquire(f, path: pathlib.Path = LOCK, secs: float | None = None):
    secs = timeout() if secs is None else secs
    end = time.monotonic() + secs
    while True:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return
        except BlockingIOError:
            if time.monotonic() >= end:
                rel = path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else str(path)
                raise LockTimeout(f"{rel} held for {secs:g} s by {holder(path)}")
            time.sleep(0.2)


_HELD: dict[str, int] = {}   # lock files this process holds through merge_lock(), for reentrant nesting


def _key(path: pathlib.Path) -> str:
    try:
        return str(path.resolve())
    except OSError:
        return str(path)


@contextlib.contextmanager
def merge_lock(path: pathlib.Path = LOCK):
    """The lock on `path`, reentrant within this process. One DAG (2026-10-18, tools/livedag.py): this project's own
    lock also takes the live repository's coord/.merge.lock (always in this order) and then makes HEAD carry the live
    DAG, so a holder reads and writes the live DAG (dag/nodes is the link to it) with no other writer of it running."""
    key = _key(path)
    if _HELD.get(key):
        _HELD[key] += 1
        try:
            yield
        finally:
            _HELD[key] -= 1
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "a") as f:
        acquire(f, path)
        _HELD[key] = 1
        try:
            if key == _key(LOCK) and (ROOT / "dag" / "nodes").is_symlink():
                import sys
                here = str(pathlib.Path(__file__).resolve().parent)
                if here not in sys.path:
                    sys.path.insert(0, here)
                import livedag
                with merge_lock(livedag.LIVE / "coord" / ".merge.lock"):
                    livedag.graft()
                    yield
            else:
                yield
        finally:
            _HELD.pop(key, None)
            fcntl.flock(f, fcntl.LOCK_UN)
