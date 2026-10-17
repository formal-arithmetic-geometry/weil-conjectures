"""Shared admission for dispatched Codex children; no dispatcher restart needed."""
import contextlib
import fcntl
import json
import os
from pathlib import Path
import time


ROOT = Path.home() / "weil-launcher-all/provider-admission"
DEFAULTS = {"max_children": 64, "start_interval": 1.0, "cooldown_seconds": 60.0}


class AdmissionTimeout(Exception):
    pass


def identity(pid):
    """A PID plus Linux start ticks protects against PID reuse; zombies are dead."""
    try:
        fields = Path(f"/proc/{pid}/stat").read_text().rsplit(") ", 1)[1].split()
        return None if fields[0] == "Z" else fields[19]
    except (OSError, IndexError):
        return None


def unmanaged_children(real, owners):
    """Count legacy workers and reviewers which do not own an admission lease."""
    result = 0
    real = Path(real).resolve()
    for directory in Path("/proc").glob("[0-9]*"):
        try:
            # Reading exe first avoids decoding command lines of unrelated tools.
            if (directory / "exe").resolve() != real:
                continue
            args = (directory / "cmdline").read_bytes().split(b"\0")
            if b"exec" not in args[:3]:
                continue
            stat = (directory / "stat").read_text().rsplit(") ", 1)[1].split()
            if stat[0] != "Z" and stat[1] not in owners:
                result += 1
        except (OSError, IndexError):
            continue
    return result


class Gate:
    def __init__(self, real, root=ROOT, *, scan=unmanaged_children):
        self.real, self.root, self.scan = real, Path(root), scan
        self.root.mkdir(parents=True, exist_ok=True)
        self.owner = str(os.getpid())
        self.token = identity(os.getpid())
        self.ticket = f"{self.owner}-{time.time_ns()}"

    @contextlib.contextmanager
    def locked(self):
        with (self.root / "lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            path = self.root / "state.json"
            state = json.loads(path.read_text()) if path.exists() else {}
            state.setdefault("waiting", {})
            state.setdefault("active", {})
            yield state
            tmp = self.root / f"state.tmp-{self.owner}"
            tmp.write_text(json.dumps(state) + "\n")
            tmp.replace(path)

    def settings(self):
        path = self.root / "config.json"
        cfg = dict(DEFAULTS)
        if path.exists():
            cfg.update(json.loads(path.read_text()))
        if int(cfg["max_children"]) < 1 or min(float(cfg[k]) for k in
                ("start_interval", "cooldown_seconds")) < 0:
            raise ValueError("invalid provider admission settings")
        return cfg

    def acquire(self, deadline, emit=print):
        """Wait FIFO within the worker's existing monotonic deadline."""
        announced = 0.0
        try:
            while True:
                if deadline - time.monotonic() <= 30:
                    raise AdmissionTimeout("provider capacity wait exhausted the worker budget")
                now = time.time()
                cfg = self.settings()
                with self.locked() as state:
                    if now >= state.get("scan_after", 0):
                        for name in ("waiting", "active"):
                            state[name] = {k: v for k, v in state[name].items()
                                           if identity(int(v["owner"])) == v["token"]}
                        state["external"] = self.scan(
                            self.real, {v["owner"] for v in state["active"].values()})
                        state["scan_after"] = now + 2
                    state["waiting"].setdefault(self.ticket, {
                        "owner": self.owner, "token": self.token, "time": now})
                    first = min(state["waiting"], key=lambda k: (state["waiting"][k]["time"], k))
                    active = len(state["active"]) + state.get("external", 0)
                    ready = max(state.get("next_start", 0), state.get("cooldown_until", 0))
                    if first == self.ticket and active < int(cfg["max_children"]) and now >= ready:
                        state["active"][self.ticket] = state["waiting"].pop(self.ticket)
                        state["next_start"] = now + float(cfg["start_interval"])
                        return
                    reason = f"{active}/{cfg['max_children']} children, {len(state['waiting'])} queued"
                remaining = deadline - time.monotonic()
                if remaining <= 30:
                    raise AdmissionTimeout(reason)
                if now - announced >= 30:
                    emit(f"[codex-admission] waiting for provider capacity: {reason}\n")
                    announced = now
                time.sleep(min(5, remaining - 30))
        except BaseException:
            self.release()
            raise

    def release(self):
        with self.locked() as state:
            state["active"].pop(self.ticket, None)
            state["waiting"].pop(self.ticket, None)
            # Recount when a managed child leaves; legacy children may have exited too.
            state["scan_after"] = 0

    def rate_limited(self):
        cfg = self.settings()
        with self.locked() as state:
            now = time.time()
            # A burst is one event. Repeated failures inside its cooldown do not
            # continually extend it and starve every waiting worker.
            if now >= state.get("cooldown_until", 0):
                state["cooldown_until"] = now + float(cfg["cooldown_seconds"])
                state["rate_limit_events"] = state.get("rate_limit_events", 0) + 1
