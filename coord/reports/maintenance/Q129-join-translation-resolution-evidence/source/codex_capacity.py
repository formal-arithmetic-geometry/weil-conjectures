"""Shared, adaptive admission for pipeline workers and maintenance sessions."""
import pathlib
import re
import threading
import time


def provider_failure(log_path):
    """Recover a fatal 429 when Codex could not write its final-answer file."""
    try:
        with open(log_path, "rb") as stream:
            stream.seek(0, 2)
            stream.seek(max(0, stream.tell() - 65536))
            tail = stream.read().decode(errors="replace")
    except OSError:
        return ""
    errors = [line for line in tail.splitlines() if re.search(
        r"^ERROR: .*\b429\b|^.*ERROR codex_core::.*Fatal error: http 429", line)]
    return errors[-1][:500] if errors else ""


class ProviderCapacity:
    """Failure counts never gate items; observed provider capacity gates launches.

    Existing sessions drain naturally. A 429 halves admission and cools launches
    for one minute after the most recent 429. Successful answers grow admission
    slowly. All launch paths, including maintenance and second readers, share
    the same reservation pool, protected against concurrent reaper threads.
    """

    def __init__(self, maximum, alive, initial=16, cooldown=60, clock=time.monotonic):
        self.maximum = max(1, maximum)
        self.limit = min(self.maximum, max(1, initial))
        self.cooldown = max(1, cooldown)
        self.clock = clock
        self.alive = alive
        self.pids = set()
        self.maintenance = set()
        self.reserved = 0
        self.until = 0
        self.last_decrease = float("-inf")
        self.last_increase = clock()
        self.lock = threading.Lock()

    def adopt(self, pids, maintenance=False):
        with self.lock:
            pids = set(pids)
            self.pids.update(pids)
            if maintenance:
                self.maintenance.update(pids)

    def _available(self):
        self.pids = {pid for pid in self.pids if self.alive(pid)}
        # Pending reservations have no PID yet. Keep them until started() or
        # __exit__ releases them, so concurrent maintenance launches share the cap.
        self.maintenance = {owner for owner in self.maintenance
                            if owner in self.pids or
                            (isinstance(owner, Reservation) and owner.pending)}
        if self.clock() < self.until:
            return 0
        return max(0, self.limit - len(self.pids) - self.reserved)

    def available(self):
        with self.lock:
            return self._available()

    def acquire(self, maintenance=False):
        with self.lock:
            if not self._available() or (maintenance and len(self.maintenance) >= 2):
                return None
            self.reserved += 1
            # Include pending reservations in the maintenance cap as well.
            slot = Reservation(self, maintenance)
            if maintenance:
                self.maintenance.add(slot)
            return slot

    def rate_limited(self):
        with self.lock:
            now = self.clock()
            # One burst can contain hundreds of ended sessions. Reduce once
            # per interval, rather than once for each member of that burst.
            if now - self.last_decrease >= self.cooldown:
                self.limit = max(1, self.limit // 2)
                self.last_decrease = now
            self.until = max(self.until, now + self.cooldown)
            self.last_increase = self.until

    def success(self):
        with self.lock:
            now = self.clock()
            if now >= self.until and now - self.last_increase >= self.cooldown:
                self.limit = min(self.maximum, self.limit + 1)
                self.last_increase = now


class Reservation:
    def __init__(self, capacity, maintenance):
        self.capacity = capacity
        self.maintenance = maintenance
        self.pending = True

    def __enter__(self):
        return self

    def __exit__(self, *args):
        with self.capacity.lock:
            if self.pending:
                self.capacity.reserved -= 1
                self.capacity.maintenance.discard(self)
                self.pending = False

    def started(self, pid):
        with self.capacity.lock:
            self.capacity.reserved -= 1
            self.capacity.pids.add(pid)
            if self.maintenance:
                self.capacity.maintenance.discard(self)
                self.capacity.maintenance.add(pid)
            self.pending = False


def maintenance_pids(root):
    for path in pathlib.Path(root).glob("*/pid"):
        try:
            yield int(path.read_text())
        except (OSError, ValueError):
            pass
