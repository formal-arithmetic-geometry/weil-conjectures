"""Restart and concurrency regressions for the Q129 provider-capacity failure."""
import ast
import concurrent.futures
import fcntl
import importlib.util
import pathlib
import re
import sys
import tempfile
import time
import unittest
from types import SimpleNamespace
from unittest.mock import Mock


SOURCE = pathlib.Path(sys.argv.pop(1)) if len(sys.argv) > 1 else pathlib.Path(__file__).with_name('dispatch_all.py')
CAPACITY_PATH = SOURCE.with_name('codex_capacity.py')
spec = importlib.util.spec_from_file_location('q129_capacity', CAPACITY_PATH)
capacity_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(capacity_module)
ProviderCapacity = capacity_module.ProviderCapacity
TREE = ast.parse(SOURCE.read_text())


def definition(name, namespace):
    node = next(n for n in TREE.body if getattr(n, 'name', None) == name)
    exec(compile(ast.Module(body=[node], type_ignores=[]), str(SOURCE), 'exec'), namespace)
    return namespace[name]


class ProviderAdmission(unittest.TestCase):
    def test_real_main_initializes_capacity_before_first_pass(self):
        with tempfile.TemporaryDirectory() as root:
            namespace = dict(A=pathlib.Path(root), fcntl=fcntl, CFG={'batches': [], 'lanes': []},
                             TOTAL=32, PER_GROUP=4, CLAIMS=4, DRY=True, CAPACITY=None,
                             ProviderCapacity=ProviderCapacity, alive=lambda pid: False,
                             maintenance_pids=lambda path: [], log=lambda *args: None,
                             concurrent=concurrent, time=time, write_queue=lambda *args: None,
                             Batch=None, Group=None, lanes=lambda batches: [])
            definition('main', namespace)()
            self.assertIsInstance(namespace['CAPACITY'], ProviderCapacity)
            self.assertEqual(namespace['CAPACITY'].available(), 16)

    def test_adopted_sessions_drain_without_killing_or_oversubscription(self):
        live = set(range(30))
        capacity = ProviderCapacity(700, live.__contains__, initial=16)
        capacity.adopt(live)
        self.assertEqual(capacity.available(), 0)
        self.assertIsNone(capacity.acquire())
        live.difference_update(range(15))
        self.assertEqual(capacity.available(), 1)
        with capacity.acquire() as admission:
            self.assertEqual(capacity.available(), 0)
            live.add(100)
            admission.started(100)
        self.assertEqual(capacity.available(), 0)
        self.assertEqual(len(live), 16)

    def test_concurrent_maintenance_reservations_share_two_slot_cap(self):
        capacity = ProviderCapacity(32, lambda pid: True, initial=16)
        first = capacity.acquire(maintenance=True)
        second = capacity.acquire(maintenance=True)
        self.assertIsNotNone(first)
        self.assertIsNotNone(second)
        self.assertIsNone(capacity.acquire(maintenance=True))
        first.__exit__(None, None, None)
        second.__exit__(None, None, None)
        self.assertEqual(capacity.available(), 16)

    def test_provider_burst_reduces_once_then_recovers_gradually(self):
        now = [100.0]
        capacity = ProviderCapacity(32, lambda pid: False, initial=16, clock=lambda: now[0])
        for _ in range(50):
            capacity.rate_limited()
        self.assertEqual(capacity.limit, 8)
        self.assertEqual(capacity.available(), 0)
        now[0] += 60
        self.assertEqual(capacity.available(), 8)
        capacity.success()
        self.assertEqual(capacity.limit, 8)
        now[0] += 60
        capacity.success()
        self.assertEqual(capacity.limit, 9)

    def test_actual_maintenance_start_records_pid_and_level_after_admission(self):
        with tempfile.TemporaryDirectory() as root:
            base = pathlib.Path(root)
            capacity = ProviderCapacity(16, lambda pid: True)
            spawned = []
            def popen(command, **kwargs):
                spawned.append(command)
                return SimpleNamespace(pid=500)
            namespace = dict(A=base, pathlib=pathlib, time=time, DRY=False, MAINT_AT=5,
                             CAPACITY=capacity, alive=lambda pid: False, CODEX='fake-codex',
                             MODEL='fake-model', MAINT_PROMPT='{item} {state} {n}',
                             subprocess=SimpleNamespace(Popen=popen, STDOUT=-2), log=lambda *args: None)
            Group = definition('Group', namespace)
            group = Group.__new__(Group)
            group.g = 'Q129-test'
            group.dir = base / 'run'
            group.sf = group.dir / 'state.json'
            group.st = {'tries': {'fixture@new': 10}, 'stage': {'fixture': '2'}, 'notes': {}}
            group.b = SimpleNamespace(project='fake-project', tools=base, sandbox=lambda stage: base)
            group.save = Mock()
            group.maint('fixture', 'fixture@new')
            self.assertEqual(len(spawned), 1)
            self.assertEqual(group.st['maint']['fixture@new'], 10)
            self.assertIn(500, capacity.pids)
            self.assertIn(500, capacity.maintenance)
            self.assertEqual(capacity.reserved, 0)


if __name__ == '__main__':
    unittest.main()
