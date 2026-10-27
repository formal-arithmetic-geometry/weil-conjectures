"""The CPU caches of the delivery checks (2026-10-24) give the results of the uncached code.

    python3 -m unittest discover -s tools -p test_check_caches.py      (temporary directories; no Lean, no git)
"""
import importlib, json, os, pathlib, sys, tempfile, unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

TEXTS = {
    "A": "module\npublic import Mathlib.Foo\nimport B\n",
    "B": "/- import Ghost\n/- nested -/ import Ghost2 -/\nimport C -- import D\n\"import E\"\nimport F\n",
    "C": "theorem x : True := by\n  sorry\n/-- doc -/\nimport G\n\"a\\\"b\nimport H\"\n",
    "D": "-- only a comment\n",
}


class ImportGraph(unittest.TestCase):
    def test_memo_equals_scan(self):
        import import_cycles as ic
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            (root / "Sheaf").mkdir()
            for k, t in TEXTS.items():
                (root / "Sheaf" / f"{k}.lean").write_text(t)
            plain = {f"Sheaf.{k}": ic.imports(t) for k, t in TEXTS.items()}
            for _ in range(2):      # computed, then from the memo
                g = ic.graph(root)
                self.assertEqual(g, plain)
            (root / "Sheaf" / "D.lean").write_text("import Z\n")
            self.assertEqual(ic.graph(root)["Sheaf.D"], {"Z"})
            g["Sheaf.A"].add("mutated")     # a caller's change does not reach the memo
            self.assertEqual(ic.graph(root)["Sheaf.A"], plain["Sheaf.A"])


class LiveClosed(unittest.TestCase):
    def test_memo_follows_file_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            live = pathlib.Path(tmp) / "live"
            (live / "lean" / "Sheaf").mkdir(parents=True)
            os.environ["SHEAF_LIVE_REPO"] = str(live)
            os.environ["SHEAF_LIVE_CLOSED_CACHE"] = str(pathlib.Path(tmp) / "cache" / "live-closed.json")
            try:
                import live_closed
                lc = importlib.reload(live_closed)
                src = live / "lean" / "Sheaf"
                (src / "A.lean").write_text("import Sheaf.B\ntheorem a : True := trivial\n")
                (src / "B.lean").write_text("theorem b : True := by\n  sorry\n")
                (src / "C.lean").write_text("/- sorry -/ theorem c : True := trivial\n")
                self.assertEqual(lc._compute(), ["Sheaf.C"])
                self.assertTrue(lc.FILES.is_file())
                self.assertEqual(lc._compute(), ["Sheaf.C"])          # from the per-file memo
                (src / "B.lean").write_text("theorem b : True := trivial\n")
                self.assertEqual(lc._compute(), ["Sheaf.A", "Sheaf.B", "Sheaf.C"])
            finally:
                os.environ.pop("SHEAF_LIVE_REPO", None); os.environ.pop("SHEAF_LIVE_CLOSED_CACHE", None)
                importlib.reload(live_closed)


class NodeFiles(unittest.TestCase):
    def test_one_parse_per_file_version(self):
        import nodefiles
        with tempfile.TemporaryDirectory() as tmp:
            p = pathlib.Path(tmp) / "a.json"
            p.write_text('{"id": "a"}')
            nodefiles.enable()
            a = nodefiles.read(p)
            self.assertIs(nodefiles.read(p), a)
            p.write_text('{"id": "a", "k": 1}')
            self.assertEqual(nodefiles.read(p), {"id": "a", "k": 1})
            p.write_text('{"id": ')
            for _ in range(2):
                with self.assertRaises(json.JSONDecodeError):
                    nodefiles.read(p)
            p.write_bytes(b'{"id": "\xff"}')
            with self.assertRaises(UnicodeDecodeError):
                nodefiles.read(p)
            p.unlink()
            with self.assertRaises(OSError):
                nodefiles.read(p)

if __name__ == "__main__":
    unittest.main()
