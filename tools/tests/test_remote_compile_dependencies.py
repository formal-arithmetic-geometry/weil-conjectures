"""Regression checks for imports landed after the last green publication; no Lean runs."""
import io
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parent
if not (TOOLS / "remote_compile_set.py").exists():
    TOOLS = TOOLS.parent
sys.path.insert(0, str(TOOLS))
from remote_compile_dependencies import missing_dependencies, DependencySourceError


def imports(path):
    return [line.split()[-1] for line in path.read_text().splitlines()
            if line.startswith(("import ", "public import "))]


class MissingImports(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="rset-missing-import-test-")
        self.addCleanup(self.tmp.cleanup)
        self.home = Path(self.tmp.name)
        self.repo = self.home / "weil-conjectures-sheaf"
        self.lean = self.repo / "lean"
        self.lean.mkdir(parents=True)
        (self.lean / "lakefile.toml").write_text("[leanOptions]\n")
        (self.home / "cc1").mkdir()
        self.pub = self.lean / ".lake/build/lib/lean"
        self.root, self.lb = self.home / "request/lean", self.home / "request/.lbuild"
        self.root.mkdir(parents=True)
        self.lb.mkdir(parents=True)
        self.jobs = [{"rel": "Test.lean", "out": False, "upstream": False}]
        (self.root / "Test.lean").write_text("module\nimport Sheaf.A\n")
        self.source("Sheaf/A.lean", "module\nimport Sheaf.B\n")
        self.source("Sheaf/B.lean", "module\nimport Sheaf.Published\n")
        self.source("Sheaf/Published.lean", "module\n")
        published = self.pub / "Sheaf/Published.olean"
        published.parent.mkdir(parents=True)
        published.write_bytes(b"green")
        subprocess.run(["git", "init", "-q", str(self.repo)], check=True)
        subprocess.run(["git", "add", "lean"], cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "fixture"], cwd=self.repo, check=True)

    def source(self, rel, text):
        p = self.lean / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def resolve(self):
        return missing_dependencies(self.jobs, self.root, self.lb, self.pub,
                                    self.lean, self.repo, imports)

    def test_order_and_published_boundary(self):
        jobs = self.resolve()
        self.assertEqual([j["dependency"] for j in jobs], ["Sheaf.B", "Sheaf.A"])
        self.assertEqual((self.root / "Sheaf/A.lean").read_bytes(),
                         (self.lean / "Sheaf/A.lean").read_bytes())
        self.assertEqual(list(self.pub.rglob("*.olean")),
                         [self.pub / "Sheaf/Published.olean"])

    def test_caller_artifacts_and_requested_jobs_win(self):
        artifact = self.lb / "Sheaf/A.olean"
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b"caller")
        self.assertEqual(self.resolve(), [])
        artifact.unlink()
        self.jobs.append({"rel": "Sheaf/A.lean"})
        p = self.root / "Sheaf/A.lean"
        p.parent.mkdir(parents=True)
        p.write_text("module\n")
        self.assertEqual(self.resolve(), [])

    def test_dirty_source_rejected(self):
        self.source("Sheaf/B.lean", "module\n-- uncommitted change\n")
        with self.assertRaisesRegex(DependencySourceError, "Sheaf.B differs from committed"):
            self.resolve()

    def test_import_cycle_rejected(self):
        self.source("Sheaf/B.lean", "module\nimport Sheaf.A\n")
        subprocess.run(["git", "add", "lean/Sheaf/B.lean"], cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "cycle"], cwd=self.repo, check=True)
        with self.assertRaisesRegex(DependencySourceError, "import cycle at Sheaf.A"):
            self.resolve()

    def service(self, failure=None):
        request = io.BytesIO()
        with tarfile.open(fileobj=request, mode="w:gz") as archive:
            manifest = json.dumps({"timeout": 60, "jobs": self.jobs}).encode()
            member = tarfile.TarInfo("manifest.json")
            member.size = len(manifest)
            archive.addfile(member, io.BytesIO(manifest))
            archive.add(self.root / "Test.lean", arcname="lean/Test.lean")
        incoming = io.TextIOWrapper(io.BytesIO(request.getvalue()))
        outgoing = io.TextIOWrapper(io.BytesIO())
        actual_run, calls = subprocess.run, []

        def compile_file(command, **kwargs):
            if "git" == command[0]:
                return actual_run(command, **kwargs)
            self.assertEqual(kwargs["timeout"], 60)
            src = Path(command[-1])
            calls.append(src.stem)
            if src.stem == failure:
                return subprocess.CompletedProcess(command, 1, "error: dependency failed\n", "")
            if src.stem == "Test":
                setup = json.loads(Path(command[command.index("--setup") + 1]).read_text())
                self.assertEqual(set(setup["importArts"]), {"Sheaf.A", "Sheaf.B"})
            if "-o" in command:
                Path(command[command.index("-o") + 1]).write_bytes(src.read_bytes())
            return subprocess.CompletedProcess(command, 0, "", "")

        with patch("pathlib.Path.home", return_value=self.home), \
             patch("subprocess.run", side_effect=compile_file), \
             patch("sys.stdin", incoming), patch("sys.stdout", outgoing):
            runpy.run_path(str(TOOLS / "remote_compile_set.py"), run_name="__main__")
        with tarfile.open(fileobj=io.BytesIO(outgoing.buffer.getvalue()), mode="r:gz") as archive:
            reply = json.load(archive.extractfile("result.json"))
        self.assertFalse(list((self.home / "cc1/rset-tmp").iterdir()))
        return reply, calls

    def test_service_compiles_then_reuses_private_dependencies(self):
        reply, calls = self.service()
        self.assertEqual(calls, ["B", "A", "Test"])
        self.assertEqual([r["rel"] for r in reply["results"]], ["Test.lean"])
        self.assertEqual(reply["results"][0]["rc"], 0)
        reply, calls = self.service()
        self.assertEqual(calls, ["Test"])
        self.assertIn("(cache)", reply["results"][0]["out"])
        self.assertEqual(list(self.pub.rglob("*.olean")),
                         [self.pub / "Sheaf/Published.olean"])

    def test_dependency_error_is_returned_for_requested_job(self):
        reply, calls = self.service(failure="B")
        self.assertEqual(calls, ["B"])
        self.assertEqual(reply["results"][0]["rc"], 1)
        self.assertIn("Dependency Sheaf.B", reply["results"][0]["out"])
        self.assertIn("error: dependency failed", reply["results"][0]["out"])


if __name__ == "__main__":
    unittest.main()
