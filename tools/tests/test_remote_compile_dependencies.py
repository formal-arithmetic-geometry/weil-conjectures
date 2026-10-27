"""Regression checks for imports landed after the last green publication; no Lean runs."""
import hashlib
import io
import json
import os
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

    def landing(self, rel, text, rid="20261022T051844-L-1", seq=1):
        self.source(rel, text)
        builds = self.repo / "local/builds"
        staged = builds / "staged" / rid / rel
        staged.parent.mkdir(parents=True, exist_ok=True)
        staged.write_text(text)
        request = builds / "requests" / (rid + ".json")
        request.parent.mkdir(parents=True, exist_ok=True)
        request.write_text(json.dumps({
            "id": rid, "landed": "2026-10-22T05:18:44Z", "seq": seq,
            "files": [{"path": rel, "deleted": False,
                       "sha": hashlib.sha256(staged.read_bytes()).hexdigest()}]}))
        return staged, request

    def resolve(self):
        return missing_dependencies(self.jobs, self.root, self.lb, self.pub,
                                    self.lean, self.repo, imports)

    def published_trace(self, mod, dependencies):
        path = self.pub.joinpath(*mod.split(".")).with_suffix(".trace")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"inputs": [["deps", [["imports", [
            [dep + ":importArts", "hash"] for dep in dependencies]]]]]}))

    def test_missing_transitive_published_import_is_supplied(self):
        for mod in ("A", "B"):
            (self.pub / f"Sheaf/{mod}.olean").write_bytes(b"published importer")
        self.published_trace("Sheaf.A", ["Sheaf.B"])
        self.published_trace("Sheaf.B", ["Sheaf.Missing"])
        self.source("Sheaf/Missing.lean", "module\n")
        subprocess.run(["git", "add", "lean/Sheaf/Missing.lean"], cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "restored missing dependency"],
                       cwd=self.repo, check=True)
        before = {p: p.read_bytes() for p in self.pub.rglob("*.olean")}
        self.assertEqual([j["dependency"] for j in self.resolve()], ["Sheaf.Missing"])
        self.assertEqual(before, {p: p.read_bytes() for p in self.pub.rglob("*.olean")})

    def test_published_trace_ignores_unpublished_proof_plan(self):
        (self.pub / "Sheaf/A.olean").write_bytes(b"published importer")
        self.published_trace("Sheaf.A", ["Sheaf.Published"])
        # A newer, unfinished source plan must not be substituted for the
        # imports recorded by the published object's trace.
        self.source("Sheaf/A.lean", "module\nimport Sheaf.Unrelated\n")
        self.source("Sheaf/Unrelated.lean", "module\n")
        self.assertEqual(self.resolve(), [])
        self.assertFalse((self.root / "Sheaf/Unrelated.lean").exists())

    def test_missing_transitive_published_import_requires_trusted_source(self):
        (self.pub / "Sheaf/A.olean").write_bytes(b"published importer")
        self.published_trace("Sheaf.A", ["Sheaf.B"])
        self.source("Sheaf/B.lean", "module\n-- unfinished repair\n")
        with self.assertRaisesRegex(DependencySourceError, "Sheaf.B differs from committed"):
            self.resolve()

    def test_service_supplies_missing_transitive_published_import(self):
        (self.pub / "Sheaf/A.olean").write_bytes(b"published importer")
        self.published_trace("Sheaf.A", ["Sheaf.B"])
        reply, calls = self.service(expected_artifacts={"Sheaf.B", "Sheaf.A"})
        self.assertEqual(calls, ["B", "A", "Test"])
        self.assertEqual(reply["results"][0]["rc"], 0)
        self.assertIn("Compiled unpublished dependency Sheaf.B", reply["results"][0]["out"])
        self.assertEqual((self.pub / "Sheaf/A.olean").read_bytes(), b"published importer")

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

    def relocated_definition(self):
        """A and B existed in the green build; B now re-exports a new owner."""
        for mod in ("A", "B"):
            (self.pub / f"Sheaf/{mod}.olean").write_bytes(b"old declaration owner")
        self.source("Sheaf/B.lean", "module\npublic import Sheaf.Data\n")
        self.source("Sheaf/Data.lean", "module\ndef relocated : Nat := 0\n")
        subprocess.run(["git", "add", "lean/Sheaf/B.lean", "lean/Sheaf/Data.lean"],
                       cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "relocate definition"], cwd=self.repo, check=True)
        (self.root / "Test.lean").write_text(
            "module\nimport Sheaf.A\nimport Sheaf.Data\nimport Sheaf.Published\n")

    def test_relocation_finds_published_owner_through_transitive_importer(self):
        self.relocated_definition()
        before = {p: p.read_bytes() for p in self.pub.rglob("*.olean")}
        jobs = self.resolve()
        self.assertEqual([j["dependency"] for j in jobs],
                         ["Sheaf.Data", "Sheaf.B"])
        self.assertEqual(before, {p: p.read_bytes() for p in self.pub.rglob("*.olean")})

    def test_affected_published_importer_still_requires_trusted_source(self):
        self.relocated_definition()
        self.source("Sheaf/B.lean", "module\nimport Sheaf.Data\n-- uncommitted edit\n")
        with self.assertRaisesRegex(DependencySourceError, "Sheaf.B differs from committed"):
            self.resolve()

    def requested_relocation(self):
        """Data moves out of B; A used to import B and now imports Data."""
        self.relocated_definition()
        self.source("Sheaf/A.lean", "module\npublic import Sheaf.Data\n")
        self.source("Sheaf/B.lean", "module\nimport Sheaf.Data\nimport Sheaf.A\n")
        subprocess.run(["git", "add", "lean/Sheaf/A.lean", "lean/Sheaf/B.lean"],
                       cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "reverse the old owner import"], cwd=self.repo, check=True)
        (self.root / "Test.lean").write_text("module\nimport Sheaf.B\n")
        for mod in ("Data", "B"):
            rel = f"Sheaf/{mod}.lean"
            target = self.root / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((self.lean / rel).read_bytes())
        self.jobs[:0] = [{"rel": f"Sheaf/{mod}.lean", "out": True, "probe": ""}
                        for mod in ("Data", "B")]

    def test_requested_new_owner_invalidates_published_importer(self):
        self.requested_relocation()
        jobs = self.resolve()
        self.assertEqual([j["dependency"] for j in jobs], ["Sheaf.A"])
        self.assertEqual((self.root / "Sheaf/Data.lean").read_bytes(),
                         (self.lean / "Sheaf/Data.lean").read_bytes())

    def test_caller_new_owner_invalidates_published_importer(self):
        self.requested_relocation()
        self.jobs = self.jobs[-1:]
        for mod in ("Data", "B"):
            (self.root / f"Sheaf/{mod}.lean").unlink()
        artifact = self.lb / "Sheaf/Data.olean"
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b"caller new owner")
        self.assertEqual([j["dependency"] for j in self.resolve()], ["Sheaf.A", "Sheaf.B"])

    def test_published_proof_plans_do_not_add_unrelated_dependencies(self):
        self.source("Sheaf/Published.lean", "module\nimport Sheaf.Unrelated\n")
        self.source("Sheaf/Unrelated.lean", "module\n")
        subprocess.run(["git", "add", "lean/Sheaf/Published.lean", "lean/Sheaf/Unrelated.lean"],
                       cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "unrelated proof plan"], cwd=self.repo, check=True)
        self.assertEqual([j["dependency"] for j in self.resolve()], ["Sheaf.B", "Sheaf.A"])
        self.assertFalse((self.root / "Sheaf/Unrelated.lean").exists())

    def test_new_module_is_ordered_after_its_rebuilt_published_dependency(self):
        self.relocated_definition()
        self.source("Sheaf/Data.lean", "module\nimport Sheaf.Bridge\n")
        self.source("Sheaf/Bridge.lean", "module\nimport Sheaf.OtherData\n")
        self.source("Sheaf/OtherData.lean", "module\n")
        (self.pub / "Sheaf/Bridge.olean").write_bytes(b"old bridge")
        subprocess.run(["git", "add", "lean/Sheaf/Data.lean", "lean/Sheaf/Bridge.lean",
                        "lean/Sheaf/OtherData.lean"], cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "bridge fixture"], cwd=self.repo, check=True)
        with (self.root / "Test.lean").open("a") as source:
            source.write("import Sheaf.OtherData\n")
        self.assertEqual([j["dependency"] for j in self.resolve()],
                         ["Sheaf.OtherData", "Sheaf.Bridge", "Sheaf.Data", "Sheaf.B"])

    def test_new_import_branch_discovers_another_relocated_owner(self):
        self.relocated_definition()
        self.source("Sheaf/B.lean", "module\nimport Sheaf.Data\nimport Sheaf.Extra\n")
        self.source("Sheaf/Extra.lean", "module\nimport Sheaf.Owner\nimport Sheaf.ExtraData\n")
        self.source("Sheaf/Owner.lean", "module\nimport Sheaf.ExtraData\n")
        self.source("Sheaf/ExtraData.lean", "module\n")
        (self.pub / "Sheaf/Owner.olean").write_bytes(b"previous extra data owner")
        subprocess.run(["git", "add", "lean/Sheaf/B.lean", "lean/Sheaf/Extra.lean",
                        "lean/Sheaf/Owner.lean", "lean/Sheaf/ExtraData.lean"],
                       cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "nested relocation fixture"], cwd=self.repo, check=True)
        self.assertEqual([j["dependency"] for j in self.resolve()],
                         ["Sheaf.Data", "Sheaf.ExtraData", "Sheaf.Owner", "Sheaf.Extra", "Sheaf.B"])

    def test_published_importer_visits_all_new_dependencies(self):
        self.relocated_definition()
        self.landing("Sheaf/B.lean", "module\nimport Sheaf.Data\nimport Sheaf.OtherData\n")
        self.landing("Sheaf/OtherData.lean", "module\n", rid="20261022T051845-L-2", seq=2)
        self.assertEqual([j["dependency"] for j in self.resolve()],
                         ["Sheaf.Data", "Sheaf.OtherData", "Sheaf.B"])

    def test_dirty_source_rejected(self):
        self.source("Sheaf/B.lean", "module\n-- uncommitted change\n")
        with self.assertRaisesRegex(DependencySourceError, "Sheaf.B differs from committed"):
            self.resolve()

    def test_completed_landing_supplies_changed_and_new_dependencies(self):
        self.landing("Sheaf/B.lean", "module\nimport Sheaf.C\n")
        self.landing("Sheaf/C.lean", "module\n", rid="20261022T051845-L-2", seq=2)
        jobs = self.resolve()
        self.assertEqual([j["dependency"] for j in jobs], ["Sheaf.C", "Sheaf.B", "Sheaf.A"])
        self.assertIn("+landing:20261022T051844-L-1", jobs[1]["source_commit"])
        self.assertEqual((self.root / "Sheaf/B.lean").read_text(), "module\nimport Sheaf.C\n")
        self.assertEqual(list(self.pub.rglob("*.olean")),
                         [self.pub / "Sheaf/Published.olean"])

    def test_live_edit_after_landing_is_rejected(self):
        self.landing("Sheaf/B.lean", "module\n-- completed repair\n")
        self.source("Sheaf/B.lean", "module\n-- work still in progress\n")
        with self.assertRaisesRegex(DependencySourceError, "Sheaf.B differs from committed"):
            self.resolve()

    def test_corrupt_or_missing_staged_source_is_rejected(self):
        staged, _ = self.landing("Sheaf/B.lean", "module\n-- completed repair\n")
        staged.write_text("module\n-- corrupted staging\n")
        with self.assertRaisesRegex(DependencySourceError, "no matching completed landing"):
            self.resolve()
        (self.root / "Sheaf/A.lean").unlink()
        staged.unlink()
        with self.assertRaisesRegex(DependencySourceError, "no matching completed landing"):
            self.resolve()

    def test_incomplete_landing_is_rejected(self):
        _, request = self.landing("Sheaf/B.lean", "module\n-- incomplete repair\n")
        record = json.loads(request.read_text())
        del record["landed"]
        request.write_text(json.dumps(record))
        with self.assertRaisesRegex(DependencySourceError, "no matching completed landing"):
            self.resolve()

    def test_superseded_landing_is_not_used(self):
        old = "module\n-- previous repair\n"
        self.landing("Sheaf/B.lean", old)
        self.landing("Sheaf/B.lean", "module\n-- latest repair\n",
                     rid="20261022T051845-L-2", seq=2)
        self.source("Sheaf/B.lean", old)
        with self.assertRaisesRegex(DependencySourceError, "no matching completed landing"):
            self.resolve()

    def test_import_cycle_rejected(self):
        self.source("Sheaf/B.lean", "module\nimport Sheaf.A\n")
        subprocess.run(["git", "add", "lean/Sheaf/B.lean"], cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "cycle"], cwd=self.repo, check=True)
        with self.assertRaisesRegex(DependencySourceError, "import cycle at Sheaf.A"):
            self.resolve()

    def service(self, failure=None, expected_artifacts=None, stop_on_fail=False):
        request = io.BytesIO()
        with tarfile.open(fileobj=request, mode="w:gz") as archive:
            manifest = json.dumps({"timeout": 60, "jobs": self.jobs,
                                   "stop_on_fail": stop_on_fail}).encode()
            member = tarfile.TarInfo("manifest.json")
            member.size = len(manifest)
            archive.addfile(member, io.BytesIO(manifest))
            for job in self.jobs:
                archive.add(self.root / job["rel"], arcname="lean/" + job["rel"])
            for artifact in self.lb.rglob("*.olean"):
                archive.add(artifact, arcname=".lbuild/" + str(artifact.relative_to(self.lb)))
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
                self.assertEqual(set(setup["importArts"]),
                                 expected_artifacts or {"Sheaf.A", "Sheaf.B"})
            if "-o" in command:
                Path(command[command.index("-o") + 1]).write_bytes(src.read_bytes())
            return subprocess.CompletedProcess(command, 0, "", "")

        with patch("pathlib.Path.home", return_value=self.home), \
             patch.dict(os.environ, {"SHEAF_FILE_RUN_LIMIT": "60"}), \
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

    def test_service_compiles_completed_landing_and_reports_provenance(self):
        self.landing("Sheaf/B.lean", "module\n-- completed repair\n")
        reply, calls = self.service()
        self.assertEqual(calls, ["B", "A", "Test"])
        self.assertEqual(reply["results"][0]["rc"], 0)
        self.assertIn("+landing:20261022T051844-L-1", reply["results"][0]["out"])
        self.assertEqual(list(self.pub.rglob("*.olean")),
                         [self.pub / "Sheaf/Published.olean"])

    def test_service_overrides_old_owner_through_published_importer(self):
        self.relocated_definition()
        expected = {"Sheaf.Data", "Sheaf.B"}
        reply, calls = self.service(expected_artifacts=expected)
        self.assertEqual(calls, ["Data", "B", "Test"])
        self.assertEqual(reply["results"][0]["rc"], 0)
        reply, calls = self.service(expected_artifacts=expected)
        self.assertEqual(calls, ["Test"])
        self.assertIn("(cache)", reply["results"][0]["out"])

    def test_service_interleaves_requested_owner_and_rebuilt_importer(self):
        self.requested_relocation()
        expected = {"Sheaf.Data", "Sheaf.A", "Sheaf.B"}
        reply, calls = self.service(expected_artifacts=expected)
        self.assertEqual(calls, ["Data", "A", "B", "Test"])
        self.assertEqual([r["rel"] for r in reply["results"]],
                         ["Sheaf/Data.lean", "Sheaf/B.lean", "Test.lean"])
        self.assertTrue(all(r["rc"] == 0 for r in reply["results"]))
        reply, calls = self.service(expected_artifacts=expected)
        self.assertEqual(calls, ["Test"])
        self.assertTrue(all(r["rc"] == 0 for r in reply["results"]))

    def test_service_rebuilds_importers_of_caller_new_owner(self):
        self.requested_relocation()
        self.jobs = self.jobs[-1:]
        artifact = self.lb / "Sheaf/Data.olean"
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b"caller new owner")
        reply, calls = self.service(expected_artifacts={"Sheaf.Data", "Sheaf.A", "Sheaf.B"})
        self.assertEqual(calls, ["A", "B", "Test"])
        self.assertEqual(reply["results"][0]["rc"], 0)

    def test_service_preserves_manifest_result_order_after_scheduling(self):
        self.requested_relocation()
        self.jobs = self.jobs[-1:] + self.jobs[:-1]
        expected = {"Sheaf.Data", "Sheaf.A", "Sheaf.B"}
        reply, calls = self.service(expected_artifacts=expected)
        self.assertEqual(calls, ["Data", "A", "B", "Test"])
        self.assertEqual([r["rel"] for r in reply["results"]],
                         [job["rel"] for job in self.jobs])

    def test_rebuilt_importer_failure_reaches_requested_jobs(self):
        self.requested_relocation()
        reply, calls = self.service(failure="A")
        self.assertEqual(calls, ["Data", "A"])
        self.assertEqual([r["rel"] for r in reply["results"]],
                         [job["rel"] for job in self.jobs])
        self.assertTrue(all(r["rc"] == 1 for r in reply["results"]))
        self.assertIn("Dependency Sheaf.A", reply["results"][0]["out"])

    def test_service_keeps_failure_positions_when_reordered_job_stops_request(self):
        self.requested_relocation()
        self.jobs = self.jobs[-1:] + self.jobs[:-1]
        reply, calls = self.service(failure="B", stop_on_fail=True)
        self.assertEqual(calls, ["Data", "A", "B"])
        self.assertEqual([r["rel"] for r in reply["results"]],
                         [job["rel"] for job in self.jobs])
        self.assertEqual([r["rc"] for r in reply["results"]], [1, 0, 1])
        self.assertIn("NOT compiled", reply["results"][0]["out"])
        self.assertIn("error: dependency failed", reply["results"][0]["out"])
        self.assertIn("error: dependency failed", reply["results"][2]["out"])

    def test_service_keeps_imports_after_wrapped_public_import(self):
        self.source("Sheaf/A.lean", "module\npublic import\n  Sheaf.B\n"
                    "public import Sheaf.C -- import Sheaf.NotADependency\n"
                    "/- outer /- nested -/\nimport Sheaf.AlsoNotADependency\n-/\n"
                    'def message := "import Sheaf.NotASource"\n')
        self.source("Sheaf/C.lean", "module\nimport Sheaf.Published\n")
        subprocess.run(["git", "add", "lean/Sheaf/A.lean", "lean/Sheaf/C.lean"],
                       cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "-qm", "wrapped import fixture"], cwd=self.repo, check=True)
        expected = {"Sheaf.A", "Sheaf.B", "Sheaf.C"}
        reply, calls = self.service(expected_artifacts=expected)
        self.assertEqual(calls, ["B", "C", "A", "Test"])
        self.assertEqual(reply["results"][0]["rc"], 0)
        reply, calls = self.service(expected_artifacts=expected)
        self.assertEqual(calls, ["Test"])
        self.assertIn("(cache)", reply["results"][0]["out"])

    def test_dependency_error_is_returned_for_requested_job(self):
        reply, calls = self.service(failure="B")
        self.assertEqual(calls, ["B"])
        self.assertEqual(reply["results"][0]["rc"], 1)
        self.assertIn("Dependency Sheaf.B", reply["results"][0]["out"])
        self.assertIn("error: dependency failed", reply["results"][0]["out"])


if __name__ == "__main__":
    unittest.main()
