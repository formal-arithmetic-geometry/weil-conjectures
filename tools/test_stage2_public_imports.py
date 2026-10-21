"""Public-import superset records, including immutable delivery sources; no Lean build."""
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import stage2_delivery as s2

ITEM = "def-maint-public-import"
DEPENDENCY = "def-maint-public-provider"
PROVIDER = "Sheaf.Fixture.Provider"
MODULE = "Sheaf.Fixture.Consumer"
NODE = "dag/nodes/sec-fixture/" + ITEM + ".json"
DEP_NODE = "dag/nodes/sec-fixture/" + DEPENDENCY + ".json"
CONSUMER_PATH = "lean/" + MODULE.replace(".", "/") + ".lean"
PROVIDER_PATH = "lean/" + PROVIDER.replace(".", "/") + ".lean"


def consumer(imports):
    return ("module\n" + imports + "\nnamespace Fixture\n"
            f"/-- Source: fixture (blueprint: {ITEM}). -/\n"
            "public def consumer : Nat := 0\nend Fixture\n")


def provider(body="public def supplied : Nat := 0\n", imports=""):
    return "module\n" + imports + "\nnamespace Fixture\n" + body + "end Fixture\n"


def record(module, declaration):
    return {"module": module, "file": "lean/" + module.replace(".", "/") + ".lean",
            "declaration": declaration, "statement": "def " + declaration.split(".")[-1] + " : Nat",
            "branch": "sheaf-dag", "by": "NP", "date": "2026-10-21", "existing": False}


class PublicImports(unittest.TestCase):
    def check(self, text, sources, name="Fixture.supplied"):
        rec = record(MODULE, "Fixture.consumer")
        rec["declarations"] = ["Fixture.consumer", name]
        with patch.object(s2, "upstream_has", return_value=None):
            return s2.check_lean_text(text, rec, ITEM, read_module=sources.get)[0]

    def test_public_project_import(self):
        self.assertEqual(self.check(consumer("public import " + PROVIDER),
                                    {PROVIDER: provider()}), [])

    def test_transitive_public_import(self):
        self.assertEqual(self.check(consumer("public import Sheaf.Fixture.Bridge"), {
            "Sheaf.Fixture.Bridge": "module\npublic import " + PROVIDER + "\n",
            PROVIDER: provider()}), [])

    def test_ordinary_import_is_not_reexported(self):
        self.assertTrue(self.check(consumer("import " + PROVIDER), {PROVIDER: provider()}))

    def test_private_transitive_import_is_not_reexported(self):
        self.assertTrue(self.check(consumer("public import Sheaf.Fixture.Bridge"), {
            "Sheaf.Fixture.Bridge": "module\nimport " + PROVIDER + "\n",
            PROVIDER: provider()}))

    def test_legacy_import_reexports_public_declarations(self):
        legacy = consumer("import " + PROVIDER).removeprefix("module\n")
        self.assertEqual(self.check(legacy, {PROVIDER: provider()}), [])

    def test_public_section(self):
        self.assertEqual(self.check(consumer("public import " + PROVIDER),
            {PROVIDER: provider("@[expose] public section\ndef supplied : Nat := 0\nend\n")}), [])

    def test_default_private_declaration(self):
        self.assertTrue(self.check(consumer("public import " + PROVIDER),
                                  {PROVIDER: provider("def supplied : Nat := 0\n")}))

    def test_explicit_private_in_public_section(self):
        self.assertTrue(self.check(consumer("public import " + PROVIDER),
            {PROVIDER: provider("public section\nprivate def supplied : Nat := 0\nend\n")}))

    def test_nested_private_section(self):
        self.assertTrue(self.check(consumer("public import " + PROVIDER),
            {PROVIDER: provider("public section\nprivate section\n"
                                "def supplied : Nat := 0\nend\nend\n")}))

    def test_public_visibility_restored_after_section(self):
        self.assertEqual(self.check(consumer("public import " + PROVIDER),
            {PROVIDER: provider("public section\nprivate section\nend\n"
                                "def supplied : Nat := 0\nend\n")}), [])

    def test_missing_and_unrelated_names_rejected(self):
        sources = {PROVIDER: provider(), "Sheaf.Fixture.Unimported":
                   provider("public def absent : Nat := 0\n")}
        self.assertTrue(self.check(consumer("public import " + PROVIDER), sources, "Fixture.absent"))

    def test_full_namespace_must_match(self):
        self.assertTrue(self.check(consumer("public import " + PROVIDER),
                                  {PROVIDER: provider()}, "Wrong.supplied"))

    def test_missing_tree_source_does_not_fall_back_to_live(self):
        with patch.object(s2, "existing_file", side_effect=AssertionError("mutable fallback")):
            self.assertTrue(self.check(consumer("public import " + PROVIDER), {}))

    def test_commented_import_does_not_export(self):
        self.assertTrue(self.check(consumer("/- public import " + PROVIDER + " -/"),
                                  {PROVIDER: provider()}))

    def test_cycle_terminates_and_missing_name_still_fails(self):
        self.assertTrue(self.check(consumer("public import " + PROVIDER),
            {PROVIDER: provider(imports="public import Sheaf.Fixture.Loop\n"),
             "Sheaf.Fixture.Loop": "module\npublic import " + PROVIDER + "\n"}, "Fixture.absent"))

    def test_primary_declaration_must_still_be_local(self):
        rec = record(MODULE, "Fixture.supplied")
        with patch.object(s2, "upstream_has", return_value=None):
            failures, _ = s2.check_lean_text(consumer("public import " + PROVIDER), rec, ITEM,
                                           read_module={PROVIDER: provider()}.get)
        self.assertTrue(any("is not declared in the file" in message for _, message in failures))


class DeliveryTree(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="stage2-public-imports-")
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.git("init", "-q")
        self.write("coord/.merge.lock", "")
        self.write(NODE, json.dumps({"id": ITEM, "kind": "definition", "status": "split",
                                    "statement": "Fixture.", "stmt_deps": [DEPENDENCY],
                                    "proof_deps": []}))
        self.write(DEP_NODE, json.dumps({"id": DEPENDENCY, "kind": "definition", "status": "split",
                                        "statement": "Provider.", "stmt_deps": [], "proof_deps": []}))
        self.write(PROVIDER_PATH, provider("public def old : Nat := 0\n"))
        self.commit([NODE, DEP_NODE, PROVIDER_PATH], "base")
        self.git("branch", "sheaf-dag")
        rec = record(MODULE, "Fixture.consumer")
        rec["declarations"] = ["Fixture.consumer", "Fixture.supplied"]
        node = json.loads((self.root / NODE).read_text())
        node["lean"] = rec
        self.write(NODE, json.dumps(node))
        dep = json.loads((self.root / DEP_NODE).read_text())
        dep["lean"] = record(PROVIDER, "Fixture.supplied")
        dep["lean"]["note"] = "Supply the missing dependency interface."
        self.write(DEP_NODE, json.dumps(dep))
        self.write(CONSUMER_PATH, consumer("public import " + PROVIDER))
        self.source = provider(f"/-- Source: fixture (blueprint: {DEPENDENCY}). -/\n"
                               "public def supplied : Nat := 0\n")
        self.write(PROVIDER_PATH, self.source)
        self.report = "coord/reports/NP/" + ITEM + ".md"
        self.write(self.report, "## Worker report\nFixture.\n\n## Second reading by NP\nChecked.\n"
                               f"\n## Dependency modules\n{DEPENDENCY}: supply the missing interface.\n")
        self.commit([NODE, DEP_NODE, CONSUMER_PATH, PROVIDER_PATH, self.report], "delivery")

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True).strip()

    def commit(self, paths, message):
        self.git("add", "--", *paths)
        subprocess.run(["flock", "coord/.merge.lock", "git", "-c", "user.name=Bin Wu",
                        "-c", "user.email=844524296@qq.com", "commit", "-qm", message],
                       cwd=self.root, env=dict(os.environ, SHEAF_LEAD="L-only"), check=True)

    def write(self, rel, text):
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def read(self, overrides=None):
        with patch.object(s2, "upstream_has", return_value=None):
            return s2.read_delivery(s2.Git(self.root), "HEAD", "sheaf-dag", "NP", ITEM,
                                    overrides=overrides)

    def test_sibling_definition_comes_from_delivery_tree(self):
        self.assertEqual(self.read()["fails"], [])

    def test_mutable_checkout_does_not_override_delivery_tree(self):
        self.write(PROVIDER_PATH, "module\n")
        self.assertEqual(self.read()["fails"], [])

    def test_reviewer_override_controls_export_resolution(self):
        changed = self.source.replace("public def", "private def")
        failures = self.read({PROVIDER_PATH: changed})["fails"]
        self.assertTrue(any("lean.declarations names Fixture.supplied" in message
                            for _, message in failures), failures)


if __name__ == "__main__":
    unittest.main()
