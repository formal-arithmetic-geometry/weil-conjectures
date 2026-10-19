"""Exercise the real batch citation check on temporary Git delivery trees.

Run from the project root: python3 tools/test_nt_land_batch_citations.py
No project imports, server calls, commits in the project, or Lean compilation.
"""
import ast
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest


SOURCE = Path(__file__).with_name("nt_land_batch.py")


class CitationCheck(unittest.TestCase):
    def setUp(self):
        self.tmp = TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.git("init", "-q")
        self.dep = "dag/nodes/chapter/dependency.json"
        self.other = "dag/nodes/chapter/other.json"
        self.item = "dag/nodes/chapter/item.json"
        self.child = "dag/nodes/chapter/reviewer-child.json"
        self.write(self.dep, {"statement": "original dependency"})
        self.write(self.other, {"statement": "original other"})
        self.write(self.item, {"stmt_deps": ["dependency"]})
        self.git("add", "--", self.dep, self.other, self.item)
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "-qm", "delivery")
        self.git("branch", "delivery")

        def load(ref, rel):
            return json.loads(self.git("show", f"{ref}:{rel}"))

        def exists(ref, rel):
            return subprocess.run(["git", "cat-file", "-e", f"{ref}:{rel}"],
                                  cwd=self.root, capture_output=True).returncode == 0

        class Fail(Exception):
            pass

        self.fail = Fail
        md = SimpleNamespace(load_json_at=load, exists_at=exists, Fail=Fail,
                             node_path=lambda nid: f"dag/nodes/chapter/{nid}.json")
        dag_queue = SimpleNamespace(deps_of=lambda n, _: n.get("stmt_deps", []))
        namespace = {"json": json, "P": self.root, "md": md, "dag_queue": dag_queue}
        tree = ast.parse(SOURCE.read_text())
        function = next(n for n in tree.body
                        if isinstance(n, ast.FunctionDef) and n.name == "cited_check")
        exec(compile(ast.Module(body=[function], type_ignores=[]), str(SOURCE), "exec"),
             namespace)
        self.check = namespace["cited_check"]
        self.delivery = {"br": "delivery", "head": "this",
                         "kinds": {self.item: "item"}, "ids": {"item"}}

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, check=True,
                              capture_output=True, text=True).stdout.strip()

    def write(self, rel, node):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(node))

    def change_head(self, rel):
        self.write(rel, {"statement": "changed after review"})
        self.git("add", "--", rel)
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "-qm", "current main")

    def add_reviewer_child(self):
        self.delivery["kinds"][self.child] = "new"
        self.delivery["ids"].add("reviewer-child")
        self.write(self.item, {"stmt_deps": ["reviewer-child"]})
        self.write(self.child, {"stmt_deps": ["dependency"]})

    def test_reviewer_added_node_absent_from_delivery_branch(self):
        self.add_reviewer_child()
        self.check(self.delivery, {})

    def test_reviewer_added_node_still_checks_its_external_citations(self):
        self.add_reviewer_child()
        self.change_head(self.dep)
        with self.assertRaisesRegex(self.fail, "cited node dependency: statement changed"):
            self.check(self.delivery, {})

    def test_reviewer_removed_stale_citation_does_not_refuse_repair(self):
        self.change_head(self.dep)
        self.write(self.item, {"stmt_deps": ["other"]})
        self.check(self.delivery, {})

    def test_reviewer_added_existing_citation_is_checked(self):
        self.change_head(self.other)
        self.write(self.item, {"stmt_deps": ["other"]})
        with self.assertRaisesRegex(self.fail, "cited node other: statement changed"):
            self.check(self.delivery, {})

    def test_unchanged_delivery_stale_citation_still_refused(self):
        self.change_head(self.dep)
        with self.assertRaisesRegex(self.fail, "cited node dependency: statement changed"):
            self.check(self.delivery, {})

    def test_earlier_batch_change_is_seen(self):
        self.write(self.dep, {"statement": "earlier batch delivery"})
        with self.assertRaisesRegex(self.fail, "cited node dependency: statement changed"):
            self.check(self.delivery, {self.dep: "earlier"}, {"earlier": 0, "this": 1})

    def test_later_batch_change_does_not_refuse_current_delivery(self):
        self.write(self.dep, {"statement": "later batch delivery"})
        self.check(self.delivery, {self.dep: "later"}, {"this": 0, "later": 1})


if __name__ == "__main__":
    unittest.main()
