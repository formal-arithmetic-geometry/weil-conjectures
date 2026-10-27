"""Read-only regression and real-packet replay for a protected landing checker.

Run from this evidence directory: python3 verify-cycle-gate.py
The proposed change runs only in memory. No tool, node, module or branch changes.
"""

import ast
import copy
import gzip
import importlib.util
import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parent
SOURCE = (ROOT / "stage3_delivery.py.bak").read_text()
TREE = ast.parse(SOURCE)
FUNCTION = next(n for n in TREE.body if isinstance(n, ast.FunctionDef) and n.name == "edge_fails")
ORIGINAL = ast.get_source_segment(SOURCE, FUNCTION)
SPEC = importlib.util.spec_from_file_location("proposed", ROOT / "proposed-cycle-gate.py")
PROPOSED = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROPOSED)
OLD = "not (reaches(base_graph, c, nid) and reaches(base_graph, nid, c))"
NEW = "not inherited_through_helpers(graph, base_graph, nid, c, reaches)"
assert ORIGINAL.count(OLD) == 1


def load_checker(source):
    namespace = {"inherited_through_helpers": PROPOSED.inherited_through_helpers}
    exec(compile(source, "<isolated edge_fails>", "exec"), namespace)
    return namespace["edge_fails"]


CURRENT = load_checker(ORIGINAL)
CANDIDATE = load_checker(ORIGINAL.replace(OLD, NEW))


def nodes(graph):
    return {k: {"stmt_deps": [], "proof_deps": list(v)} for k, v in graph.items()}


def delivery(base, edits):
    return {"nodes": {k: {"role": "changed" if k in base else "new",
                         "base_node": base.get(k), "node": v, "path": k + ".json"}
                      for k, v in edits.items()}}


class CycleTests(unittest.TestCase):
    def check_graph(self, base, edits, rejects):
        baseline = nodes(base)
        packet = delivery(baseline, nodes(edits))
        saved = copy.deepcopy((baseline, packet))
        self.assertEqual(bool(CANDIDATE(packet, baseline)), rejects)
        self.assertEqual((baseline, packet), saved)

    def test_baseline_bug_reproduces(self):
        base = nodes({"a": ["b"], "b": ["a"]})
        packet = delivery(base, nodes({"a": ["helper"], "helper": ["b"]}))
        self.assertEqual(len(CURRENT(packet, base)), 1)
        self.assertEqual(CANDIDATE(packet, base), [])

    def test_split_with_helper_chain(self):
        self.check_graph({"a": ["b"], "b": ["a"]},
                         {"a": ["h1"], "h1": ["h2"], "h2": ["b"]}, False)

    def test_acyclic_split(self):
        self.check_graph({"a": ["b"], "b": []},
                         {"a": ["helper"], "helper": ["b"]}, False)

    def test_existing_baseline_cycle_still_allowed(self):
        self.check_graph({"a": ["b"], "b": ["c"], "c": ["a"]},
                         {"a": ["b", "c"]}, False)

    def test_new_backedge_still_rejected(self):
        self.check_graph({"a": ["b"], "b": []}, {"b": ["a"]}, True)

    def test_new_cycle_through_helper_still_rejected(self):
        self.check_graph({"a": [], "b": ["a"]},
                         {"a": ["helper"], "helper": ["b"]}, True)

    def test_self_edge_still_rejected(self):
        self.check_graph({"a": []}, {"a": ["a"]}, True)

    def test_missing_dependency_still_rejected(self):
        self.check_graph({"a": []}, {"a": ["missing"]}, True)

    def test_direct_helper_return_to_parent_rejected(self):
        self.check_graph({"a": ["b"], "b": ["a"]},
                         {"a": ["helper"], "helper": ["a"]}, True)

    def test_helper_only_cycle_not_hidden(self):
        self.check_graph({"a": ["b"], "b": ["a"]},
                         {"a": ["h1"], "h1": ["h2", "b"], "h2": ["h1"]}, True)

    def test_new_baseline_component_cannot_join_old_cycle(self):
        self.check_graph({"a": ["b"], "b": ["a"], "c": ["a"]},
                         {"a": ["helper"], "helper": ["b", "c"]}, True)

    def test_nonreturning_extra_dependency_allowed(self):
        self.check_graph({"a": ["b"], "b": ["a"], "c": []},
                         {"a": ["helper"], "helper": ["b", "c"]}, False)

    def test_statement_edge_has_same_protection(self):
        baseline = nodes({"a": ["b"], "b": ["a"]})
        edits = nodes({"a": [], "helper": ["b"]})
        edits["a"]["stmt_deps"] = ["helper"]
        packet = delivery(baseline, edits)
        self.assertEqual(len(CURRENT(packet, baseline)), 1)
        self.assertEqual(CANDIDATE(packet, baseline), [])

    def test_actual_packet(self):
        snapshot = json.loads(gzip.decompress((ROOT / "baseline-graph.json.gz").read_bytes()))
        baseline = snapshot["nodes"]
        packet = json.loads((ROOT / "packet-nodes.json").read_text())
        for k, v in packet.items():
            v.update(role="changed" if k in baseline else "new", base_node=baseline.get(k))
        data = {"nodes": packet}
        current = CURRENT(data, baseline)
        candidate = CANDIDATE(data, baseline)
        self.assertEqual(len(current), 1)
        self.assertIn("lem-coef-system-total-enriched-transpose", current[0][1])
        self.assertEqual(candidate, [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
