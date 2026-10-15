"""Regression checks for reaching a sketch expanded in another blueprint unit."""
import copy
import unittest
from unittest.mock import patch

import units


class UnitBindingTests(unittest.TestCase):
    def setUp(self):
        self.nodes = {
            "item": {"id": "item", "kind": "statement", "chapter": "chapter",
                     "unit": "consumer", "stmt_deps": ["expansion"]},
            "expansion": {"id": "expansion", "kind": "statement", "chapter": "chapter",
                          "unit": "source", "stmt_deps": []},
            "auxiliary": {"id": "auxiliary", "kind": "statement", "chapter": "chapter",
                          "unit": "source", "stmt_deps": []},
        }
        self.records = {
            "consumer": {"uses": ["sketch"], "steps": [{"text": "consumer proof"}],
                         "realized": {"statement": ["item"], "steps": [["item"]]}},
            "sketch": {"uses": [], "steps": [{"text": "sketch proof"}],
                       "realized": {"statement": [], "steps": [[]]}},
            "source": {"uses": [], "steps": []},
        }

    def findings(self):
        with patch.object(units, "load_units", return_value=(self.records, {"chapter": {}})), \
                patch.object(units.dq.li, "config", return_value={}):
            return units.check(self.nodes, verbose=False)

    def bind(self):
        self.records["sketch"]["realized"] = {
            "statement": ["expansion"], "steps": [["expansion"]]}

    def test_unbound_sketch_still_fails(self):
        self.assertIn("units: consumer cites sketch, which its nodes do not reach", self.findings())

    def test_cross_unit_expansion_satisfies_consumer(self):
        self.bind()
        self.assertEqual(self.findings(), [])
        self.assertEqual(self.nodes["expansion"]["unit"], "source")

    def test_unreached_proof_carrier_still_fails(self):
        self.bind()
        self.records["sketch"]["realized"]["steps"] = [["auxiliary"]]
        self.assertIn("units: consumer cites sketch, which its nodes do not reach", self.findings())

    def test_all_carriers_reached_satisfies_consumer(self):
        self.bind()
        self.records["sketch"]["realized"]["steps"] = [["auxiliary"]]
        self.nodes["expansion"]["stmt_deps"] = ["auxiliary"]
        self.assertEqual(self.findings(), [])

    def test_incomplete_bindings_do_not_count(self):
        for realized in ({"statement": [], "steps": [["expansion"]]},
                         {"statement": ["expansion"], "steps": [[]]},
                         {"statement": ["expansion"], "steps": []}):
            with self.subTest(realized=realized):
                self.records["sketch"]["realized"] = copy.deepcopy(realized)
                self.assertIn("units: consumer cites sketch, which its nodes do not reach", self.findings())

    def test_missing_carrier_still_fails(self):
        self.bind()
        self.records["sketch"]["realized"]["statement"] = ["missing"]
        errors = self.findings()
        self.assertIn("units: sketch is realized by missing, no such node", errors)
        self.assertIn("units: consumer cites sketch, which its nodes do not reach", errors)

    def test_source_unit_reachability_is_preserved(self):
        self.records["consumer"]["uses"] = ["source"]
        self.assertEqual(self.findings(), [])


if __name__ == "__main__":
    unittest.main()
