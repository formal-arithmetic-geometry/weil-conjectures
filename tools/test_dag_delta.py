"""Stage-1 preflight and landing share the advisory-route policy."""
import unittest

import dag_delta


ITEM = 'fin2-lem-lisse-dense-open'
ROUTE = ('route: lem-fin-constructible-devissage (sk-prop-sf-cbc) depends on '
         'fin2-lem-lisse-dense-open (sk-p-real-purity), outside its unit\'s route')


class DeliveryFindingsTests(unittest.TestCase):
    def check_findings(self, current, baseline=''):
        return dag_delta.delivery_findings(current, baseline, {ITEM})

    def test_returned_incoming_route_is_advisory_even_when_inherited(self):
        # check_dag emits this edge twice; introduced deliberately retains it
        # because its dependency is the delivered item, even on the baseline.
        output = ROUTE + '\n' + ROUTE
        self.assertEqual(dag_delta.introduced(output, output, {ITEM}), [ROUTE, ROUTE])
        self.assertEqual(self.check_findings(output, output), ([], [ROUTE, ROUTE]))

    def test_new_incoming_route_is_recorded(self):
        self.assertEqual(self.check_findings(ROUTE), ([], [ROUTE]))

    def test_cycles_and_missing_dependencies_still_block_with_a_route_notice(self):
        cycle = 'cycles: ' + ITEM + ' -> lem-test-input -> ' + ITEM
        missing = 'deps: ' + ITEM + ' depends on missing-node'
        output = '\n'.join([ROUTE, cycle, missing])
        self.assertEqual(self.check_findings(output), ([cycle, missing], [ROUTE]))

    def test_inherited_missing_dependency_on_delivered_item_still_blocks(self):
        missing = 'deps: ' + ITEM + ' depends on missing-node'
        self.assertEqual(self.check_findings(missing, missing), ([missing], []))

    def test_new_unit_realization_error_still_blocks(self):
        error = 'units: sk-prop-sf-cbc cites sk-test-unit, which its nodes do not reach'
        self.assertEqual(self.check_findings(error), ([error], []))

    def test_unrelated_inherited_findings_remain_baseline(self):
        output = ('deps: lem-other-item depends on missing-node\n'
                  'route: lem-other-item (sk-test) depends on lem-other-input (sk-other), '
                  'outside its unit\'s route')
        self.assertEqual(self.check_findings(output, output), ([], []))


if __name__ == '__main__':
    unittest.main()
