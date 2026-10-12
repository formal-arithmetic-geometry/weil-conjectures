"""Regression tests for the maintainers' section and protected-layer rules."""
import contextlib
import io
import json
import pathlib
import tempfile
import types
import unittest
import blueprint_pr as bp


class RulesTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name)
        self.baseline = {}
        for rel, ident in [('blueprint/sec-a/_section.md', 'sec-a'),
                           ('blueprint/sec-a/sk-a/_section.md', 'sk-a'),
                           ('blueprint/sec-a/sk-a/lem-a.md', 'lem-a')]:
            text = bp.fields({'id': ident, 'kind': 'lemma'}) + 'A statement.\n'
            bp.write(self.root / rel, text)
            self.baseline[rel] = text
        bp.write(self.root / '.blueprint-cut.json', json.dumps({'baseline': self.baseline}))

    def check(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = bp.check(types.SimpleNamespace(dir=str(self.root)))
        return code, output.getvalue()

    def add(self, rel, ident='lem-b', body='A statement.'):
        bp.write(self.root / rel, bp.fields({'id': ident, 'kind': 'lemma'}) + body + '\n')

    def test_flat_refinement_passes(self):
        self.add('blueprint/sec-a/sk-a/lem-b.md')
        self.assertEqual(self.check()[0], 0)

    def test_new_folder_without_section_fails(self):
        self.add('blueprint/sec-a/sk-a/lem-b/lem-c.md', 'lem-c')
        self.assertIn('new section missing _section.md', self.check()[1])

    def test_deep_section_with_statement_passes(self):
        self.add('blueprint/sec-a/sk-a/lem-b/_section.md')
        self.add('blueprint/sec-a/sk-a/lem-b/lem-c.md', 'lem-c')
        self.assertEqual(self.check()[0], 0)

    def test_empty_section_fails(self):
        self.add('blueprint/sec-a/sk-a/lem-b/_section.md', body='')
        self.assertIn('section must hold its statement', self.check()[1])

    def test_second_layer_edit_fails(self):
        self.add('blueprint/sec-a/sk-a/_section.md', 'sk-a', 'Changed statement.')
        self.assertIn('protected layer changed', self.check()[1])

    def test_second_layer_addition_fails(self):
        self.add('blueprint/sec-a/sk-b/_section.md', 'sk-b')
        self.assertIn('protected layer changed', self.check()[1])

    def test_chapter_addition_fails(self):
        self.add('blueprint/sec-b/_section.md', 'sec-b')
        self.assertIn('protected layer changed', self.check()[1])

    def test_second_layer_proof_edit_fails(self):
        bp.write(self.root / 'blueprint/sec-a/sk-a/sk-a.proof.md', bp.fields({'kind': 'proof', 'of': 'sk-a'}) + 'Proof.')
        self.assertIn('protected layer changed', self.check()[1])

    def test_statement_removal_fails(self):
        (self.root / 'blueprint/sec-a/sk-a/lem-a.md').unlink()
        self.assertIn('blueprint file removed', self.check()[1])

    def test_missing_dependency_fails(self):
        bp.write(self.root / 'blueprint/sec-a/sk-a/lem-b.md', bp.fields({'id': 'lem-b', 'kind': 'lemma', 'uses': ['lem-absent']}) + 'Statement.')
        self.assertIn('missing dependency lem-absent', self.check()[1])


class CitationTests(unittest.TestCase):
    def setUp(self):
        self.nodes = {'lem-leaf': {'status': 'mathlib', 'blueprint': {'is': None},
            'mathlib_match': {'declaration': 'A.foo, B.bar (instances)',
                             'file': 'Mathlib/A.lean, Mathlib/B.lean'}}}

    def test_multiple_mathlib_sources_have_individual_urls(self):
        text = bp.rendered('[lem-leaf]', self.nodes)
        self.assertIn('blob/master/Mathlib/A.lean)', text)
        self.assertIn('blob/master/Mathlib/B.lean)', text)
        self.assertNotIn('.lean, Mathlib/', text)
        self.assertNotIn('[lem-leaf]', text)

    def test_grouped_citation_resolves_each_leaf(self):
        text = bp.rendered('[lem-internal, lem-leaf]', self.nodes)
        self.assertTrue(text.startswith('[lem-internal], `A.foo'))
        self.assertNotIn('lem-leaf', text)

    def test_imported_mathlib_node_keeps_internal_reference(self):
        self.nodes['lem-leaf']['blueprint']['is'] = 'lem-leaf'
        self.assertEqual(bp.rendered('[lem-leaf]', self.nodes), '[lem-leaf]')

    def test_mathlib_leaf_removed_from_structural_dependencies(self):
        self.assertEqual(bp.dependencies(['lem-leaf', 'lem-other'], self.nodes), ['lem-other'])


if __name__ == '__main__':
    unittest.main()
