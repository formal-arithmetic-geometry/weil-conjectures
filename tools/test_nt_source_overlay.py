"""Regressions for private source selection over stale existing artifacts."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import nt_source_overlay as overlay


LEGACY = '''/- Original documentation. -/
import Mathlib.Data.Nat.Basic

set_option autoImplicit false

def value : Nat := 1
'''
CONVERTED = LEGACY.replace(
    'import Mathlib', 'module\n\npublic import Mathlib', 1).replace(
        'set_option', '@[expose] public section\n\nset_option', 1)


class HeaderConversionTests(unittest.TestCase):
    def test_exact_conversion(self):
        self.assertTrue(overlay._header_conversion(LEGACY, CONVERTED))

    def test_rejects_changes_to_declarations_and_documentation(self):
        for altered in (
            CONVERTED.replace(':= 1', ':= 2'),
            CONVERTED.replace('value : Nat', 'value : Int'),
            CONVERTED.replace('Original documentation', 'Changed documentation'),
            CONVERTED + '\ndef extra : Nat := 0\n',
            CONVERTED.replace('Mathlib.Data.Nat.Basic', 'Mathlib.Data.Int.Basic'),
        ):
            with self.subTest(altered=altered):
                self.assertFalse(overlay._header_conversion(LEGACY, altered))
        self.assertFalse(overlay._header_conversion(CONVERTED, CONVERTED))
        self.assertFalse(overlay._header_conversion(LEGACY, LEGACY))

    def test_preserves_blank_lines_in_data(self):
        before = LEGACY + '\ndef text : String := "a\n\nb"\n'
        after = CONVERTED + '\ndef text : String := "a\nb"\n'
        self.assertFalse(overlay._header_conversion(before, after))


class SourceSelectionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.lean = self.root / 'lean'
        self.rel = 'Sheaf/Test/Legacy.lean'
        self.source = self.lean / self.rel
        self.source.parent.mkdir(parents=True)
        self.source.write_text(LEGACY)
        (self.lean / 'lakefile.toml').write_text('name = "test"\n')
        artifact = self.lean / '.lake/build/lib/lean/Sheaf/Test/Legacy.olean'
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b'published legacy artifact')
        self.git('init', '-q')
        self.git('add', 'lean/Sheaf/Test/Legacy.lean', 'lean/lakefile.toml')
        self.commit()
        self.published = self.git('rev-parse', 'HEAD').strip()
        (self.root / 'local/builds').mkdir(parents=True)
        self.publish(self.published)
        overlay._HEADER_CONVERSIONS.clear()
        overlay._UNBUILT.clear()
        overlay._COMMITTED_ADDITIONS.clear()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True,
                                       stderr=subprocess.PIPE)

    def commit(self):
        self.git('-c', 'user.name=Bin Wu', '-c', 'user.email=844524296@qq.com',
                 'commit', '-qm', 'fixture')

    def publish(self, commit):
        (self.root / 'local/builds/published.json').write_text(json.dumps({'commit': commit}))

    def convert(self, text=CONVERTED):
        self.source.write_text(text)
        self.git('add', 'lean/Sheaf/Test/Legacy.lean')
        self.commit()

    def test_both_compilers_select_header_conversion_with_existing_artifact(self):
        self.convert()
        self.assertEqual(overlay.source_for_import(self.root, self.lean, self.rel), self.source)
        self.assertEqual(overlay.overlay_sources(self.root, self.lean)[self.rel], CONVERTED.encode())

    def test_committed_mathematical_change_is_compiled_from_source(self):
        # 2026-10-25 (deliverfix; the human): a stale publication is a tool bug; a committed modification since the
        # last green publication is compiled privately from its committed source
        self.convert(CONVERTED.replace(':= 1', ':= 2'))
        self.assertEqual(overlay.source_for_import(self.root, self.lean, self.rel), self.source)
        self.assertIn(self.rel, overlay.overlay_sources(self.root, self.lean))

    def test_uncommitted_conversion_stays_on_published_artifact(self):
        self.source.write_text(CONVERTED)
        self.assertIsNone(overlay.source_for_import(self.root, self.lean, self.rel))

    def test_cached_conversion_rechecks_working_source(self):
        self.convert()
        self.assertIn(self.rel, overlay.module_header_conversions(self.lean))
        self.source.write_text(CONVERTED.replace(':= 1', ':= 2'))
        self.assertIsNone(overlay.source_for_import(self.root, self.lean, self.rel))
        self.source.write_text(CONVERTED)
        self.assertIn(self.rel, overlay.module_header_conversions(self.lean))

    def test_new_publication_retires_private_conversion(self):
        self.convert()
        self.assertIn(self.rel, overlay.module_header_conversions(self.lean))
        self.publish(self.git('rev-parse', 'HEAD').strip())
        self.assertIsNone(overlay.source_for_import(self.root, self.lean, self.rel))


    def add_module(self, commit=True, symlink=False):
        rel = 'Sheaf/Test/NewModule.lean'
        source = self.lean / rel
        source.write_text(CONVERTED)
        artifact = self.lean / '.lake/build/lib/lean/Sheaf/Test/NewModule.olean'
        if symlink:
            old_cache = self.root / 'old-cache.olean'
            old_cache.write_bytes(b'obsolete private artifact')
            artifact.symlink_to(old_cache)
        else:
            artifact.write_bytes(b'obsolete private artifact')
        if commit:
            self.git('add', 'lean/' + rel)
            self.commit()
        return rel, source, artifact

    def assert_selected(self, rel, source):
        self.assertEqual(overlay.source_for_import(self.root, self.lean, rel), source)
        self.assertEqual(overlay.overlay_sources(self.root, self.lean)[rel], CONVERTED.encode())

    def assert_published(self, rel):
        self.assertIsNone(overlay.source_for_import(self.root, self.lean, rel))
        self.assertNotIn(rel, overlay.overlay_sources(self.root, self.lean))

    def test_committed_addition_with_leftover_artifact(self):
        self.assertEqual(overlay.committed_additions(self.lean), frozenset())
        rel, source, artifact = self.add_module()
        self.assert_selected(rel, source)
        self.assertEqual(artifact.read_bytes(), b'obsolete private artifact')

    def test_committed_addition_with_old_cache_symlink(self):
        rel, source, artifact = self.add_module(symlink=True)
        self.assert_selected(rel, source)
        self.assertTrue(artifact.is_symlink())

    def test_first_snapshot_selects_all_committed_additions(self):
        rel, source, _ = self.add_module()
        other = source.with_name('ZZLater.lean')
        other.write_text(CONVERTED)
        self.git('add', str(other.relative_to(self.root)))
        self.commit()
        snapshot = overlay.overlay_sources(self.root, self.lean)
        self.assertEqual(snapshot[rel], CONVERTED.encode())
        self.assertIn('Sheaf/Test/ZZLater.lean', snapshot)

    def test_addition_and_committed_modification_both_selected(self):
        self.convert(CONVERTED.replace(':= 1', ':= 2'))
        self.add_module()
        self.assertEqual(overlay.source_for_import(self.root, self.lean, self.rel), self.source)

    def test_uncommitted_addition_is_not_selected_over_artifact(self):
        rel, _, _ = self.add_module(commit=False)
        self.assert_published(rel)

    def test_cached_addition_rechecks_working_source(self):
        rel, source, _ = self.add_module()
        self.assert_selected(rel, source)
        source.write_text(CONVERTED.replace(':= 1', ':= 2'))
        self.assert_published(rel)
        source.write_text(CONVERTED)
        self.assert_selected(rel, source)

    def test_publication_retires_private_addition(self):
        rel, source, _ = self.add_module()
        self.assert_selected(rel, source)
        self.publish(self.git('rev-parse', 'HEAD').strip())
        self.assert_published(rel)


if __name__ == '__main__':
    unittest.main()
