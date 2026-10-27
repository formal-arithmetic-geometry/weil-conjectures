"""Regressions for nt_parallel2.overlay_index: moved/deleted declaration origins must not
count as duplicates, while genuine duplicates in current modules are still refused."""
import collections
import unittest

import nt_parallel2 as nt

li = nt.li
TEXT = 'namespace OverlayProbe\ntheorem relocation_probe : True := by trivial\nend OverlayProbe\n'
Q = 'OverlayProbe.relocation_probe'


def base_of(texts):
    """An index describing exactly the current modules in ``texts``."""
    base = nt.batch.SourceIndex()
    base.decls, base.statements = collections.defaultdict(set), collections.defaultdict(set)
    base.imports, base.by_module, base.loaded = {}, {}, True
    for mod, text in texts.items():
        names = li.decls_in_text(text)
        stmts = {(s, q) for q, s in li.statements_in_text(text).items() if s}
        base.by_module[mod] = [names, stmts]
        for q in names:
            base.decls[q].add(mod)
        for s, q in stmts:
            base.statements[s].add((q, mod))
        base.imports[mod] = li.imports_of(text)
    return base


def refused(index, mod, old, new):
    try:
        nt.prune(mod, old, new, index)
    except nt.md.Fail as exc:
        return 'already declare' in str(exc)
    return False


class OverlayIndexTests(unittest.TestCase):
    def test_move_between_delivered_modules_is_accepted(self):
        base = base_of({'Sheaf.ProbeA': TEXT})
        move = [{'module': 'Sheaf.ProbeA', 'text': ''}, {'module': 'Sheaf.ProbeB', 'text': TEXT}]
        cand = nt.overlay_index(base, move)
        self.assertEqual(cand.decls[Q], {'Sheaf.ProbeB'})
        self.assertFalse(any(m == 'Sheaf.ProbeA' for v in cand.statements.values() for _, m in v))
        self.assertFalse(refused(cand, 'Sheaf.ProbeB', '', TEXT))
        # the shared base is untouched (a rejected candidate never leaks)
        self.assertEqual(base.decls[Q], {'Sheaf.ProbeA'})

    def test_complete_deletion_masks_base(self):
        base = base_of({'Sheaf.ProbeA': TEXT})
        cand = nt.overlay_index(base, [{'module': 'Sheaf.ProbeA', 'text': ''}])
        self.assertEqual(cand.decls.get(Q, set()), set())

    def test_genuine_duplicate_in_untouched_module_is_refused(self):
        base = base_of({'Sheaf.ProbeA': TEXT, 'Sheaf.ProbeOther': TEXT})
        move = [{'module': 'Sheaf.ProbeA', 'text': ''}, {'module': 'Sheaf.ProbeB', 'text': TEXT}]
        cand = nt.overlay_index(base, move)
        self.assertEqual(cand.decls[Q], {'Sheaf.ProbeB', 'Sheaf.ProbeOther'})
        self.assertTrue(refused(cand, 'Sheaf.ProbeB', '', TEXT))

    def test_new_declaration_colliding_with_current_module_is_refused(self):
        base = base_of({'Sheaf.ProbeA': TEXT})
        cand = nt.overlay_index(base, [{'module': 'Sheaf.ProbeB', 'text': TEXT}])
        self.assertTrue(refused(cand, 'Sheaf.ProbeB', '', TEXT))

    def test_two_delivered_copies_are_refused(self):
        base = base_of({})
        mods = [{'module': 'Sheaf.ProbeB', 'text': TEXT}, {'module': 'Sheaf.ProbeC', 'text': TEXT}]
        cand = nt.overlay_index(base, mods)
        self.assertTrue(refused(cand, 'Sheaf.ProbeB', '', TEXT))

    def test_accumulated_candidates_see_earlier_accepted_plans(self):
        base = base_of({})
        first = nt.overlay_index(base, [{'module': 'Sheaf.ProbeB', 'text': TEXT}])
        second = nt.overlay_index(first, [{'module': 'Sheaf.ProbeC', 'text': TEXT}])
        self.assertTrue(refused(second, 'Sheaf.ProbeC', '', TEXT))
        self.assertEqual(base.decls.get(Q, set()), set())


if __name__ == '__main__':
    unittest.main()
