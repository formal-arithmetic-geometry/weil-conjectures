"""Source-only regression tests: no Lean invocation."""
import unittest
import json
import pathlib
import subprocess
import tempfile
from unittest.mock import patch
import sorry_ledger as sl


class Scanner(unittest.TestCase):
    def rows(self,text):
        return sl.scan_text(text)[0]

    def test_lexer_adversarial(self):
        text='''/- sorry /- admit -/ axiom -/
namespace N
def «shim/-» := "sorry -- \\\" axiom"
theorem real : True := by sorry
-- admit
end N
'''
        rows=self.rows(text)
        self.assertEqual([(r['name'],r['markers']) for r in rows if r['markers']], [('N.real',['sorry'])])

    def test_signature_let_and_fields(self):
        rows=self.rows('''namespace N
structure S where
  data : Nat := sorry
  ok : True := by sorry
instance : Inhabited Nat := ⟨sorry⟩
theorem t : let x := 1; x = x := by sorry
axiom bad : True
end N
''')
        h={r['name']:r for r in rows if r['markers']}
        self.assertEqual(h['N.S.data']['kind'],'structure field')
        self.assertEqual(h['N.S.ok']['kind'],'structure field')
        self.assertEqual(h['N.bad']['markers'],['axiom'])
        self.assertIn('let x := 1;',h['N.t']['signature'])
        self.assertTrue(any(r['kind']=='instance' for r in h.values()))

    def test_unattributed_and_errors(self):
        self.assertIn('unattributed',sl.scan_text('#check sorry')[1][0])
        self.assertEqual(sl.scan_text('/-')[0][0]['markers'],['unavailable'])

    def test_missing_gate(self):
        self.assertTrue(sl.missing_gate('', 'theorem t : True := by admit'))
        self.assertTrue(sl.missing_gate('axiom old : True', 'axiom old : True\naxiom new : True'))
        self.assertTrue(sl.missing_gate('', 'structure S where\n  x : Nat := sorry'))
        self.assertTrue(sl.missing_gate('', 'instance : Inhabited Nat := ⟨sorry⟩'))
        self.assertEqual(sl.missing_gate('', 'theorem t : True := by sorry'), [])
        self.assertEqual(sl.missing_gate('', 'def «shim/-» := r#"admit \" sorry"#'), [])

    def test_private_helper_dependency(self):
        a=self.state('theorem t : True := by sorry\n')
        b=self.state('private theorem helper : True := by exact lower\ntheorem t : True := by exact helper\ntheorem lower : True := by sorry\n')
        self.assertEqual(sl.classify(sl.delta(a,b),a,b),'moved')
        a=self.state('structure S where\n  x : Nat := sorry\n')
        b=self.state('structure S where\n  x : Nat := 0\n')
        self.assertEqual(len(sl.delta(a,b)['closed']),1)

    def state(self,text):
        return dict(decls={('Sheaf.X',r['name']):r for r in self.rows(text)},
                    imports={'Sheaf.X':set()},dist={'Sheaf.X':0})

    def test_delta_classes(self):
        a=self.state('theorem t : True := by sorry\n')
        b=self.state('theorem t : True := by trivial\n')
        self.assertEqual(sl.classify(sl.delta(a,b),a,b),'proved')
        b=self.state('theorem t : True := by exact lower\ntheorem lower : True := by sorry\n')
        self.assertEqual(sl.classify(sl.delta(a,b),a,b),'moved')
        b=self.state('theorem t : False := by sorry\n')
        self.assertEqual(sl.classify(sl.delta(a,b),a,b),'moved')
        b=self.state('')
        self.assertEqual(sl.delta(a,b)['closed'],[])
        self.assertEqual(len(sl.delta(a,b)['deleted']),1)


class PostBuild(unittest.TestCase):
    def test_green_pin_noop_and_unrelated_index(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=pathlib.Path(tmp)
            def git(*args):
                return subprocess.check_output(['git','-C',tmp,*args],stderr=subprocess.DEVNULL).decode().strip()
            git('init','-q'); git('config','user.name','Ledger test')
            git('config','user.email','test@localhost')
            (root/'lean/Sheaf').mkdir(parents=True)
            (root/'coord').mkdir(); (root/'local/builds').mkdir(parents=True)
            (root/'lean/TargetsCheck.lean').write_text('import Sheaf.X\n')
            (root/'lean/Sheaf/X.lean').write_text('theorem t : True := by sorry\n')
            git('add','lean'); git('commit','-qm','baseline')
            baseline=git('rev-parse','HEAD')
            (root/'local/builds/last.json').write_text(json.dumps(dict(result='green',commit=baseline)))
            (root/'unrelated').write_text('keep staged'); git('add','unrelated')
            with patch.object(sl,'ROOT',root), patch.object(sl,'BASELINES',[(baseline,'test stage'),(baseline,'test imports')]):
                sl.blob.cache_clear()
                try:
                    self.assertTrue(sl.post_build()['changed'])
                    self.assertEqual(git('diff','--cached','--name-only'),'unrelated')
                    self.assertEqual(git('show','--format=','--name-only','HEAD'),
                                     'coord/sorry-ledger.md\ncoord/sorry-ledger.tsv')
                    self.assertFalse(sl.post_build()['changed'])
                    (root/'local/builds/last.json').write_text('{"result":"red"}')
                    self.assertIn('skipped',sl.post_build())
                finally:
                    if sl._CAT is not None:
                        sl._CAT.stdin.close(); sl._CAT.wait()
                        sl._CAT.stdout.close(); sl._CAT=None
                    sl.blob.cache_clear()


class UndeterminedData(unittest.TestCase):
    def state(self,modules,imports=None,exceptions=()):
        return dict(decls={(m,r['name']):dict(r,module=m)
                           for m,text in modules.items() for r in sl.scan_text(text)[0]},
                    imports=imports or {m:set() for m in modules},dist={'Sheaf.Use':0},
                    warnings=[],determined_definitions=set(exceptions))

    def test_choice_forms_and_one_count_per_definition(self):
        state=self.state({'Sheaf.Use':'''namespace N
theorem existence : ∃ n : Nat, True := by sorry
theorem inhabited : Nonempty Nat := by sorry
def prefix := Classical.choose (existence)
abbrev existsPrefix := Exists.choose existence
def postfix := (existence).choose
def nested := (existence).choose_spec.choose
def projected := ((existence).choose_spec).2.choose
def piped := (existence).choose_spec |> .2.choose
def direct := existence.choose
def some := Nonempty.some inhabited
def dotSome := inhabited.some
def choice := Classical.choice inhabited
def description := (Classical.indefiniteDescription _ existence).1
def repeated := (Classical.choose existence, Classical.choose existence)
instance arbitrary : Inhabited Nat := ⟨Classical.choice inhabited⟩
structure S where
  arbitrary : Nat := (existence).choose
  supplied : Nat
end N
'''})
        found=sl.undetermined_data(state)
        self.assertEqual(len(found),14)
        self.assertEqual(found['Sheaf.Use','N.repeated']['chosen_from'],['N.existence'])
        self.assertIn(('Sheaf.Use','N.S.arbitrary'),found)
        self.assertNotIn(('Sheaf.Use','N.S.supplied'),found)
        self.assertEqual(sl.census(state)['definitions'],0)
        self.assertEqual(sl.census(state)['undetermined_definitions'],14)

    def test_import_namespace_open_and_method_resolution(self):
        state=self.state({'Sheaf.Base':'''namespace A
namespace Inner
theorem ex : Nonempty Nat := by sorry
end Inner
theorem maps_exists : Nonempty Nat := by sorry
end A
''','Sheaf.Other':'namespace B\ntheorem ex : Nonempty Nat := by sorry\nend B\n',
                         'Sheaf.Use':'''open A.Inner
namespace A
namespace Nested
def relative := Classical.choice maps_exists
def opened := Classical.choice ex
def qualified := Classical.choice A.Inner.ex
def method (x : Nat) := Classical.choice x.maps_exists
end Nested
end A
''','Sheaf.Outside':'def unreachable := Classical.choice A.maps_exists\n'},
                        imports={'Sheaf.Base':set(),'Sheaf.Other':set(),
                                 'Sheaf.Use':{'Sheaf.Base'},'Sheaf.Outside':set()})
        found=sl.undetermined_data(state)
        self.assertEqual(len(found),4)
        self.assertEqual(found['Sheaf.Use','A.Nested.opened']['chosen_from'],['A.Inner.ex'])
        self.assertEqual(found['Sheaf.Use','A.Nested.method']['chosen_from'],['A.maps_exists'])

    def test_no_unrelated_signature_shadow_or_comment_matches(self):
        state=self.state({'Sheaf.Use':'''theorem ex : Nonempty Nat := by sorry
theorem good : Nonempty Nat := ⟨0⟩
def unrelated := by
  have h := ex
  exact Classical.choice good
def binder (ex : Nonempty Nat) := Classical.choice ex
def lambdaBinder := fun ex ↦ Classical.choice ex
def shadow := by
  let ex : Nonempty Nat := ⟨0⟩
  exact Classical.choice ex
def signature (x : Fin (Classical.choice ex)) := 0
def text := "Classical.choice ex"
/- def comment := Classical.choice ex -/
structure S where
  x : Fin (Classical.choice ex)
theorem proofOnly : True := by
  have x := Classical.choice ex
  trivial
'''})
        self.assertEqual(sl.undetermined_data(state),{})

    def test_exceptions_by_declaration_and_closure(self):
        judgments='''Mentioning `outside` class 1 in prose grants no exception.
| Module | Declaration | Chosen from | Class | Reason |
|---|---|---|---|---|
| Sheaf.Use | `N.allowed` | `N.ex` | 1 | unique |
| Sheaf.Use | `N.forbidden` | `N.ex` | 2 | arbitrary |

| Class | Declaration | Module |
|---|---|---|
| 1 | `N.repaired` | Sheaf.Repaired |
'''
        self.assertEqual(sl.class_one_names(judgments),{'N.allowed','N.repaired'})
        text='''namespace N
theorem ex : Nonempty Nat := by sorry
def allowed := Classical.choice ex
def forbidden := Classical.choice ex
end N
'''
        state=self.state({'Sheaf.Use':text,'Sheaf.Outside':'theorem ex : Nonempty Nat := by sorry\ndef outside := Classical.choice ex\n'},
                         exceptions=sl.class_one_names(judgments))
        self.assertEqual(len(sl.undetermined_data(state)),2)
        self.assertEqual(len(sl.undetermined_data(state,True)),1)

    def test_judgments_are_pinned_to_input_tree(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=pathlib.Path(tmp)
            def git(*args):
                return subprocess.check_output(['git','-C',tmp,*args],stderr=subprocess.DEVNULL).decode().strip()
            git('init','-q'); git('config','user.name','Ledger test')
            git('config','user.email','test@localhost')
            (root/'lean/Sheaf').mkdir(parents=True); (root/'coord').mkdir()
            (root/'lean/TargetsCheck.lean').write_text('import Sheaf.Use\n')
            (root/'lean/Sheaf/Use.lean').write_text('theorem ex : Nonempty Nat := by sorry\ndef data := Classical.choice ex\n')
            doc=root/sl.HOLLOW_JUDGMENTS
            doc.write_text('| Declaration | Class |\n|---|---|\n| `data` | 2 |\n')
            git('add','.'); git('commit','-qm','undetermined')
            old=git('rev-parse','HEAD')
            doc.write_text('| Declaration | Class |\n|---|---|\n| `data` | 1 |\n')
            git('add','.'); git('commit','-qm','determined')
            with patch.object(sl,'ROOT',root):
                sl.blob.cache_clear()
                try:
                    self.assertEqual(sl.census(sl.snapshot(sl.tree(old)))['undetermined_definitions'],1)
                    self.assertEqual(sl.census(sl.snapshot(sl.tree('HEAD')))['undetermined_definitions'],0)
                finally:
                    if sl._CAT is not None:
                        sl._CAT.stdin.close(); sl._CAT.wait()
                        sl._CAT.stdout.close(); sl._CAT=None
                    sl.blob.cache_clear()


if __name__=='__main__': unittest.main()
