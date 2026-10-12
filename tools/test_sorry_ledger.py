"""Source-only regression tests: no Lean invocation."""
import unittest
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


if __name__=='__main__': unittest.main()
