"""Integration tests: single-file compiler, private imports, and current diagnostics.

Run on the project server with its published Lean library. No global build.
"""
import json
import os
import pathlib
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent


class PrivateModuleImports(unittest.TestCase):
    def compile(self, files):
        return subprocess.run(
            ['python3', str(ROOT / 'tools/nt_compile.py'), '--json'], cwd=ROOT,
            input=json.dumps({'files': files}), capture_output=True, text=True, timeout=190)

    def test_transitive_private_imports_override_published_namespace(self):
        live = pathlib.Path(os.environ.get('SHEAF_LIVE_LEAN',
                                           ROOT.parent / 'weil-conjectures-sheaf/lean'))
        published = live / '.lake/build/lib/lean/Sheaf/CategoryTheory/CompactObject.olean'
        before = published.stat() if published.exists() else None
        files = {
            'Sheaf/Stage2/MaintQ26Consumer.lean': '''module
public import Sheaf.Stage2.MaintQ26Middle
public meta import Sheaf.Stage2.MaintQ26Middle
@[expose] public section
#eval maintQ26Next
example : maintQ26Next = 42 := rfl
''',
            'Sheaf/Stage2/MaintQ26Middle.lean': '''module
public import Sheaf.CategoryTheory.CompactObject
@[expose] public section
def maintQ26Next : Nat := maintQ26Value + 5
''',
            'Sheaf/CategoryTheory/CompactObject.lean': '''module
@[expose] public section
def maintQ26Value : Nat := 37
''',
        }
        result = self.compile(files)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('42\n', result.stdout)
        self.assertIn('limit 60 s', result.stdout)
        self.assertLess(result.stdout.index('CompactObject.lean:'),
                        result.stdout.index('MaintQ26Middle.lean:'))
        self.assertLess(result.stdout.index('MaintQ26Middle.lean:'),
                        result.stdout.index('MaintQ26Consumer.lean:'))
        after = published.stat() if published.exists() else None
        self.assertEqual(before, after, 'published artifact was modified')

    def test_bad_source_returns_lean_error(self):
        result = self.compile({'Sheaf/Stage2/MaintQ26Bad.lean':
                               'def maintQ26Bad : Nat := "invalid"\n'})
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('error:', result.stdout)
        self.assertIn('MaintQ26Bad.lean', result.stdout)

    @unittest.skip('the side KFlat override is retired (2026-10-19): live proves the interface in KFlatIndependentCoefficients')
    def test_recorded_kflat_interface_available_without_supplying_sources(self):
        result = self.compile({'Sheaf/Stage2/MaintNPKFlatImport.lean': '''module
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
#check @CochainComplex.IsKFlatIndependentCoefficients
#check @CochainComplex.IsKFlatGeneral
#check @CochainComplex.IsKFlat
#check @SheafOfModules.hasSheafify_coefficientUniverse
#check @SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
'''})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('@CochainComplex.IsKFlatIndependentCoefficients', result.stdout)
        self.assertIn('KFlatIndependentCoefficients.lean:', result.stdout)
        self.assertLess(result.stdout.index('KFlat.lean:'),
                        result.stdout.index('MaintNPKFlatImport.lean:'))

    @unittest.skip('the side KFlat override is retired (2026-10-19): live proves the interface in KFlatIndependentCoefficients')
    def test_override_reached_only_through_published_import(self):
        # The published resolution module imports the retired compatibility
        # implementation; the consumer never directly imports that module.
        result = self.compile({'Sheaf/Stage2/MaintNFTransitiveKFlat.lean': """module
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
#check @CochainComplex.IsKFlatIndependentCoefficients
#check @CochainComplex.exists_isKFlatResolutionIndependentCoefficients
#check @CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat
#check @CochainComplex.isKFlatResolutionIndependentCoefficients_iff_isKFlatResolution
@[expose] public section
open CategoryTheory
universe u v w
example {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) : Prop :=
  @CochainComplex.IsKFlatIndependentCoefficients _ _ _ J R K
#check @SheafOfModules.isMonoidal_W_separateHomUniverse.{0, 0}
#check @SheafOfModules.preservesZeroMorphisms_curriedTensor.{0, 0}
#check @SheafOfModules.preservesZeroMorphisms_curriedTensor_obj.{0, 0}
#check @SheafOfModules.isMonoidal_W_coefficientUniverse.{0, 0, 0}
#check @SheafOfModules.preservesZeroMorphisms_curriedTensor_coefficientUniverse.{0, 0, 0}
#check @SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_coefficientUniverse.{0, 0, 0}
"""})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('KFlatIndependentCoefficients.lean:', result.stdout)
        self.assertIn('MaintNFTransitiveKFlat.lean:', result.stdout)


if __name__ == '__main__':
    unittest.main()
