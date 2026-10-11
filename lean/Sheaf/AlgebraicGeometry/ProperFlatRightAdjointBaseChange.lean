/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Base change for the right adjoint of proper flat direct image

Source: Stacks Project, Duality for Schemes, Lemma 48.12.4, Tag 0AAB
(blueprint: lem-sc-proper-flat-right-adjoint-basechange).
-/

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical right-adjoint base-change map is an isomorphism for a proper flat
morphism of finite presentation and arbitrary base change between qcqs schemes.
The witness `hβ` supplies the ordinary derived base-change isomorphism needed by the
shared definition of the canonical map; it is concluded, not assumed. The qcqs
structures of `X` are deduced from properness and the qcqs hypotheses on `Y`.
Source: Stacks Project, Duality for Schemes, Lemma 48.12.4, Tag 0AAB
(blueprint: lem-sc-proper-flat-right-adjoint-basechange).

Proof:
1. Apply lem-sc-proper-flat-right-adjoint-restriction-open to `f` and its base change.
Formation of the right adjoints and their canonical base-change map commutes with
restriction to quasi-compact affine opens of either base. Locality of isomorphisms
in D_QCoh therefore reduces the assertion to a morphism between affine bases.
2. Flatness gives Tor independence for every base change. Properness and finite
presentation then put this in case (1) of Tag 0AA8. Apply
lem-sc-proper-flat-right-adjoint-affine-basechange to the canonical map, using the
derived base-change isomorphism for the flat complex O_X[0]. The restriction
identifications transport the affine isomorphisms to the covers and hence globally.
-/
theorem proper_flat_rightAdjoint_baseChange
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
        (QuasiCompact.compactSpace_of_compactSpace f)
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst
          E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a') :
    ∃ hβ : ∀ E : schemeDerivedQCohCategory X,
        IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition E.obj),
      ∀ K : schemeDerivedQCohCategory Y,
        IsIso (@dualityEquationBaseChangeMap _ X Y Y'
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f g a a' adjf adjf' hβ K) := by
  sorry

end AlgebraicGeometry
