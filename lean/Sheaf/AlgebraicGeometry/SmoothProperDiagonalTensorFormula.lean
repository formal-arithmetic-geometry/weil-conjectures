/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.PerfectComplex
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Tensor formula for the right adjoint of a perfect proper immersion

Source: literature/stacks-project/duality.tex, Tag 0A9U
(projection formula for a perfect proper morphism and its right adjoint)
(blueprint: lem-sc-smooth-proper-diagonal-tensor-formula).
-/

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- For a proper perfect closed immersion, the right adjoint of derived direct image
satisfies the projection formula.  The displayed morphism is the mate, under the
specified adjunction, of the projection-formula morphism.
Source: Stacks Project, Tag 0A9U.
(blueprint: lem-sc-smooth-proper-diagonal-tensor-formula).

Proof (Tag 0A9U, following the five node steps):
1. The closed immersion is proper, finite type and perfect: the stalks of i_*O_Z have
   finite free resolutions by local perfection. By lem-sc-smooth-proper-tensor-direct-sums
   (Tag 0A9R), c commutes with arbitrary set-indexed direct sums.
2. Direct sums exist by lem-pc-derived-qcoh-direct-sums. The isomorphism locus of the
   comparison is strictly full, saturated and triangulated, because both functors are
   exact. It is closed under sums: derived pullback and tensor preserve sums, as does c.
3. Perfect objects generate this localizing subcategory by
   lem-pc-derived-qcoh-perfect-generation. The adjoint exists by
   lem-pc-noetherian-derived-direct-image-right-adjoint.
4. The comparison is invertible on perfect K by lem-sc-smooth-proper-tensor-perfect-case
   (Tag 0A9T), with the same counit-pinned projection comparison.
5. The localizing-subcategory argument of Tag 0A9U now gives invertibility for all K.
   Taking its inverse gives the equivalent displayed tensor formula.
-/
theorem smooth_proper_diagonal_tensor_formula
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsProper i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hperfect : Y.IsPerfect ((schemeDerivedDirectImage i).obj
      (𝟙_ (schemeDerivedCategory Z)))) :
    ∃ (hRf : ∀ E : schemeDerivedQCohCategory Z,
        schemeDerivedQCohProperty Y ((schemeDerivedDirectImage i).obj E.obj))
      (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
      (hTensor : ∀ (K : schemeDerivedQCohCategory Y)
        (E : schemeDerivedQCohCategory Z),
        schemeDerivedQCohProperty Z (((derivedPullback i).obj K.obj) ⊗ E.obj)),
      Nonempty (Functor.Monoidal (derivedPullback i)) ∧
      Nonempty (derivedPullback i ⊣ schemeDerivedDirectImage i) ∧
      ∀ (_ : Functor.Monoidal (derivedPullback i))
        (a : derivedPullback i ⊣ schemeDerivedDirectImage i)
        (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
        (adj : (schemeDerivedQCohProperty Y).lift
          ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i) hRf ⊣ c)
        (K : schemeDerivedQCohCategory Y),
        ∃ pf : (schemeDerivedDirectImage i).obj
            (((derivedPullback i).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage i).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback i) K.obj
              ((schemeDerivedDirectImage i).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback i).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback i).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom))) := by
  sorry

end AlgebraicGeometry
