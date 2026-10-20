/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafComparison

/-! # Compatibility with the upstream smooth-diagonal determinant theorem

The canonical theorem `AlgebraicGeometry.smoothDiagonal_dualizing_determinant` now lives
in `WeilConjectures.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant`. Its exterior
power equals the original `exteriorSheaf` by `exteriorSheaf_eq_exteriorPower`.
The private check below retains the entire archived statement, including independent
derived universes, and transports the upstream isomorphism to its original conclusion.

Source: Stacks Project, Tags 0BR0 and 08S2, fourth equality of Tag 0BRT
(blueprint: lem-sc-smooth-diagonal-dualizing-determinant).
-/

@[expose] public section

set_option autoImplicit false

-- This compatibility module exports imports; its sole local theorem checks the old interface.
set_option linter.privateModule false

universe u wX wP

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The archived conclusion follows from the canonical theorem by equality of exterior sheaves.
Source: Stacks Project, Tags 0BR0 and 08S2, fourth equality of Tag 0BRT
(blueprint: lem-sc-smooth-diagonal-dualizing-determinant). -/
private theorem exteriorSheaf_compatibility
    (X S : Scheme.{u}) [IsNoetherian S]
    (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wP}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))]
    (hRΔ : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty (pullback f f)
        ((schemeDerivedDirectImage (pullback.diagonal f)).obj E.obj))
    (c : schemeDerivedQCohCategory (pullback f f) ⥤ schemeDerivedQCohCategory X)
    (adjC : (schemeDerivedQCohProperty (pullback f f)).lift
      ((schemeDerivedQCohProperty X).ι ⋙
        schemeDerivedDirectImage (pullback.diagonal f)) hRΔ ⊣ c)
    (OP : schemeDerivedQCohCategory (pullback f f))
    (hOP : OP.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) 0).obj
          (SheafOfModules.unit (pullback f f).ringCatSheaf)) :
    Nonempty ((c.obj OP).obj ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorSheaf
            (SheafOfModules.homObj (R := X.sheaf) f.relativeDifferentials
              (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧) := by
  simpa only [Scheme.Modules.exteriorSheaf_eq_exteriorPower] using
    smoothDiagonal_dualizing_determinant X S f d hRΔ c adjC OP hOP

end AlgebraicGeometry
