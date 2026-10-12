/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DiagonalConormalDifferentials
import Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing
import Sheaf.AlgebraicGeometry.SmoothDiagonalKoszulRegular
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex

/-! # The dualizing object of a smooth diagonal in constant rank

Source: Stacks Project, Tags 0BR0 and 08S2, fourth equality of Tag 0BRT
(blueprint: lem-sc-smooth-diagonal-dualizing-determinant).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wP

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The diagonal right adjoint takes the structure object to the shifted determinant
of the dual of relative differentials. This does not involve the right adjoint of f.
Source: Stacks Project, Tags 0BR0 and 08S2, fourth equality in Tag 0BRT.
(blueprint: lem-sc-smooth-diagonal-dualizing-determinant).

Proof: Properness makes the diagonal a closed immersion. Smoothness of pure relative
dimension d makes it Koszul regular. The local generators near each diagonal point
have length d; restrict their affine neighbourhoods to obtain the regularity witness
required by koszulRegularImmersion_dualizing. The diagonal conormal is relative
Kahler differentials by diagonalConormal_iso_relativeDifferentials. Smoothness says
that this sheaf is finite locally free of rank d; hence its stalk finrank is d,
and the constant locally constant function with value d satisfies the rank witness
in Koszul duality. Apply koszulRegularImmersion_dualizing with this rank function
and the specified adjunction c. First apply c to the full-subcategory lift of hOP,
so its input is literally the single structure sheaf as required there. Koszul
duality gives the rank-stratified exterior complex isomorphic to c(OP).
Dualize the conormal isomorphism by precomposition, then apply the exterior power.
For constant rank d, all rank strata other than d are empty; their extensions by
zero vanish. The rank-d stratum is all of X, so its extension is the original
exterior sheaf. Thus the locally ranked complex is the complex with this sheaf in
degree d and zero elsewhere. Its image in the derived category is its degree-zero
single shifted by -d. Compose these identifications with the inverse of Koszul
duality. Its theorem already permits different derived universes for X and P.
If X is empty, the rank witness is vacuous and the same complex identification
holds. For d = 0 it gives the structure sheaf in degree zero, as it should. -/
theorem smoothDiagonal_dualizing_determinant
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
              (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧) := by sorry

end AlgebraicGeometry
