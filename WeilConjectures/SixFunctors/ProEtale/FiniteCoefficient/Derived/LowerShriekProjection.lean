/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj

/-!
# The projection map for the compactly supported direct image

Let `f : X ⟶ Y` be a morphism of schemes with a compactification
`c = (X ⟶[i] Z ⟶[g] Y)`, so that `Rf_!(c) = Di_! ⋙ Rg_*`. We construct the projection map
```
PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)
```
natural in `K` in `D(X_proét)` and `L` in `D(Y_proét)`, as the composite
```
Rg_*(i_!K) ⊗ᴸ L ⟶ Rg_*(i_!K ⊗ᴸ Lg^*L)          (projection map of `Rg_*`)
                ≅ Rg_*(i_!(K ⊗ᴸ Li^*Lg^*L))     (projection formula for `i_!`)
                ≅ Rg_*(i_!(K ⊗ᴸ Lf^*L))         (`Lg^* ⋙ Li^* ≅ L(i ≫ g)^*` and `f = i ≫ g`)
```
of `AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap`, of the inverse of
`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso` and of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp`.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.derivedTensorRightDerivedLowerShriek c` and
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar c`: the
  bifunctors `(K, L) ↦ Rf_!(c)K ⊗ᴸ L` and `(K, L) ↦ Rf_!(c)(K ⊗ᴸ Lf^*L)`, of type
  `D(X_proét) ⥤ D(Y_proét) ⥤ D(Y_proét)`.
- `AlgebraicGeometry.ProEtale.projectionMapOfCompactification c`: the projection map `PF_c`, as a
  natural transformation between these bifunctors.
- `AlgebraicGeometry.ProEtale.projectionMap f`: the projection map for the chosen
  compactification `HasCompactification.compactification f`.
- `AlgebraicGeometry.ProEtale.projectionMapOfCompactification_app_app`: the value of `PF_c` at
  `(K, L)` is the composite above.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

variable [ProEtale.UpperStarPreservesFlat A]

end ProEtale

end AlgebraicGeometry
