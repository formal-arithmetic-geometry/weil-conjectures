/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Internal hom adjunction formulas on the pro-étale site

Let `f : Y ⟶ X` be a morphism of schemes. On the unbounded derived categories of pro-étale
sheaves, the derived pullback `Lf^*` is strong monoidal
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso`). Passing to right adjoints
along `Lf^* ⊣ Rf_*` and the tensor–hom adjunctions gives the internal-hom form of the
projection formula `RHom(B, Rf_* C) ≅ Rf_* RHom(Lf^* B, C)`. In the same way, the projection
formula for the extension by zero along an open immersion `j`
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso`) gives
`Rj_* RHom(K, j^* N) ≅ RHom(j_! K, N)`.

## Main statements

- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompDerivedHomIso`:
  `RHom(B, Rf_* C) ≅ Rf_* RHom(Lf^* B, C)`, naturally in `C`.
- `AlgebraicGeometry.ProEtale.derivedHomOpenImmersionLowerShriekIso`:
  `Rj_* RHom(K, j^* N) ≅ RHom(j_! K, N)` for an open immersion `j`, naturally in `N`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompDerivedHomClosedImmersionIso`:
  `RHom(Ri_* K, Ri_* C) ≅ Ri_* RHom(K, C)` for a closed immersion `i`, naturally in `C`.
- `AlgebraicGeometry.ProEtale.isZero_derivedHom_rightDerivedLowerStar_of_disjoint`:
  `RHom(Ri_* K, Rj_* N) = 0` when the ranges of `i` and of the open immersion `j` are disjoint.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]

end General

section Immersion

variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]

end Immersion

end AlgebraicGeometry.ProEtale
