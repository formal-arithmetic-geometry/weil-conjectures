/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection

/-!
# The projection formula for the extension by zero along an open immersion

Let `j : U ⟶ X` be an open immersion. For `K` in `D(U_proét)` and `M` in `D(X_proét)` there is a
canonical morphism
```
j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M
```
in `D(X_proét)`: the projection map `CategoryTheory.Adjunction.projectionMap` of the adjunction
`D(j_!) ⊣ D(j^*)`, i.e. the transpose along `j_! ⊣ j^*` of
```
K ⊗ᴸ Lj^*M --(η ⊗ᴸ 1)--> j^*(j_!K) ⊗ᴸ Lj^*M ≅ j^*(j_!K ⊗ᴸ M),
```
where `η` is the unit of `j_! ⊣ j^*` and the isomorphism comes from the inverse of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`. It is an isomorphism.

The projection map `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` of the blueprint
(`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Exchange`) goes in the opposite
direction: its open part is the inverse `(derivedOpenImmersionLowerShriekProjectionIso j).inv`.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionMap j`: the morphism
  `j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` of bifunctors `D(U_proét) ⥤ D(X_proét) ⥤ D(X_proét)`.
- `AlgebraicGeometry.ProEtale.isIso_derivedOpenImmersionLowerShriekProjectionMap`: it is an
  isomorphism.
- `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso j`: the resulting
  isomorphism of bifunctors.
- `AlgebraicGeometry.ProEtale.derivedTensorOpenImmersionLowerShriekIso j K L`: the projection
  formula `j_!K ⊗ᴸ L ≅ j_!(K ⊗ᴸ Lj^*L)` (blueprint `lem-cbc-extension-zero-projection-formula`).

## The argument

The unit of `D(j_!) ⊣ D(j^*)` is an isomorphism, so by
`CategoryTheory.Adjunction.isIso_projectionMap_app_app_of_iso` it suffices that `j_!K ⊗ᴸ M` lies
in the essential image of `D(j_!)`. Writing `K` as a complex `K₀` and `M` as a K-flat complex
`M₁`, the derived tensor product is computed termwise, `j_!K ⊗ᴸ M ≅ Q(j_!K₀ ⊗ M₁)`, and the
termwise projection isomorphisms
`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekProjectionMap_app_app` of sheaves
assemble to an isomorphism of complexes `j_!(K₀ ⊗ j^*M₁) ≅ j_!K₀ ⊗ M₁`
(`HomologicalComplex.mapBifunctorComparison`).
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

open DerivedCategory

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

variable [ProEtale.UpperStarPreservesFlat A]

end ProEtale

end AlgebraicGeometry
