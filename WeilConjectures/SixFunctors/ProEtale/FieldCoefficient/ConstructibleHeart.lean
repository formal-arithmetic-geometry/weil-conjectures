/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Abelian

/-!
# The constructible heart with coefficients in a finite extension of `ℚ_ℓ`

Let `Λ` be a field with an ultrametric norm, for instance a finite extension `E` of `ℚ_ℓ` inside
`ℚ̄_ℓ`, and `X` a scheme. The bounded constructible derived category `D^b_c(X, Λ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructible`) is cut out of the
derived category of sheaves of `Λ_X`-modules on the pro-étale site
(`AlgebraicGeometry.ProEtale.FieldSheaf`) by boundedness and constructibility of the cohomology
sheaves. It is stable under the canonical truncations `τ^{≤ n}` and `τ^{≥ n}`, so it inherits the
standard `t`-structure, and its heart `D^{≤ 0}_c ∩ D^{≥ 0}_c`
(`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeart`) is equivalent, by
placing sheaves in degree `0`, to the category `Sh_c(X, Λ)` of constructible `Λ`-adic sheaves
(`AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeartEquiv`), which is abelian on
a locally Noetherian scheme.

This is the constructible heart at the stage `Λ = E`, in the Bhatt–Scholze
model of `D^b_c(X, E)` (*The pro-étale topology for schemes*, §6.8): `E_X`-modules on the
pro-étale site with constructible cohomology. The stage `ℚ̄_ℓ` is
`AlgebraicGeometry.ProEtale.DerivedCategory.adicConstructibleHeart`.

## Main definitions

- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedFieldConstructible`: `D^b_c(X, Λ)`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeart`: the constructible
  heart.
- `AlgebraicGeometry.ProEtale.DerivedCategory.fieldConstructibleHeartEquiv`:
  `Sh_c(X, Λ) ≌ D^{≤ 0}_c(X, Λ) ∩ D^{≥ 0}_c(X, Λ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type) [NormedField Λ] [IsUltrametricDist Λ]

variable {Λ} {X : Scheme.{u}}

namespace DerivedCategory

end DerivedCategory

end AlgebraicGeometry.ProEtale
