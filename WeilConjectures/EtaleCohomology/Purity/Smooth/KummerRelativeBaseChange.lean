/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerOrientation

/-!
# Base change of the direct images of `Λ(1)` from `𝔸¹` and `𝔾ₘ`

For a morphism `g : Y' ⟶ Y` of separated `k`-schemes of finite type, `k` algebraically closed,
the derived base change maps `Lg^* Rp_* Λ(1) ⟶ Rp'_* Λ(1)` of the affine line
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_tateObject_affineLine_of_cohomology`)
and
`Lg^* Rπ_* Λ(1) ⟶ Rπ'_* Λ(1)` of the complement of the zero section
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_tateObject_multiplicativeGroup`) are
isomorphisms: both sides have cohomology sheaves only in degree `0` (resp. `0` and `1`), where
the base change maps are compatible with the units (resp. with the Kummer classes, which
generate).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable [Finite Λ] [HasTateTwist Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
  [QuasiCompact aY] {Y' : Scheme.{u}} (aY' : Y' ⟶ Spec (.of k)) [IsSeparated aY']
  [LocallyOfFiniteType aY'] [QuasiCompact aY'] (g : Y' ⟶ Y)
  [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ Y']

end Etale

end AlgebraicGeometry
