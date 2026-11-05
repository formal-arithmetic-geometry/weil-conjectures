/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ObjectProperty.IndHeart
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible

import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-!
# The ind-constructible heart

Blueprint `sk-prop-ind-heart` (2): if the constructible sheaves of `R`-modules on `X_proét` are
closed under kernels, cokernels and extensions, and morphisms out of a constructible sheaf `C`
into `B[n]`, `B = colim Bᵢ` a filtered colimit of sheaves, factor through some `Bᵢ[n]`
(`AlgebraicGeometry.ProEtale.HasConstructibleExtContinuity`), then the ind-constructible sheaves
are closed under kernels, cokernels, extensions and direct sums
(`AlgebraicGeometry.ProEtale.isIndConstructibleHeart_of_hasConstructibleExtContinuity`). This is
the abstract statement
`CategoryTheory.ObjectProperty.isClosedUnder_ind_of_homFactorsThroughFilteredColimits`.

We also record that, on a topologically noetherian scheme, the constructible sheaves are closed
under kernels, cokernels and extensions for the coefficient rings `E`, `𝒪_E` and `ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_serre_continuousMapRingObj`,
`AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_serre_padicIntegersRingObj`,
`AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_serre_padicAlgClRingObj`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory ZeroObject

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

end

namespace CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]

-- The prime `ℓ` of `E̲` occurs only in the instance `NormedAlgebra ℚ_[ℓ] E`; it is found from the
-- local instance `Fact ℓ.Prime`, so the synthesis order is not the default one.

end CondensedRing

end AlgebraicGeometry.ProEtale
