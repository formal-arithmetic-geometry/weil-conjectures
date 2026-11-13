/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Canonical localization comparisons for the projection mate

All model functors below carry natural representative comparisons. Ordinary operations
are Mathlib's module pullback and pushforward for the specified ring map. Tensor
comparisons are normalized on pure tensors and signed total complexes; derived
adjunctions are normalized by the ordinary counit on K-injectives. No operation or
projection arrow is selected from an unconstrained existence statement.

## Main definitions

* `ProjectionRestriction.Operation`: the canonical module and derived operations.
* `ProjectionRestriction.TensorModel`: derived tensor normalized on resolving pairs.
* `ProjectionRestriction.Local`: canonical slice comparisons and their normalizations.

The assembly theorem `ringedProjectionRestriction` is in
`Sheaf.Paper.RingedProjectionRestriction`. This module contains its unchanged data
interfaces so the construction lemmas can be imported without a cycle.

## References

* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 0FN5](https://stacks.math.columbia.edu/tag/0FN5)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 05RU](https://stacks.math.columbia.edu/tag/05RU)
* [Stacks Project, Tag 0735](https://stacks.math.columbia.edu/tag/0735)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Modules with the original coefficient universe. -/
abbrev Mod (R : Sheaf J CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The standard localization size for these module categories. -/
instance derived (R : Sheaf J CommRingCat.{u + 1}) : HasDerivedCategory (Mod R) :=
  HasDerivedCategory.standard _

/-- Standard localization on the slice site. -/
instance derivedOver (R : Sheaf J CommRingCat.{u + 1}) (V : C) :
    HasDerivedCategory (Mod (R.over V)) := HasDerivedCategory.standard _

/-- The same standard localization for the raw slice-ring presentation. -/
instance derivedOverModules (R : Sheaf J RingCat.{u + 1}) (V : C) :
    HasDerivedCategory (SheafOfModules.{u + 1} (R.over V)) := HasDerivedCategory.standard _

/-- The module operations associated to a continuous ringed site map: a coefficient ring map
whose module pushforward is a right adjoint with exact additive pullback, together with
K-injective resolutions on the target. -/
structure Operation (F : C ⥤ D) (R : Sheaf J CommRingCat.{u + 1})
    (S : Sheaf K CommRingCat.{u + 1}) where
  [continuous : F.IsContinuous J K]
  coefficient : ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
    (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
  [rightAdjoint : (SheafOfModules.pushforward.{u + 1} coefficient).IsRightAdjoint]
  [pullbackAdditive : (SheafOfModules.pullback.{u + 1} coefficient).Additive]
  [pushforwardAdditive : (SheafOfModules.pushforward.{u + 1} coefficient).Additive]
  [pullbackLimits : PreservesFiniteLimits (SheafOfModules.pullback.{u + 1} coefficient)]
  [pullbackColimits : PreservesFiniteColimits (SheafOfModules.pullback.{u + 1} coefficient)]
  [kInjectives : Abelian.HasKInjectiveResolutions (Mod S)]

attribute [instance] Operation.rightAdjoint Operation.pullbackAdditive
  Operation.pushforwardAdditive Operation.pullbackLimits Operation.pullbackColimits

namespace Operation

variable {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}}
  {S : Sheaf K CommRingCat.{u + 1}} (o : Operation F R S)

end Operation

namespace Operation
end Operation

end AlgebraicGeometry.Scheme.ProjectionRestriction

namespace AlgebraicGeometry.Scheme.ProjectionRestriction
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)

end AlgebraicGeometry.Scheme.ProjectionRestriction
