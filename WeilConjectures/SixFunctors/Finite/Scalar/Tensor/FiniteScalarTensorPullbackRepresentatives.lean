/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackFixedDataLaw
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackIntrinsicDataLaw
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackFactorsDataLaw
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackChainDataLaw

/-! # The normalized scalar tensor square on resolving pairs

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-pullback-representatives).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

attribute [local irreducible] SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleCanonicalTensorComparison
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

attribute [local implicit_reducible] WeilConjectures.finiteScalarTensorRepresentativeData

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
  AlgebraicGeometry.ProEtale.derivedTensor
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  CategoryTheory.Equivalence.mapDerivedCategory

attribute [local implicit_reducible] WeilConjectures.finiteScalarTensorPullbackData

attribute [local implicit_reducible] WeilConjectures.finiteScalarFixedTensorDataForCoefficients
  WeilConjectures.finiteScalarFixedPullbackDataForCoefficients

namespace WeilConjectures

/-- The specified scalar tensor and inverse-image comparisons commute on flat-term
K-flat fixed-scalar complexes. The tensor isomorphisms here are the constructed,
uniquely normalized finiteScalarTensorRealization, not existential choices.

Source: Stacks Tags 07A4 and 07A6; representative part of step 3 of
lem-sf-finite-scalar-tensor-pullback-comparison.
(blueprint: lem-sf-finite-scalar-tensor-pullback-representatives).

Proof: first compare the ordinary inverse-image adjunctions through the coefficient
realization. Restrict both direct images along the scalar-unit map. The sectionwise
comparison is the identity on M(X ×_Y U), by sfIntrinsicDirectImageComparison's
normalization. Applying the coefficient Hom bijection identifies this direct image
with proEtaleConstantRingPushforward. Taking its inverse mate therefore gives the
ordinary scalar inverse-image comparison with its actual adjunction unit. The tensor
comparison used in finiteScalarOrdinaryTensorIso is constructed by sheafifying the
tensor of the scalar-unit sections. On a balanced pure tensor, the two ordinary
pullback composites both give the tensor of these inverse-image unit sections.
Tensor's universal property and sheafification show that the ordinary square commutes.
For the given flat-term K-flat complexes apply this square in each bidegree. The total
map is finiteScalarTotalTensorIso, so the coproduct injection equations assemble the
ordinary squares, with the same Koszul signs, into the chain square. Exactness and the
ordinary tensor comparison preserve the flat K-flat representative classes. Localize
this chain square and substitute the defining representative equations of
finiteScalarTensorRealization, proEtaleCanonicalTensorComparison, and the published
leftDerivedUpperStarTensorComparison. Finally the K-injective characterization of
sfIntrinsicDerivedDirectImageComparison and compatibility of derived adjunction Hom
bijections identify the derived inverse mate with finiteScalarPullbackComparison.
Cancel the localization tensorators and the exact-functor comparison isomorphisms.
The result is the equation below. Only a fixed pair of resolving complexes is used;
there is no extension to arbitrary derived inputs in this statement. All arguments
are universal properties and apply to zero coefficients, zero complexes and empty sites.
-/
theorem finiteScalarTensorPullback_onRepresentatives
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X R))
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R))
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (_hp : finiteScalarFlatRepresentatives Y R P)
    (_hq : finiteScalarFlatRepresentatives Y R Q) :
    let F := (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).leftDerivedFunctor
    let EX := (sfIntrinsicDerivedEquivalence X R).functor
    let EY := (sfIntrinsicDerivedEquivalence Y R).functor
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    EX.map (((ProEtale.leftDerivedUpperStarTensorComparison
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).app M).app N) ≫
        ((finiteScalarTensorRealization X R aX).hom.app (F.obj M)).app (F.obj N) =
      (finiteScalarPullbackComparison R p).inv.app
          (((ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} R)) Y).obj M).obj N) ≫
        (proEtaleConstantRingDerivedPullback R p).map
          (((finiteScalarTensorRealization Y R aY).hom.app M).app N) ≫
        ((finiteScalarCurriedTensorPullback R p aX aY).app (EY.obj M)).app (EY.obj N) ≫
        ((curry.obj aX.tensor).map ((finiteScalarPullbackComparison R p).hom.app M)).app _ ≫
        ((curry.obj aX.tensor).obj _).map
          ((finiteScalarPullbackComparison R p).hom.app N) := by
  let S := finiteScalarTensorPullbackData R p aX aY
  have h := ScalarTensorPullbackData.tensorSquare S
    (finiteScalarTensorPullback_fixedLaw R p aX aY)
    (finiteScalarTensorPullback_intrinsicLaw R p aX aY)
    (finiteScalarTensorPullback_factorsLaw R p aX aY)
    (finiteScalarTensorPullback_chainLaw R p aX aY) P Q _hp _hq
  simpa only [S, finiteScalarTensorPullbackData, finiteScalarTensorRepresentativeData,
    finiteScalarFixedTensorDataForCoefficients, finiteScalarFixedPullbackDataForCoefficients,
    finiteScalarCurriedTensorPullback, ProEtale.leftDerivedUpperStarDerivedTensor] using h

end WeilConjectures
