/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.Paper.IntegralOperationsScalarComparisonModels
public import Sheaf.Paper.ScalarExtensionComposition

/-! # Degreewise scalar pullback chain tower comparison

This is the degreewise component of the normalized scalar pullback chain tower
identity.  It isolates the finite-level generator and Roos-coordinate calculation
from the final chain-map extensionality argument.
(blueprint: lem-pur-integral-scalar-pullback-chain-tower)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (j : L →ₐ[ℚ_[l]] F)

/--
Degreewise form of the normalized pullback Roos chain tower identity.

Source: Stacks 07A4, 08TC; the finite-level generator calculation, reduction
squares, and both Roos product-coordinate calculations in the proof of
`lem-pur-integral-scalar-pullback-chain-tower`.

The proof is the explicit coefficient calculation on finite pullback generators,
extended through sheafification and the strict reduction tower, followed by the
unshifted and shifted Roos coordinate formulas.  This statement is strictly
smaller than the chain-map identity because it fixes one cochain degree; the
chain-map result follows by extensionality in the degree index.
(blueprint: lem-pur-integral-scalar-pullback-chain-tower)
-/
theorem integralScalarPullbackChainTower_f {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) :
    (((integralOrdinaryScalar l L F j X).mapHomologicalComplex (.up ℤ)).map
        (scalarPullbackChain l E L ι f P) ≫
      scalarPullbackChain l L F j f
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (integralOperationsPullbackComplexFunctor l F f).map
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι Y F j)
          (.up ℤ)).hom.app P)).f i =
    ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι X F j)
      (.up ℤ)).hom.app ((integralOperationsPullbackComplexFunctor l E f).obj P) ≫
        scalarPullbackChain l E F (j.comp ι) f P).f i := by
  sorry

end WeilConjectures
