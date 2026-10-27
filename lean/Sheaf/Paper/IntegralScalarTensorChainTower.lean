/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.IntegralOperationsScalarComparisonModels
public import Sheaf.Paper.ScalarExtensionComposition

/-! # Scalar completed tensor chain comparisons and coefficient towers

Source: Stacks 07A4, 08TC; coefficient-comparison coherence in the blueprint.
(blueprint: lem-pur-integral-scalar-tensor-chain-tower). -/

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

/-- The normalized completed-tensor Roos chain maps respect coefficient towers.
Source: Stacks 07A4, 08TC; blueprint scalar comparison proof step 9
(blueprint: lem-pur-integral-scalar-tensor-chain-tower).
Proof: on each bidegree generator the two finite-level routes send
c tensor (b tensor ((1 tensor x) tensor (1 tensor y))) to the tensor of
c*j(b) tensor (1 tensor x) with 1 tensor (1 tensor y). The scalar
associator's multiplication and the two tensor comparison formulas give exactly
this equality. Balanced tensor relations, sheafification, and the coproducts in
total degree extend it to the finite total complex, respecting both signed
differential summands. Consecutive reduction compatibility gives equality of
strict tower maps. Project the Roos comparison onto each of its two product
coordinates. Finite freeness commutes with these products, and the finite-level
equality identifies both routes. Product projections are jointly injective,
so the chain maps agree. Zero complexes, identity extensions and arbitrary
unbounded inputs are included. -/
theorem integralScalarTensorChainTower (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l L F j W).mapHomologicalComplex (.up ℤ)).map
        (scalarTensorChain l E L ι W P Q) ≫
      scalarTensorChain l L F j W
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (integralOperationsTensorComplexFunctor l F W).map (CategoryTheory.Prod.mkHom
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app P)
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app Q)) =
    (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
      (.up ℤ)).hom.app ((integralOperationsTensorComplexFunctor l E W).obj (P, Q)) ≫
        scalarTensorChain l E F (j.comp ι) W P Q := by sorry

end WeilConjectures
