/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorModels
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingReductionTensorSquare

/-! # The strict Roos normalization of the coherent tensor comparison

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08TC and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The natural comparison constructed from the coherent system tensor and limit maps.
It uses no chosen completed tensor reindexing comparison.
Source: Stacks 07A4 and 0941
(blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
@[irreducible] def podReindexingLimitTensorComparisonHom
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g) (hA : PodCompletionReindex.Laws l E g A)
    (M N : podReindexingDerived l E Y none) :
    let q := podReindexingTensorFrame l E g A hA M N
    q.F.obj q.CY ⟶ q.CX :=
  let q := podReindexingTensorFrame l E g A hA M N
  q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map q.w₁ ≫ q.RX.map q.w₂ ≫ q.dX.inv

/-- On good complexes, the coherent tensor comparison is the prescribed strict Roos map.
This is a calculation before descent: there is no constructibility assumption and
neither `T.tensor`, its Model law, nor its derived naturality occurs in the equation.

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08TC, 0941.
Proof: expand the representative normalizations of the two tensor realizations.
Their reduction models identify the coherent system tensor with the total tensor of
the two ordinary quotient complexes, and their strict tower comparisons identify
its restriction with the finite tensor tower. Apply A's LimitModel equation to
this coherent total tensor. The naturality of its Roos comparison moves the strict
tower identifications across that equation. The whole-system unit law fixes
A.reduction as the mate of A.limit. The FiniteModel and QuotientGenerators laws
therefore identify its two quotient factors with A.quotient on every scalar-tensor
generator. The normalized system tensor comparison takes a total-tensor generator
to the tensor of its two inverse images. Consequently the induced tower arrow
agrees with T.tower by hGenerators: use the balanced tensor universal property on
each summand, the total direct-sum universal property in each degree, and then
natural-transformation extensionality on the tower. These are equalities of entire
chain maps; quotient transitions are retained. Applying the Roos functor and Q,
and cancelling the intermediate realization isomorphisms, gives the displayed
identity. The target factor is the ordinary inverse-image localization comparison
on each of P and Q, followed by the specified tensor realization. The argument
also applies to zero complexes and the empty scheme.
(blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem podReindexing_tensor_roos_normalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (_hGenerators : PodCompletedTensorReindex.Generators l E g A T)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    letI : (isoReductionIntegralInverse l E g).Additive :=
      isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
    HEq (podReindexingLimitTensorComparisonHom l E g A hA
        (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj) ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj)
          ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
      (integralCompletedTensorComparison l E X).hom.app
        ((podGoodReindex l E g A).obj P, (podGoodReindex l E g A).obj Q))
      ((podOrdinaryReindex l E g).map
        ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map
        ((A.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))).hom ≫
          integralOperationsRoosFunctor.map (T.tower P Q).hom)) := by sorry

end WeilConjectures
