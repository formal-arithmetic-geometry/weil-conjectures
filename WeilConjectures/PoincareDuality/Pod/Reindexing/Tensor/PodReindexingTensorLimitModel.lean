/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingReductionTensorSquare
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorLimitModelDescent
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCoherentTensorRoos
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Limit realization of the normalized completed tensor reindexing

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/--
The strict normalized tensor equation descends through the product of the two good
complex localizations. The hypotheses record the pure-tensor generator normalization,
the strict model equation and its naturality; the conclusion is the component equation
used by the parent limit-model lemma.

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08TC,
0941. Construct the natural coherent comparison. Its strict Roos normalization
and Model identify it with T.tensor on good representatives after cancelling the
target realization. Choose representatives of the constructible inputs, transport
constructibility across their isomorphisms, and use Naturality to transport this
component equality. Postcompose with the target tensor realization to get the frame
equation. STATEMENT-DISPUTED: the original signature omitted Generators. Simultaneously
negating T.tower and T.tensor preserves Model and Naturality, but changes the equation.
(blueprint: stage3-pod-reindexing-tensor-limit-model-descent).
-/
private theorem podReindexing_tensor_limit_model_descent_legacy
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hGenerators : PodCompletedTensorReindex.Generators l E g A T)
    (_hModel : PodCompletedTensorReindex.Model l E g A T)
    (_hNaturality : PodCompletedTensorReindex.Naturality l E g A T)
    (M N : sfIntegralConstructibleCategory l E Y) :
    let q := podReindexingTensorFrame l E g A hA M.obj N.obj
    let t : q.F.obj q.CY ⟶ q.CX := (T.tensor M N).hom
    q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map (q.w₁ ≫ q.w₂) =
      t ≫ q.dX.hom := by
  classical
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  let κ := podReindexingLimitTensorComparisonHom l E g A hA
  have hrep (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
      (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj)) :
      κ (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj) =
        (T.tensor ⟨DerivedCategory.Q.obj P.obj, hP⟩
          ⟨DerivedCategory.Q.obj Q.obj, hQ⟩).hom := by
    have hs := podReindexing_tensor_roos_normalization l E g A T hA hGenerators P Q
    have hm := _hModel P Q hP hQ
    let e := (integralCompletedTensor l E X).mapIso
      (Iso.prod (goodReindexFactors l E g A P) (goodReindexFactors l E g A Q)) ≪≫
      (integralCompletedTensorComparison l E X).app
        ((podGoodReindex l E g A).obj P, (podGoodReindex l E g A).obj Q)
    apply (cancel_mono e.hom).1
    dsimp only [e, Iso.trans, Functor.mapIso, Iso.prod, Iso.app] at ⊢
    simpa only [κ, goodReindexFactors, id, podGoodReindex, Iso.app_hom,
      Category.assoc, podReindexingTensorFrame] using eq_of_heq (hs.trans hm)
  dsimp only [κ] at hrep
  let L := integralOperationsGoodLocalization l E Y
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  have : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E Y
  have : L.EssSurj := Localization.essSurj L W
  let P := L.objPreimage M.obj
  let Q := L.objPreimage N.obj
  let eM : DerivedCategory.Q.obj P.obj ≅ M.obj := L.objObjPreimageIso M.obj
  let eN : DerivedCategory.Q.obj Q.obj ≅ N.obj := L.objObjPreimageIso N.obj
  let MP : sfIntegralConstructibleCategory l E Y :=
    ⟨DerivedCategory.Q.obj P.obj,
      ObjectProperty.prop_of_iso (sfIntegralConstructible l E Y) eM.symm M.property⟩
  let NQ : sfIntegralConstructibleCategory l E Y :=
    ⟨DerivedCategory.Q.obj Q.obj,
      ObjectProperty.prop_of_iso (sfIntegralConstructible l E Y) eN.symm N.property⟩
  have hk : κ M.obj N.obj = (T.tensor M N).hom := by
    let e := (podOrdinaryReindex l E g).mapIso
      ((integralCompletedTensor l E Y).mapIso (Iso.prod eM eN))
    apply (cancel_epi e.hom).1
    dsimp only [e, Functor.mapIso, Iso.prod]
    rw [limitTensorComparison_naturality l E g A hA _ _ _ _ eM.hom eN.hom]
    rw [hrep P Q MP.property NQ.property]
    exact (_hNaturality MP NQ M N
      (ObjectProperty.homMk eM.hom) (ObjectProperty.homMk eN.hom)).symm
  exact frameFinish _ (T.tensor M N).hom
    ((eq_of_heq (limitTensorComparison_app l E g A hA M.obj N.obj)).symm.trans hk)

/-- The completed tensor comparison is the limit of the coherent system tensor map.
This identifies isomorphisms only; no ordinary tensor comparison or augmentation occurs.
Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08TC, 0941
(blueprint: lem-pod-reindexing-tensor-limit-model).

Proof: take simultaneous flat-term K-flat representatives of M and N. The tensor
realizations pullbackTensorIntegralTensorModel identify both completed tensors with
the limit of the tensor of their coherent reductions. Apply A.limit's LimitModel
normalization to that system tensor. Its restricted tower is the finite tensor tower
by pullbackTensorTensorTower. The system tensor map is the localized cochain map
specified by pullbackTensorSystemComparison; on every total summand it sends the two
factors to their inverse-image unit sections. The whole-system adjunct formula
podReindexing_reduction_inv_mate, computed using LimitModel and the strict quotient
units, identifies A.reduction on these representatives with A.quotient; FiniteModel
and QuotientGenerators give its pure-section formula. Thus the
resulting map on each strict tower level is T.tower by T.Generators. Include quotient
transitions using QuotientTransition and TowerNaturality. After restriction, A's
RoosFst and RoosSnd equations identify both cone coordinates of this map with A.roos
followed by Roos(T.tower). T.Model identifies its localization with T.tensor. Cancel
the representative tensor realization isomorphisms. Naturality of T.tensor and of all
the system comparisons descends the equation to constructible M,N along the product
of the good-complex localizations. No completeness of their ordinary tensor is used;
zero inputs and the empty scheme satisfy the same coordinate equations. -/
theorem podReindexing_tensor_limit_model
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hT : PodCompletedTensorReindex.Laws l E g A T)
    (M N : sfIntegralConstructibleCategory l E Y) :
    let q := podReindexingTensorFrame l E g A hA M.obj N.obj
    let t : q.F.obj q.CY ⟶ q.CX := (T.tensor M N).hom
    q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map q.w₁ ≫ q.RX.map q.w₂ =
      t ≫ q.dX.hom := by
  have h := podReindexing_tensor_limit_model_descent_legacy l E g A T hA
    hT.1 hT.2.2.2.2.1 hT.2.2.2.1 M N
  simpa only [Functor.map_comp, Category.assoc] using h

end WeilConjectures
