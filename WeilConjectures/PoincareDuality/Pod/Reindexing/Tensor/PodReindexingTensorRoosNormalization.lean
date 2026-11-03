/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorRoosStrict
public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRoosRepresentativeSquare
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Strict steps in normalized completed tensor reindexing -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem representative_equivalence
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hgen : PodCompletedTensorReindex.Generators l E g D T)
    [(isoReductionIntegralInverse l E g).Additive]
    [PreservesFiniteLimits (isoReductionIntegralInverse l E g)]
    [PreservesFiniteColimits (isoReductionIntegralInverse l E g)]
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
    (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj)) :
    HEq ((podOrdinaryReindex l E g).map ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
        (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map
          ((D.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj))).hom ≫
            integralOperationsRoosFunctor.map (T.tower P Q).hom))
      ((T.tensor (⟨DerivedCategory.Q.obj P.obj,hP⟩ : sfIntegralConstructibleCategory l E Y)
        (⟨DerivedCategory.Q.obj Q.obj,hQ⟩ : sfIntegralConstructibleCategory l E Y)).hom ≫
        (integralCompletedTensor l E X).map
          (Prod.mkHom ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj)
            ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
        (integralCompletedTensorComparison l E X).hom.app
          ((podGoodReindex l E g D).obj P,(podGoodReindex l E g D).obj Q)) ↔
        (podOrdinaryToCompleted l E g D).app
            ((integralCompletedTensor l E Y).obj
              (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
            ((canonicalIntegralPullbackTensor l E g ⟨_,hP⟩ ⟨_,hQ⟩).hom).hom =
          (T.tensor ⟨_,hP⟩ ⟨_,hQ⟩).hom ≫
            (integralCompletedTensor l E X).map
              (Prod.mkHom
                ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
                ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj))) := by
  let F := integralCompletedTensor l E X
  let B := F.map (Prod.mkHom
    ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
    ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj)))
  let a := (T.tensor ⟨_,hP⟩ ⟨_,hQ⟩).hom
  let r := (podOrdinaryReindex l E g).map
      ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
    (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
    DerivedCategory.Q.map
      ((D.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj))).hom ≫
        integralOperationsRoosFunctor.map (T.tower P Q).hom)
  let c := (podOrdinaryToCompleted l E g D).app
      ((integralCompletedTensor l E Y).obj
        (DerivedCategory.Q.obj P.obj,DerivedCategory.Q.obj Q.obj)) ≫
    ((canonicalIntegralPullbackTensor l E g ⟨_,hP⟩ ⟨_,hQ⟩).hom).hom
  have hβP := ordinaryComparisonIsIso l E g D hD
    (⟨DerivedCategory.Q.obj P.obj,hP⟩ : sfIntegralConstructibleCategory l E Y)
  have hβQ := ordinaryComparisonIsIso l E g D hD
    (⟨DerivedCategory.Q.obj Q.obj,hQ⟩ : sfIntegralConstructibleCategory l E Y)
  have : IsIso (Prod.mkHom
      ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
      ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj))) :=
    (isIso_prod_iff _ _).mpr ⟨hβP, hβQ⟩
  have hB : IsIso B := F.map_isIso _
  have hs :=
    podTensorRoosRepresentativeSquare l E g D hD P Q hP hQ (T.tower P Q) (hgen P Q)
  exact podTensorComparison_cancel F (hb := hB)
    ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.app P.obj)
    ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.app Q.obj)
    ((integralCompletedTensorComparison l E X).app
      ((podGoodReindex l E g D).obj P,(podGoodReindex l E g D).obj Q)) a r B c hs

/-- The strict Roos equation is equivalent to the canonical equation on good
representatives. No naturality of the independently supplied derived tensor family
is assumed, so the conclusion concerns actual localized representatives only.

Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 07A4 and 0941 (legacy proof retained during the coefficient-route migration).

Proof: the representative square identifies the localized strict Roos arrow,
transported through the two representative comparisons and the completion maps,
with the canonical completed tensor arrow. The completion maps on constructible
inputs are invertible by CompleteUnit. Cancel their tensor and the representative
comparison to obtain the equivalence, independently for each pair of representatives.

STATEMENT-DISPUTED: the old generator and tower naturality laws do not
constrain T.tensor. In particular they cannot imply the global Canonical equation.
The repaired statement identifies exactly the equation needed by the parent.
-/
private theorem podReindexingTensorRoosNormalization_model_iff_canonical_legacy
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hgen : PodCompletedTensorReindex.Generators l E g D T) :
    PodCompletedTensorReindex.Model l E g D T ↔
      ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
        (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj)),
        (podOrdinaryToCompleted l E g D).app
            ((integralCompletedTensor l E Y).obj
              (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
            ((canonicalIntegralPullbackTensor l E g ⟨_,hP⟩ ⟨_,hQ⟩).hom).hom =
          (T.tensor ⟨_,hP⟩ ⟨_,hQ⟩).hom ≫
            (integralCompletedTensor l E X).map
              (Prod.mkHom
                ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
                ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj))) := by
  have : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  have : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  have : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  constructor
  · intro h P Q hP hQ
    exact (representative_equivalence l E g D hD T hgen P Q hP hQ).mp (h P Q hP hQ)
  · intro h P Q hP hQ
    exact (representative_equivalence l E g D hD T hgen P Q hP hQ).mpr (h P Q hP hQ)

/-- The canonical derived comparison realizes the normalized strict Roos map.
Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-tensor-roos-normalization).

Proof: take simultaneous flat-term K-flat P,Q. Their finite tensor reductions
are the total tensors of the quotient complexes. The forward generator law
identifies T.tower with the ordinary finite pullback/tensor comparison conjugated
by the two quotient comparisons of D. The quotient-transition squares identify
these comparisons on the entire coherent system, not just its evaluations.
Apply the specified Roos realization: its two cone coordinates are fixed by
D.RoosFst and D.RoosSnd, so the realized map is D.roos followed by Roos(T.tower).
Use D.FiniteModel and D.LimitModel to identify its source and target with the
existing completed operations. D.Unit, D.Counit, and D.PullbackNormalization
identify the resulting derived comparison with the canonical completed
pullback/tensor map after podOrdinaryToCompleted on all three objects.
The assumed Canonical equation and invertibility of the ordinary-to-completed
maps on the complete constructible inputs therefore give the displayed Model
equation by cancellation. Naturality of the strict tower maps ensures this
calculation respects morphisms of representatives. No assertion of equality is
inferred from faithfulness of finite evaluation; the whole-system unit/counit
and the two Roos coordinates are used before localization. Zero representatives
and empty schemes satisfy the same identities. -/
theorem podReindexingTensorRoosNormalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hgen : PodCompletedTensorReindex.Generators l E g D T)
    (hnat : PodCompletedTensorReindex.TowerNaturality l E g D T)
    (hcanonical : PodCompletedTensorReindex.Canonical l E g D T) :
    PodCompletedTensorReindex.Model l E g D T := by
  have hpair := podReindexingTensorRoosNormalization_model_iff_canonical_legacy
    l E g D hD T hgen
  have _ := hnat
  exact hpair.mpr (fun P Q hP hQ ↦ hcanonical ⟨_,hP⟩ ⟨_,hQ⟩)

end WeilConjectures
