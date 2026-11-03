/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedRightFiniteTor
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Logic.Small.Defs
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitDescentComparison
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteSingleUnitNormalization
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistComposition
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence

/-! # Rank-one source comparison before compact support

Source: projection-purity agreement, final paragraph: normalized last-line evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

attribute [local semireducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
  etaleCategory proCategory sourceEtale

attribute [local semireducible] sourceWitness
attribute [local implicit_reducible] sourceWitness rightDerivedLowerShriek
  Etale.affineTraceOpenLeft affineTraceLineCompactification
  affineTraceTower affineTraceProjection

set_option maxHeartbeats 3200000 in
-- Elaborating the concrete derived-source comparison requires the larger limit.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

private theorem pro_tensor_iso_hom
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M M' L L' : C A X} (e : M ≅ M') (c : L ≅ L') :
    (AffineSpacePurity.tensorIso A X e c).hom = e.hom ⊗ₘ c.hom := rfl

private theorem realizedTensorComparison_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : C A Y)
    (Ke : Etale.DerivedCategoryModule A Y) (W : Etale.DerivedCategoryModule A X)
    (eK : (comparison A Y).obj Ke ≅ K) :
    (realizedTensorComparison A f K Ke W eK).hom =
      (tensorComparison A X ((Etale.ordinaryFinitePullback A f).obj Ke) W).hom ≫
        ((pullback A f).app Ke).hom ▷ (comparison A X).obj W ≫
        (inverseImage A f).map eK.hom ▷ (comparison A X).obj W := by
  unfold realizedTensorComparison tensorPullbackComparison
  simp -implicitDefEqProofs only [id_eq, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    derivedTensor, curriedTensor_map_app, Category.assoc]
  rfl

private theorem line_coefficient_iso
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) :
    lineCoefficientIso P Y aY =
      (comparison (AffineLinePurity.Ring P) (AffineSpace PUnit.{u + 1} Y)).mapIso
        (Etale.ordinaryFiniteShiftedLinePullback (AffineLinePurity.Ring P)
          (exponent P) (annihilates P) (transport P)
          (ProjectiveLine.affineChart Y)
          (affineTraceProjectiveInvertible (exponent P) Y (exponentUnit P Y aY))) := by
  unfold lineCoefficientIso
  simp -implicitDefEqProofs only [eqToIso_refl, Functor.mapIso_refl,
    Iso.refl_trans]
  unfold comparedLinePullback transport
  with_unfolding_all rfl

private theorem line_witness_iso
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : C (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K) :
    (AffineLineEvaluation.lineWitness P Y K Ke hKe eK).iso =
      realizedTensorComparison (AffineLinePurity.Ring P)
        (AffineSpace PUnit.{u + 1} Y ↘ Y) K Ke
        (AffineLinePurity.etaleCoefficient P.coefficients.l P.extension
          (P.level - 1) Y P.level (annihilates P)) eK := by
  unfold AffineLineEvaluation.lineWitness AffineLinePurity.sourceWitness
    AffineLinePurity.sourceComparison
  simp -implicitDefEqProofs only [eqToIso_refl, Functor.mapIso_refl, Iso.refl_trans,
    Iso.refl_symm]
  erw [Iso.trans_refl, Iso.trans_refl]

/-- The geometric rank-one witness and ordered tensor realization agree before
applying compact support.

Source: projection-purity agreement, final paragraph, source reassociations
(blueprint: lem-pur-affine-rank-one-source-realization).

Proof: characterize sourceComparison and sourceReassociation by their defining
HEq equations. Expand both at one and expand ordinarySourceIso using
normalized_source_descent at one. The zero ordinary descent is the inverse tensor
right unitor followed by inverse identity pullback. Tensor associator naturality
and the right-unit coherence cancel these zero factors against the corresponding
ones in coefficientActionComparison. Pullback-composition naturality moves eK
through the tensor comparison. The shifted-line pullback identifies the chart
coefficient with the base shifted Tate line. The remaining ordinary map is
sourceCoordinates followed by rightComparison inverse and the inverse of
ordinaryOrderedRightCoordinates. This equality takes place on the affine line;
it uses no compact-support map, trace, or counit. -/
theorem rankOne_source_realization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    (AffineLineEvaluation.lineWitness P Y K.obj Ke hKe eK).iso ≪≫
        (sourceReassociation P Y aY K.obj 0).symm ≪≫
        (sourceRealization P Y K.obj Ke eK 1).symm =
      (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y 1)).mapIso
        ((CoordinateLine.sourceCoordinates P Y P.level (annihilates P) Ke ≪≫
          (CoordinateLine.rightComparison (AffineLinePurity.Ring P) (exponent P)
            (annihilates P) Y).symm.app Ke) ≪≫
          (ordinaryOrderedRightCoordinates P Y aY Ke 1).symm) := by
  sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
