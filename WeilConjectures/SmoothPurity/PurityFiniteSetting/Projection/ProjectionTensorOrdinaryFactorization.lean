/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionTensorOrdinaryData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionUnitIntegration
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionUnitOrderedTrace
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.SmoothPurityTensorTrace

/-! # Factorization of the tensor-unit mate through ordinary coefficient coordinates

Source: projection purity agreement, the coefficient tensor calculation.
(blueprint: lem-pur-projection-tensor-ordinary-factorization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open ProEtale ProEtale.AffineSpacePurity ProEtale.VectorIntegrationSite

private theorem reassociate_three
    {D : Type*} [Category* D] {V W X Y Z : D}
    (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (t : Y ⟶ Z) :
    a ≫ b ≫ c ≫ t = (a ≫ b ≫ c) ≫ t := by
  simp only [Category.assoc]

set_option maxHeartbeats 1600000 in
-- The fixed coefficient aliases require extra reduction in the tensor comparison.
/-- The tensor of the independent unit integration followed by theta factors
through the specified ordinary source and coefficient adjunct.

Source: projection purity agreement, coefficient tensor calculation and exponent
normalization. (blueprint: lem-pur-projection-tensor-ordinary-factorization)

Proof: express the unit integration with the ordered trace and the inverse
root transition by projectionUnitIntegration_orderedTrace. Naturality of the
ordinary adjunction moves the inverse root transition outside its adjunct.
Functoriality splits its comparison image and its tensor with the pullback of K.
The smooth tensor comparison theorem then moves the remaining ordinary adjunct
through theta. The ordinary tensor-trace identity identifies that composite
with the coefficient adjunct of the ordered trace. The remaining source
factors are exactly projectionTensorOrdinarySourceIso, and its target factors
are exactly projectionCoefficientMate. No exceptional purity is used. -/
theorem projection_tensor_ordinary_factorization
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : ProEtale.AffineSpacePurity.C (projectionSetting F C E n).Coefficient Y)
    (H : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (e : (comparison (projectionSetting F C E n).Coefficient Y).obj H ≅ K) (d : ℕ) :
    let P := projectionSetting F C E n
    letI := (projection_geometry Y d).2
    (P.smoothPurityReassociation (iteratedAffineLine Y d) d
      ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K)).hom ≫
      ((smoothPurityTensor P.Coefficient (iteratedAffineLine Y d)).obj
        ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K)).map
          (projectionUnitIntegration P Y aY d) ≫
      P.smoothPurityTheta (iteratedAffineLineProj Y d) K H e =
    (projectionTensorOrdinarySourceIso F C E n Y aY K H e d).hom ≫
      projectionCoefficientMate F C E n Y aY K H e d := by
  intro P
  let := (projection_geometry Y d).2
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  let p := iteratedAffineLineProj Y d
  let W := ProEtale.AffineOrderedIntegration.etaleCoefficient P Y d
  let t := ProEtale.AffineOrderedIntegration.ordinaryTrace P Y aY d
  let adj := Etale.rightDerivedUpperShriekAdjunction P.Coefficient p
  have hu := projectionUnitIntegration_orderedTrace F C E n Y aY d
  dsimp only at hu
  erw [Adjunction.homEquiv_naturality_left, Functor.map_comp] at hu
  rw [hu]
  have hc := smoothPurityTheta_coefficient P p K H e W (adj.homEquiv _ _ t)
  have ht := smoothPurityEtaleTheta_trace P.Coefficient p W t H
  change _ = adj.homEquiv _ _ (ordinaryCoefficientTrace P.Coefficient p W t H) at ht
  dsimp only at hc
  erw [ht] at hc
  erw [Functor.map_comp] at hc
  simp only [Category.assoc] at hc
  dsimp only [projectionTensorOrdinarySourceIso, projectionCoefficientMate]
  dsimp only [P, p, W, t, adj] at *
  erw [Functor.map_comp, Functor.map_comp]
  dsimp only [Iso.trans, Functor.mapIso]
  simp only [Category.assoc]
  erw [hc]
  exact reassociate_three _ _ _ _

end WeilConjectures.PurityFiniteSetting
