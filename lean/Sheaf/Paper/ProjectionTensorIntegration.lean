/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.Paper.ProjectionUnitIntegration
public import Sheaf.Paper.AffineOrderedIntegrationTransposes

/-! # Tensoring the coefficient-unit integration transpose

Source: the coefficient tensor calculation and the canonical reassociations in
lem-pur-projection-purity-agreement, Steps 7--8.
(blueprint: lem-pur-projection-tensor-integration).
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
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AffineSpacePurity

/-- Tensor the independently constructed unit integration mate and then apply the
specified exceptional tensor arrow. After the fixed source and exceptional
coordinates this is the integration transpose with coefficients. No diagonal
orientation or smooth purity arrow occurs in this assertion.
Source: the coefficient tensor calculation, Steps 7--8, and the final canonical
reassociations of lem-pur-projection-purity-agreement
(blueprint: lem-pur-projection-tensor-integration).

Proof: first work on the ordinary etale site with representative Ke. Use its
finite Tor interval and bounded constructibility to apply the compact projection
formula both at the shifted Tate coefficient and at the dualizing object.
The ordinary unit transpose is diagonalAffineMate: its trace is the ordered
affine counit after inverse coefficient descent and inverse compact-support
comparison. Naturality of the inverse projection in its first variable moves
this unit transpose through the projection. The adjunction triangle identifies
its counit composite with that trace. The tensor-trace transpose identity
therefore gives theta composed with tensor of the unit transpose equal to the
coefficient integration transpose. Transport this equation by the exact site
comparison; its monoidal and pullback comparisons identify the sources, and the
bounded exceptional Hom bijection identifies the targets. Its comparison-unit
factor is exactly the last factor of smoothPurityTheta. Transport through eK.
The pure-root transition from diagonalExponent to exponent is the specified
root-power map: exponent independence of the normalized projective-line trace
identifies the two traces and their transposes. Induct through the ordered
Tate tensor powers: the successor is precisely projectionTensorStep, and its
action gives projectionSourceIso after smoothPurityReassociation. No factors
are permuted and the shifts are even. At positive rank the target comparison
is identity. At zero use the identity adjunction: its comparison counit is
projectionTargetMap and the inverse-image and tensor-unit isomorphisms give
projectionSourceIso. These equations also hold for zero coefficients and empty
bases. Thus the displayed equality uses the actual coordinate maps on both sides. -/
theorem projection_tensor_integration
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring (projectionSetting F C E n)) Y)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (hKe : etaleFiniteTor (projectionSetting F C E n).Coefficient Y Ke)
    (eK : (ProEtale.VectorIntegrationSite.comparison
      (projectionSetting F C E n).Coefficient Y).obj Ke ≅ K.obj) (d : ℕ) :
    let P := projectionSetting F C E n
    letI := (projection_geometry Y d).1
    letI := (projection_geometry Y d).2
    (P.smoothPurityReassociation (iteratedAffineLine Y d) d
      ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K.obj)).hom ≫
      ((smoothPurityTensor P.Coefficient (iteratedAffineLine Y d)).obj
        ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K.obj)).map
          (projectionUnitIntegration P Y aY d) ≫
      P.smoothPurityTheta (iteratedAffineLineProj Y d) K.obj Ke eK ≫
      projectionTargetMap F C E n Y aY K.obj d =
    (projectionSourceIso F C E n Y aY K.obj d).hom ≫
      ProEtale.AffineOrderedIntegration.integrationTranspose P Y aY K Ke hKe eK d := by sorry

/-- The presentation-level coordinate equation underlying the final assembly.
It is the tensor integration equation before transport through the intrinsic
realization equivalence; its target is the explicit affine comparison coordinate.
Source: Steps 7--14 of lem-pur-projection-purity-agreement.
(blueprint: lem-pur-projection-presentation-coordinate).

Proof: the presentation tensor map is the tensor with the inverse diagonal orientation
followed by theta; by `projection_diagonal_unit_integration` that inverse is the unit
integration mate. Then `projection_tensor_integration` says the composite followed by
projectionTargetMap is projectionSourceIso followed by the integration transpose, which
is affineSpacePurityComparison by `ordered_integration_transposes`. Compose with the
inverse of the invertible projectionTargetMap. -/
theorem projection_presentation_coordinate
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring (projectionSetting F C E n)) Y)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (hKe : etaleFiniteTor (projectionSetting F C E n).Coefficient Y Ke)
    (eK : (ProEtale.VectorIntegrationSite.comparison
      (projectionSetting F C E n).Coefficient Y).obj Ke ≅ K.obj) (d : ℕ) :
    let P := projectionSetting F C E n
    letI : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
    letI : (iteratedAffineLine Y d).Over (Spec (.of P.field.k)) :=
      ⟨towerBase aY d⟩
    letI : (iteratedAffineLineProj Y d).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
    letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (LocallyOfFiniteType aY)
    letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (QuasiCompact aY)
    letI := (projection_geometry Y d).1
    letI := (projection_geometry Y d).2
    letI := projection_smooth Y d
    letI := projectionTarget_isIso F C E n Y aY K Ke hKe eK d
    (P.smoothPurityReassociation (iteratedAffineLine Y d) d
      ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K.obj)).hom ≫
      P.smoothPurityTensorMapInPresentation (iteratedAffineLineProj Y d) d
        (Y ↘ Spec (.of P.field.k)) K.obj Ke eK =
    (projectionSourceIso F C E n Y aY K.obj d).hom ≫
      affineSpacePurityComparison P Y aY K Ke hKe eK d ≫
        inv (projectionTargetMap F C E n Y aY K.obj d) := by
  intro P
  let := (projection_geometry Y d).1
  let := (projection_geometry Y d).2
  let := projection_smooth Y d
  let := projectionTarget_isIso F C E n Y aY K Ke hKe eK d
  have hu := projection_diagonal_unit_integration P Y aY d
  have ht := projection_tensor_integration F C E n Y aY K Ke hKe eK d
  have ho := (ProEtale.AffineOrderedIntegration.ordered_integration_transposes
    P Y aY K Ke hKe eK).1 d
  have key : (P.smoothPurityReassociation (iteratedAffineLine Y d) d
      ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K.obj)).hom ≫
      P.smoothPurityTensorMapInPresentation (iteratedAffineLineProj Y d) d
        aY K.obj Ke eK ≫
      projectionTargetMap F C E n Y aY K.obj d =
      (projectionSourceIso F C E n Y aY K.obj d).hom ≫
        affineSpacePurityComparison P Y aY K Ke hKe eK d := by
    have hG : P.smoothPurityTensorMapInPresentation (iteratedAffineLineProj Y d) d
        aY K.obj Ke eK =
        ((smoothPurityTensor P.Coefficient (iteratedAffineLine Y d)).obj
          ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K.obj)).map
            (P.projectionUnitIntegration Y aY d) ≫
          P.smoothPurityTheta (iteratedAffineLineProj Y d) K.obj Ke eK := by
      dsimp only [smoothPurityTensorMapInPresentation]
      rw [hu]
      rfl
    simp only [hG, ← ho]
    exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ht
  exact ((IsIso.eq_comp_inv (projectionTargetMap F C E n Y aY K.obj d)).2
    ((Category.assoc _ _ _).trans key)).trans (Category.assoc _ _ _)

/-- The intrinsic smooth map is represented by the explicit presentation composite.
The structures over k are those of the base map aY and the tower, as in the item.
Source: Steps 1--3 and 7--14 of lem-pur-projection-purity-agreement.
(blueprint: lem-pur-projection-intrinsic-presentation).

Proof: by definition the smooth map is the realization of the reassociation followed by
the unique tensor map, and the unique tensor map equals its presentation formula at the
etale presentation (Ke, eK). The realization functor preserves composition, so the
claim is the realization of the presentation coordinate equation
`projection_presentation_coordinate`, whose right side is the defining composite of
`projectionAffineInPresentation`. -/
theorem projection_intrinsic_presentation
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k)) (d : ℕ)
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y K)
    (hb : boundedBelow (projectionSetting F C E n).Coefficient Y
      ((Scheme.sfIntrinsicDerivedEquivalence Y (projectionSetting F C E n).Ring).inverse.obj K))
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (hKe : etaleFiniteTor (projectionSetting F C E n).Coefficient Y Ke)
    (eK : (ProEtale.VectorIntegrationSite.comparison
      (projectionSetting F C E n).Coefficient Y).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence Y (projectionSetting F C E n).Ring).inverse.obj K) :
    let P := projectionSetting F C E n
    letI : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
    letI : (iteratedAffineLine Y d).Over (Spec (.of P.field.k)) := ⟨towerBase aY d⟩
    letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (LocallyOfFiniteType aY)
    letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (QuasiCompact aY)
    letI : LocallyOfFiniteType (iteratedAffineLine Y d ↘ Spec (.of P.field.k)) :=
      (tower_geometry aY d).1
    letI : QuasiCompact (iteratedAffineLine Y d ↘ Spec (.of P.field.k)) :=
      (tower_geometry aY d).2.1
    letI : (iteratedAffineLineProj Y d).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
    letI := (projection_geometry Y d).1
    letI := (projection_geometry Y d).2
    letI := projection_smooth Y d
    P.smoothPurityMap (iteratedAffineLineProj Y d) d K hK =
      (Scheme.sfIntrinsicDerivedEquivalence (iteratedAffineLine Y d) P.Ring).functor.map
        (projectionAffineInPresentation F C E n Y aY
          ⟨(Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K, hb⟩ Ke hKe eK d) := by
  intro P
  let : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  let : (iteratedAffineLine Y d).Over (Spec (.of P.field.k)) := ⟨towerBase aY d⟩
  let : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aY)
  let : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact aY)
  let : LocallyOfFiniteType (iteratedAffineLine Y d ↘ Spec (.of P.field.k)) :=
    (tower_geometry aY d).1
  let : QuasiCompact (iteratedAffineLine Y d ↘ Spec (.of P.field.k)) :=
    (tower_geometry aY d).2.1
  let : (iteratedAffineLineProj Y d).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let := (projection_geometry Y d).1
  let := (projection_geometry Y d).2
  let := projection_smooth Y d
  let Kp : Plus P.Coefficient Y :=
    ⟨(Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K, hb⟩
  have hc := (P.existsUnique_smoothPurityTensorMap (iteratedAffineLineProj Y d) d K
    hK).exists.choose_spec Ke eK
  have hp := projection_presentation_coordinate F C E n Y aY Kp Ke hKe eK d
  dsimp only [smoothPurityMap, smoothPurityTensorMap]
  simp only [hc]
  exact (Functor.map_comp _ _ _).symm.trans (congrArg _ hp)

end WeilConjectures.PurityFiniteSetting
