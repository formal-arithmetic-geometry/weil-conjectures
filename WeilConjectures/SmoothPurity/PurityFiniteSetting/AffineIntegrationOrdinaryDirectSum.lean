/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DualizingUnitComposite
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPastingData
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization
import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-! # Direct-sum integration in ordinary coefficient-unit coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Reduction of the ordinary orientation square to the three concrete integration
adjuncts, with the specified finite-coordinate block chart.
Source: composition proof Step 1, trivial-frame identification and cancellation.
(blueprint: new-pur-affine-integration-ordinary-coordinate-reduction).

Proof: construct q's chart from the unique isomorphism between its block pullback square
and the standard affine-space pullback square. The charts of p and qp are the specified
ordered tower isomorphisms; the latter is over qp by the block projection equation.
Cancel the three orientation isomorphisms. The coordinate normalization theorem replaces
each inverse orientation by its actual ordered-counit adjunct. Expanding the bifunctor
isomorphism gives precisely the reversed two factors displayed below. No direct-sum
identity is assumed in this reduction, and the same construction handles both zero ranks. -/
theorem affineIntegration_ordinary_directSum_iff_coordinateGamma (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
    letI := DiagonalPasting.affineDimension e B
    letI : SmoothOfRelativeDimension (d + e)
        (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) :=
      smoothOfRelativeDimension_comp (n := d) (m := e)
        (DiagonalPasting.q d e B) (DiagonalPasting.pr e B)
    letI := P.noetherian aB
    letI := P.noetherian (DiagonalPasting.pr e B ≫ aB)
    letI := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
    letI := Dnc.compactifiable P (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB)
    letI := Dnc.compactifiable P (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB
    let t := Etale.projectiveLineTraceTransport P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates
    let D := fun (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) ↦
      Etale.projectiveLineTraceDatum P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates T hT
    let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
    let γq := AffineOrdinaryIntegrationCoordinates.gamma P d (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB)
      (AffineOrdinaryIntegrationCoordinates.blockChart B d e)
      (AffineOrdinaryIntegrationCoordinates.blockChart_over B d e) N t D
    let γp := AffineOrdinaryIntegrationCoordinates.gamma P e (DiagonalPasting.pr e B) aB
      (affineTraceAffineSpaceIso B e).symm
      (AffineOrdinaryIntegrationCoordinates.tower_chart_over B e) N t D
    let γh := AffineOrdinaryIntegrationCoordinates.gamma P (d + e)
      (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB
      (affineTraceAffineSpaceIso B (d + e)).symm
      ((AffineOrdinaryIntegrationCoordinates.tower_chart_over B (d + e)).trans
        (DiagonalPasting.affineGeometry d e B).2.2.2.1.symm) N t D
    (P.affineIntegrationOrdinarySigma (DiagonalPasting.q d e B) (DiagonalPasting.pr e B) ≫
        (P.chartOrdinaryOrientation (d + e)
          (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB).hom =
      (compatibleBifunctorIso
        (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) (DiagonalPasting.A (d + e) B))
        (P.chartOrdinaryOrientation d (DiagonalPasting.q d e B)
          (DiagonalPasting.pr e B ≫ aB))
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (DiagonalPasting.q d e B)).leftDerivedFunctor.mapIso
          (P.chartOrdinaryOrientation e (DiagonalPasting.pr e B) aB))).hom ≫
        (P.affineIntegrationOrdinaryMu d e (DiagonalPasting.q d e B)
          (DiagonalPasting.pr e B ≫ aB)).hom) ↔
    γh = (P.affineIntegrationOrdinaryMu d e (DiagonalPasting.q d e B)
        (DiagonalPasting.pr e B ≫ aB)).inv ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient)
        (DiagonalPasting.A (d + e) B)).obj
          (P.diagonalTwistEtale (DiagonalPasting.A (d + e) B) d)).map
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (DiagonalPasting.q d e B)).leftDerivedFunctor.map γp) ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient)
        (DiagonalPasting.A (d + e) B)).map γq).app
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (DiagonalPasting.q d e B)).leftDerivedFunctor.obj
            (P.diagonalOrdinaryDualizing (DiagonalPasting.pr e B))) ≫
      P.affineIntegrationOrdinarySigma (DiagonalPasting.q d e B) (DiagonalPasting.pr e B) := by
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
  let := DiagonalPasting.affineDimension e B
  let : SmoothOfRelativeDimension (d + e)
      (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) :=
    smoothOfRelativeDimension_comp (n := d) (m := e)
      (DiagonalPasting.q d e B) (DiagonalPasting.pr e B)
  let := P.noetherian aB
  let := P.noetherian (DiagonalPasting.pr e B ≫ aB)
  let := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
  let := Dnc.compactifiable P (DiagonalPasting.q d e B)
    (DiagonalPasting.pr e B ≫ aB)
  let := Dnc.compactifiable P (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  let D := fun (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) ↦
    Etale.projectiveLineTraceDatum P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates T hT
  let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
  have hq := AffineOrdinaryIntegrationCoordinates.orientation_inv P d
    (DiagonalPasting.q d e B) (DiagonalPasting.pr e B ≫ aB)
    (AffineOrdinaryIntegrationCoordinates.blockChart B d e)
    (AffineOrdinaryIntegrationCoordinates.blockChart_over B d e) N t D
  have hp := AffineOrdinaryIntegrationCoordinates.orientation_inv P e
    (DiagonalPasting.pr e B) aB (affineTraceAffineSpaceIso B e).symm
    (AffineOrdinaryIntegrationCoordinates.tower_chart_over B e) N t D
  have hh := AffineOrdinaryIntegrationCoordinates.orientation_inv P (d + e)
    (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB
    (affineTraceAffineSpaceIso B (d + e)).symm
    ((AffineOrdinaryIntegrationCoordinates.tower_chart_over B (d + e)).trans
      (DiagonalPasting.affineGeometry d e B).2.2.2.1.symm) N t D
  dsimp only
  rw [AffineOrdinaryIntegrationCoordinates.orientation_square_iff_inverse]
  simp only [compatibleBifunctorIso, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
    hq, hp, hh, Category.assoc]
  rfl

/-- Ordinary normalized integration is multiplicative on the two coordinate blocks.
This is an equation of ordinary etale arrows, before any pro-etale site transport.
Source: composition proof Step 1, normalized vector-integration direct sums.
(blueprint: new-pur-affine-integration-ordinary-direct-sum).

Proof: use the free coordinate modules of ranks d and e over B and their concatenated
basis to identify the total vector bundle with A^(d+e), its second projection with
pr_e, and the projection to the second bundle with q. Apply
vectorIntegrationCounit_directSum to the integration-normalized gamma of the first
bundle. Normalized gamma is unique by its counit equation, so the two existential
normalized gammas are the specified vectorBundlePurity maps. Trivial-frame integration
and ordered_integration_transposes identify these with the inverses of the ordinary
diagonal orientations, including q viewed as a trivial rank-d projection over A^e.
The ordered associator becomes the inverse of affineIntegrationOrdinaryMu; the
second-factor gamma becomes the tensor transpose at the dualizing object of pr_e.
The compact-support mate becomes dualizingCompositeConjugate. Cancel the three
invertible gamma factors to obtain the displayed orientation equation. All source
Tate powers have even shifts; the concatenation keeps the d block before the e block.
Zero ranks use the normalized identity gamma, and empty bases give the same equation.
-/
theorem affineIntegration_ordinary_directSum (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
    letI := DiagonalPasting.affineDimension e B
    letI : SmoothOfRelativeDimension (d + e)
        (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) :=
      smoothOfRelativeDimension_comp (n := d) (m := e)
        (DiagonalPasting.q d e B) (DiagonalPasting.pr e B)
    letI := P.noetherian aB
    letI := P.noetherian (DiagonalPasting.pr e B ≫ aB)
    letI := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
    letI := Dnc.compactifiable P (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB)
    letI := Dnc.compactifiable P (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB
    P.affineIntegrationOrdinarySigma (DiagonalPasting.q d e B) (DiagonalPasting.pr e B) ≫
        (P.chartOrdinaryOrientation (d + e)
          (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB).hom =
      (compatibleBifunctorIso
        (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) (DiagonalPasting.A (d + e) B))
        (P.chartOrdinaryOrientation d (DiagonalPasting.q d e B)
          (DiagonalPasting.pr e B ≫ aB))
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (DiagonalPasting.q d e B)).leftDerivedFunctor.mapIso
          (P.chartOrdinaryOrientation e (DiagonalPasting.pr e B) aB))).hom ≫
        (P.affineIntegrationOrdinaryMu d e (DiagonalPasting.q d e B)
          (DiagonalPasting.pr e B ≫ aB)).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
