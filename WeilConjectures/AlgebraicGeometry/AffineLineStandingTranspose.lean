/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineCompositeTranspose
import WeilConjectures.AlgebraicGeometry.AffineLineChartTransposeCounit

/-! # Counit normalization of the standing affine-line comparison

Source: projection-purity agreement, final paragraph, one-coordinate transpose.
(blueprint: lem-route-line-comparison-counit).
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

/-- Evaluating the standing line comparison by the actual upstream counit retains
its upstream site comparison at the standing compactification.

Source: projection-purity agreement, final paragraph, inverse-transpose calculation
(blueprint: lem-pur-affine-line-standing-transpose-expanded).

Proof: factor the source-coordinate equality out of compact support. Expand the chart
comparison as the specified Hom transpose of augmentation. Apply
lineChartTranspose_counit to its retained ordinary source, then recombine the source
coordinate equality with the inverse witness isomorphism by functoriality. This
calculates the exact remaining comparisons without assuming that the existence-chosen
upstream site comparison equals the specified proper/open counit mate. -/
theorem lineComparison_counit_expanded
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
    let W := sourceWitness P.coefficients.l P.extension (P.level - 1) Y P.level
      (annihilates P) K.obj Ke hKe eK
    (AffineLineEvaluation.support P aY (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
        (lineComparison P Y aY K Ke hKe eK) ≫
      AffineLineEvaluation.counit P aY (AffineSpace PUnit.{u + 1} Y ↘ Y) K =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
        (eqToHom (lineSource_obj_eq P Y K.obj) ≫ W.iso.inv) ≫
      (rightDerivedLowerShriekComparisonIso (ModuleCat.{u + 1} (Ring P))
        (AffineSpace PUnit.{u + 1} Y ↘ Y)).hom.app W.complex ≫
      (comparison (Ring P) Y).map ((Etale.rightDerivedLowerShriekIso (Ring P)
        (affineTraceLineCompactification Y)).inv.app W.complex.obj) ≫
      (fixedCompactSupportComparisonIso (Ring P) (affineTraceLineCompactification Y)).inv.app
        W.complex ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
        (affineTraceLineCompactification Y)).map W.iso.hom ≫
      augmentation P.coefficients.l P.extension (P.level - 1) Y P.level
        (annihilates P) (primeUnit P Y aY) P.field.k aY K.obj Ke hKe eK := by
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  let W := sourceWitness P.coefficients.l P.extension (P.level - 1) Y P.level
    (annihilates P) K.obj Ke hKe eK
  have ht := lineChartTranspose_counit (Ring P) Y
    ⟨source P.coefficients.l P.extension (P.level - 1) Y P.level (annihilates P) K.obj,
      source_plus P.coefficients.l P.extension (P.level - 1) Y P.level
        (annihilates P) K.obj Ke hKe eK⟩ W K
    (augmentation P.coefficients.l P.extension (P.level - 1) Y P.level
      (annihilates P) (primeUnit P Y aY) P.field.k aY K.obj Ke hKe eK)
  have ht' := congrArg (fun z ↦
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
        (eqToHom (lineSource_obj_eq P Y K.obj)) ≫ z) ht
  simpa only [AffineLineEvaluation.support, AffineLineEvaluation.counit, lineComparison,
    affineLinePurityComparison, comparisonFromOrigin, Functor.map_comp, Category.assoc]
    using ht'

/-- Inverse-transposing the standing line comparison gives its independently defined
coefficient evaluation, including canonical change of compactification.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, final paragraph, and the expanded
ordered-transpose proof, Steps 3--4
(blueprint: lem-route-line-comparison-counit).

Planned proof: cancel the chart Hom chain and use ordinary right-adjoint uniqueness
and the ordinary compactification comparison. The proved calculation
lineComparison_counit_expanded performs these cancellations. To conclude the proposed
identity one still needs to identify the upstream standing site comparison with the
specified proper/open site comparison (and restrict the ordinary compactification
comparison to D+). The first identification is not part of the current definitions:
the upstream comparison uses an isomorphism chosen from a bare Nonempty statement,
whereas standingEvaluation uses the specified counit mate. Thus this declaration is
disputed pending a normalization repair. Neither the line comparison's isomorphy nor
any nonvanishing hypothesis addresses that missing identification. -/
-- STATEMENT-DISPUTED: the specified chart Hom chain and changeSupport use
-- fixedCompactSupportComparisonIso, whereas the standing counit uses
-- rightDerivedLowerShriekComparisonIso, whose proper factor is chosen from bare
-- Nonempty. Ordinary right-adjoint uniqueness does not identify these site maps.
-- lineComparison_counit_expanded proves the exact formula with both maps retained.
theorem lineComparison_counit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    (AffineLineEvaluation.support P aY (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
        (lineComparison P Y aY K Ke hKe eK) ≫
      AffineLineEvaluation.counit P aY (AffineSpace PUnit.{u + 1} Y ↘ Y) K =
    AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK := by sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
