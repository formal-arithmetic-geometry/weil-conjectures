/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
import WeilConjectures.AlgebraicGeometry.SpecifiedExceptionalStandingIso
import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison

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

/-- Evaluating the normalized line comparison by the actual standing counit gives
the canonical compactification comparison followed by chart augmentation.

Source: projection-purity agreement, final paragraph, inverse-transpose calculation
(blueprint: lem-pur-affine-line-standing-transpose-expanded).

Proof: factor the source-coordinate equality out of compact support. Expand the chart
comparison as the specified Hom transpose of augmentation. Apply
specifiedExceptionalStandingIso_counit to its retained ordinary source, then recombine the source
coordinate equality with the inverse witness isomorphism by functoriality. This
uses the normalized relative representing-object comparison; its transport identity
accounts for the difference of the standing and specified site comparisons. -/
theorem lineComparison_counit_expanded
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
    let W := sourceWitness P.coefficients.l P.extension (P.level - 1) Y P.level
      (annihilates P) K.obj Ke hKe eK
    (AffineLineEvaluation.support P aY (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
        (lineComparison P Y aY K Ke hKe eK) ≫
      AffineLineEvaluation.counit P aY (AffineSpace PUnit.{u + 1} Y ↘ Y) K =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
        (eqToHom (lineSource_obj_eq P Y K.obj) ≫ W.iso.inv) ≫
      (fixedCompactSupportOriginIso (Ring P)
        (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))
        (affineTraceLineCompactification Y)).hom.app W.complex ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
        (affineTraceLineCompactification Y)).map W.iso.hom ≫
      augmentation P.coefficients.l P.extension (P.level - 1) Y P.level
        (annihilates P) (primeUnit P Y aY) P.field.k aY K.obj Ke hKe eK := by
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  let W := sourceWitness P.coefficients.l P.extension (P.level - 1) Y P.level
    (annihilates P) K.obj Ke hKe eK
  let M : Plus (Ring P) (AffineSpace PUnit.{u + 1} Y) :=
    ⟨source P.coefficients.l P.extension (P.level - 1) Y P.level (annihilates P) K.obj,
      source_plus P.coefficients.l P.extension (P.level - 1) Y P.level
        (annihilates P) K.obj Ke hKe eK⟩
  have ht := specifiedExceptionalStandingIso_counit (Ring P)
    (affineTraceLineCompactification Y) M W K
    (augmentation P.coefficients.l P.extension (P.level - 1) Y P.level
      (annihilates P) (primeUnit P Y aY) P.field.k aY K.obj Ke hKe eK)
  have ht' := congrArg (fun z ↦
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
        (eqToHom (lineSource_obj_eq P Y K.obj)) ≫ z) ht
  simpa only [AffineLineEvaluation.support, AffineLineEvaluation.counit, lineComparison,
    affineLinePurityComparison, comparisonFromOrigin, Functor.map_comp, Category.assoc]
    using ht'

/-- Cancel a source-coordinate isomorphism after compact-support transport.
Source: source-coordinate cancellation in the inverse-transpose calculation
(blueprint: lem-route-line-comparison-counit). -/
private theorem source_transport_cancel
    {C D : Type*} [Category* C] [Category* D] (F G : C ⥤ D)
    {V M N : C} {K : D} (e : V ≅ M) (w : N ≅ M)
    (c : F.obj N ⟶ G.obj N) (a : G.obj M ⟶ K) :
    F.map (e.hom ≫ w.inv) ≫ c ≫ G.map w.hom ≫ a =
      (F.map (w ≪≫ e.symm).inv ≫ c ≫ G.map (w ≪≫ e.symm).hom) ≫
        G.map e.hom ≫ a := by
  have hc : G.map e.inv ≫ G.map e.hom = 𝟙 _ := by
    rw [← G.map_comp, e.inv_hom_id, G.map_id]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    G.map_comp, Category.assoc]
  rw [reassoc_of% hc]

set_option maxHeartbeats 1600000 in
-- Normalizing the large derived-category source expressions needs additional heartbeats.
/-- Inverse-transposing the standing line comparison gives its independently defined
coefficient evaluation, including canonical change of compactification.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, final paragraph, and the expanded
ordered-transpose proof, Steps 3--4
(blueprint: lem-route-line-comparison-counit).

Proof: the expanded counit identity gives the fixed change of compactification
followed by augmentation. Unfold standingEvaluation, its retained origin, and its
chart evaluation. The source-coordinate isomorphism and its inverse cancel, so the
result is exactly the expanded identity. The normalized representing-object comparison
in lineComparison accounts for the standing counit's site-comparison normalization. -/
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
    AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK := by
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  rw [lineComparison_counit_expanded]
  let W := sourceWitness P.coefficients.l P.extension (P.level - 1) Y P.level
    (annihilates P) K.obj Ke hKe eK
  have h := source_transport_cancel
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} Y ↘ Y))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
      (affineTraceLineCompactification Y))
    (eqToIso (lineSource_obj_eq P Y K.obj)) W.iso
    ((fixedCompactSupportOriginIso (Ring P)
      (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))
      (affineTraceLineCompactification Y)).hom.app W.complex)
    (augmentation P.coefficients.l P.extension (P.level - 1) Y P.level
      (annihilates P) (primeUnit P Y aY) P.field.k aY K.obj Ke hKe eK)
  simpa only [W, AffineLineEvaluation.support, rightDerivedLowerShriek,
    AffineLineEvaluation.standingEvaluation, AffineLineEvaluation.changeSupport,
    AffineLineEvaluation.lineWitness, AffineLineEvaluation.evaluation,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    eqToIso.hom] using h

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
