/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose

/-! # Inverse transpose of the ordered integration map

(blueprint: lem-pur-affine-ordered-transpose-counit).
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
attribute [local implicit_reducible] compactification proCategory etaleCategory
attribute [local implicit_reducible] rightDerivedLowerShriek
attribute [local irreducible] rightDerivedUpperShriekHomEquiv
  rightDerivedUpperShriekCounit

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- The inverse exceptional transpose of a positive-stage ordered integration map is
sourceComparison followed by its independently defined augmentation.

Source: projection-purity agreement, final paragraph, defining ordered transposes.
(blueprint: lem-pur-affine-ordered-transpose-counit).

Proof: use integrationTranspose_existsUnique to identify its chosen value with
sourceComparison followed by standingTranspose of augmentation. Functoriality of
compact supports separates these factors. The inverse-Hom formula and the inverse
law of rightDerivedUpperShriekHomEquiv cancel standingTranspose, leaving precisely
sourceComparison followed by augmentation. All sources have source_origin. -/
theorem integrationTranspose_counit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map
        (integrationTranspose P Y aY K Ke hKe eK (d + 1)) ≫
      AffineLineEvaluation.counit P aY (iteratedAffineLineProj Y (d + 1)) K =
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map
        (sourceComparison P Y K.obj (d + 1)).hom ≫
      augmentation P Y aY K Ke hKe eK (d + 1) := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let := (projection_geometry Y (d + 1)).1
  let := (projection_geometry Y (d + 1)).2
  have ht : integrationTranspose P Y aY K Ke hKe eK (d + 1) =
      (sourceComparison P Y K.obj (d + 1)).hom ≫
        standingTranspose (AffineLinePurity.Ring P) (iteratedAffineLineProj Y (d + 1))
          _ K.obj (source_origin P Y aY K Ke hKe eK (d + 1)) K.property
          (augmentation P Y aY K Ke hKe eK (d + 1)) := by
    unfold integrationTranspose
    exact eq_of_heq
      (integrationTranspose_existsUnique P Y aY K Ke hKe eK (d + 1)).exists.choose_spec
  simp only [AffineLineEvaluation.counit]
  rw [ht, (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map_comp,
    Category.assoc]
  apply congrArg (fun z ↦
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map
      (sourceComparison P Y K.obj (d + 1)).hom ≫ z)
  simpa only [standingTranspose, rightDerivedUpperShriekHomEquiv_symm_apply,
    AffineLineEvaluation.support] using
    (rightDerivedUpperShriekHomEquiv (iteratedAffineLineProj Y (d + 1))
      (source_origin P Y aY K Ke hKe eK (d + 1)) K.property).symm_apply_apply
      (augmentation P Y aY K Ke hKe eK (d + 1))

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
