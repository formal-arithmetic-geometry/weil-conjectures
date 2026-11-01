/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineLineStandingTranspose

/-! # Counit of the first line with the identity compositor

(blueprint: lem-pur-affine-ordered-first-line-counit).
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

private theorem counit_congr (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y]
    (h : f = g) (M : C A X) (K : Plus A Y)
    (t : M ⟶ (rightDerivedUpperShriek A f).obj K.obj) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        (t ≫ (rightDerivedUpperShriekCongr A h).hom.app K.obj) ≫
      rightDerivedUpperShriekCounit g K.obj K.property =
    (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A) h).inv.app M ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map t ≫
      rightDerivedUpperShriekCounit f K.obj K.property := by
  subst g
  simp only [rightDerivedUpperShriekCongr_rfl, rightDerivedLowerShriekCongr_rfl,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.comp_id, Category.id_comp]

/-- The first standing line comparison with the prescribed identity compositor has
the equality-transported coefficient evaluation as its inverse transpose.

Source: projection-purity agreement, final paragraph, first-coordinate normalization.
(blueprint: lem-pur-affine-ordered-first-line-counit).

Proof: substitute into an equality of scheme morphisms to show that exceptional
counits commute with rightDerivedUpperShriekCongr and rightDerivedLowerShriekCongr.
Apply this to q = q followed by id and to lineComparison. The untransported counit
is standingEvaluation by lineComparison_counit. Compose with the lower-shriek
comparison and unfold identityCompositeMap. Normalize the zero-stage coordinate
wrappers to obtain the displayed statement. -/
theorem lineComposite_counit (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    letI : IsNoetherian (iteratedAffineLine Y 0) := tower_noetherian P Y aY 0
    letI : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
      HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y 1)).map
        (lineComparison P Y aY K Ke hKe eK ≫
          identityCompositeMap (AffineLinePurity.Ring P) (lastProjection Y 0) K.obj) ≫
      rightDerivedUpperShriekCounit (iteratedAffineLineProj Y 1) K.obj K.property =
    (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (Category.comp_id (lastProjection Y 0)).symm).inv.app ((lineSource P Y).obj K.obj) ≫
      AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : IsNoetherian (iteratedAffineLine Y 0) := tower_noetherian P Y aY 0
  let : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
    HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
  let H := AffineLineEvaluation.support P aY (iteratedAffineLineProj Y 1)
  let g := lineComparison P Y aY K Ke hKe eK
  let c := identityCompositeMap (AffineLinePurity.Ring P) (lastProjection Y 0) K.obj
  let w := (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
    (Category.comp_id (lastProjection Y 0)).symm).inv.app ((lineSource P Y).obj K.obj)
  let b := AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK
  let e := rightDerivedUpperShriekCounit (iteratedAffineLineProj Y 1) K.obj K.property
  change H.map (g ≫ c) ≫ e = w ≫ b
  have hc := counit_congr (AffineLinePurity.Ring P)
    (Category.comp_id (lastProjection Y 0)).symm
    ((lineSource P Y).obj K.obj) K g
  have hl := lineComparison_counit P Y aY K Ke hKe eK
  simp only [AffineLineEvaluation.support, AffineLineEvaluation.counit] at hl
  have hce : H.map (g ≫ c) ≫ e = w ≫ b := by
    simpa only [H, g, c, e, w, b, identityCompositeMap, AffineLineEvaluation.support,
      iteratedAffineLineProj, iteratedAffineLine, lastProjection, Category.assoc] using
      hc.trans (congrArg (fun z ↦ w ≫ z) hl)
  exact hce

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
