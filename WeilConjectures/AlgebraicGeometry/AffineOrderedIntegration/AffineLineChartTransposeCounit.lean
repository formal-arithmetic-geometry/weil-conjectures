/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison

/-! # The specified chart transpose evaluated with the standing counit

Source: projection-purity agreement, inverse-transpose calculation.
(blueprint: lem-pur-affine-line-chart-transpose-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor

private theorem transported_rightAdjointUniq_inverse
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} {R S : D ⥤ C}
    (adj : F ⊣ R) (adj' : G ⊣ S) (e : G ≅ F)
    {X : C} {Y : D} (a : X ⟶ R.obj Y) :
    (adj'.homEquiv _ _).symm
        (a ≫ (adj.rightAdjointUniq (adj'.ofNatIsoLeft e)).hom.app Y) =
      e.hom.app X ≫ (adj.homEquiv _ _).symm a := by
  have h : ((adj'.ofNatIsoLeft e).homEquiv _ _).symm
      (a ≫ (adj.rightAdjointUniq (adj'.ofNatIsoLeft e)).hom.app Y) =
      (adj.homEquiv _ _).symm a := by
    rw [Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
    rfl
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply] at h
  apply (cancel_epi (e.inv.app X)).1
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using h

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

/-- The exact inverse-transpose formula, retaining both site-comparison conventions.

Source: projection-purity agreement, final paragraph, inverse-transpose calculation
(blueprint: lem-pur-affine-line-chart-transpose-counit).

Proof: expand the specified Hom chain. The comparison-pullback map of the ordinary
transpose, followed by the ordinary right-adjoint uniqueness map, is the comparison
pullback of their composite. Apply the standing counit formula on an ordinary origin.
Naturality and right-adjoint uniqueness replace the inverse ordinary transpose by
precomposition with the inverse ordinary compactification comparison. Naturality of
the comparison adjunction moves this precomposition out. The two inverse laws cancel
the chart adjunction and comparison adjunction. The standing upstream site comparison
and the specified chart site comparison remain visible; neither can be replaced by
the other without an additional normalization identity. -/
theorem lineChartTranspose_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [CompactSpace Y]
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification Y)).IsLeftAdjoint]
    (M : Plus A (AffineSpace PUnit.{u + 1} Y))
    (W : Scheme.FixedEtaleOriginWitness _ A M) (K : Plus A Y)
    (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification Y)).obj M.obj ⟶ K.obj) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
      (specifiedExceptionalHomEquiv A (affineTraceLineCompactification Y) M W K a ≫
        (lineExceptionalIso A Y K.obj).hom) ≫
      rightDerivedUpperShriekCounit (AffineSpace PUnit.{u + 1} Y ↘ Y) K.obj K.property =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} Y ↘ Y)).map W.iso.inv ≫
      (rightDerivedLowerShriekComparisonIso (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} Y ↘ Y)).hom.app W.complex ≫
      (comparison A Y).map ((Etale.rightDerivedLowerShriekIso A
        (affineTraceLineCompactification Y)).inv.app W.complex.obj) ≫
      (fixedCompactSupportComparisonIso A (affineTraceLineCompactification Y)).inv.app
        W.complex ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (affineTraceLineCompactification Y)).map W.iso.hom ≫ a := by
  let c := affineTraceLineCompactification Y
  let f := AffineSpace PUnit.{u + 1} Y ↘ Y
  let Q := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let C := comparison A (AffineSpace PUnit.{u + 1} Y)
  let adj := Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
  let adj' := Etale.rightDerivedUpperShriekAdjunction A f
  let e := (Etale.rightDerivedLowerShriekIso A c).symm
  let b := (fixedCompactSupportComparisonIso A c).inv.app W.complex ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map W.iso.hom ≫ a
  let h := adj.homEquiv _ _
    ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).homEquiv _ K.obj b)
  let t := (adj.rightAdjointUniq (adj'.ofNatIsoLeft e)).hom.app
    ((comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor.obj K.obj)
  have hs : specifiedExceptionalHomEquiv A c M W K a ≫
      (lineExceptionalIso A Y K.obj).hom = W.iso.inv ≫ C.map (h ≫ t) := by
    change (W.iso.inv ≫ C.map h) ≫ C.map t = W.iso.inv ≫ C.map (h ≫ t)
    rw [C.map_comp, Category.assoc]
  rw [hs]
  erw [Functor.map_comp, Category.assoc]
  erw [rightDerivedLowerShriek_map_mapDerivedCategory_map_comp_counit f
    W.complex.property K.property (h ≫ t)]
  erw [transported_rightAdjointUniq_inverse adj adj' e h]
  erw [Adjunction.homEquiv_naturality_left_symm]
  dsimp only [h]
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp only [b, e, Iso.symm_hom, Iso.app_hom]
  rfl

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
