module

public import Sheaf.Paper.CompactSupportStrictScalarCompositionPrelude

import Sheaf.Paper.ScalarReductionBalancingComposition
import Sheaf.Paper.StrictScalarComparisonSelection
import Sheaf.Paper.StrictImageReindexComposition

/-! # Support realization of strict scalar comparison

The image-tower comparison is transported through the chosen support models,
reduction balancing, and retained-level maps. This is the support realization
part of the compact-support composition argument.
(blueprint: lem-pur-compact-support-strict-scalar-composition-support-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

private theorem support_pasting
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (I : A ⥤ B) (J : C ⥤ D) (TX : A ⥤ C) (TY : B ⥤ D)
    (aX : A ⥤ A) (aY : B ⥤ B)
    (eX hX pX : C ⥤ C) (eY hY pY : D ⥤ D)
    (χ : I ⋙ TY ⟶ TX ⋙ J)
    (σX : aX ⋙ TX ≅ TX ⋙ eX) (σY : aY ⋙ TY ≅ TY ⋙ eY)
    (rF : aX ⋙ I ≅ I ⋙ aY)
    (rE : eX ⋙ J ≅ J ⋙ eY) (rH : hX ⋙ J ≅ J ⋙ hY)
    (rP : pX ⋙ J ≅ J ⋙ pY)
    (qX : hX ⋙ eX ≅ pX) (qY : hY ⋙ eY ≅ pY)
    {K N : A} {P Q : C} {V : B} {VP VQ : D}
    (b : K ⟶ aX.obj N) (d : TX.obj N ⟶ hX.obj P)
    (a : TX.obj K ⟶ pX.obj Q) (t : P ⟶ Q) (v : VP ⟶ VQ)
    (mF : V ≅ I.obj N) (mP : VP ≅ J.obj P) (mQ : VQ ≅ J.obj Q)
    (ha : a = TX.map b ≫ σX.hom.app N ≫ eX.map d ≫ qX.hom.app P ≫ pX.map t)
    (hs : χ.app (aX.obj N) ≫ J.map (σX.hom.app N) ≫ rE.hom.app (TX.obj N) =
      TY.map (rF.hom.app N) ≫ σY.hom.app (I.obj N) ≫ eY.map (χ.app N))
    (hr : J.map (qX.hom.app P) ≫ rP.hom.app P =
      rE.hom.app (hX.obj P) ≫ eY.map (rH.hom.app P) ≫ qY.hom.app (J.obj P))
    (hm : J.map t ≫ mQ.inv = mP.inv ≫ v) :
    χ.app K ≫ J.map a ≫ rP.hom.app Q ≫ pY.map mQ.inv =
      TY.map (I.map b) ≫ TY.map (rF.hom.app N) ≫ TY.map (aY.map mF.inv) ≫
        σY.hom.app V ≫
        eY.map (TY.map mF.hom ≫ χ.app N ≫ J.map d ≫ rH.hom.app P ≫
          hY.map mP.inv) ≫ qY.hom.app VP ≫ pY.map v := by
  have hnχ := χ.naturality b
  have hne := rE.hom.naturality d
  have hnp := rP.hom.naturality t
  have hnq := qY.hom.naturality mP.inv
  have hnσ := σY.hom.naturality mF.hom
  simp only [Functor.comp_map] at hnχ hne hnp hnq hnσ
  calc
    _ = TY.map (I.map b) ≫ TY.map (rF.hom.app N) ≫
        σY.hom.app (I.obj N) ≫ eY.map (χ.app N) ≫ eY.map (J.map d) ≫
        eY.map (rH.hom.app P) ≫ eY.map (hY.map mP.inv) ≫
        qY.hom.app VP ≫ pY.map v := by
      rw [ha]
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% hnp, ← pY.map_comp, hm, pY.map_comp]
      rw [reassoc_of% hr, reassoc_of% hnq]
      rw [reassoc_of% hne, ← reassoc_of% hnχ, reassoc_of% hs]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hnσ]
      simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

-- Preserve the geometry hypotheses of the existing declaration.
set_option linter.unusedSectionVars false in
/-- The support realization maps are coherent with the composite tower
associator. This is the postcomposition part of the strict compact-support
composition calculation; it contains no image-level mate comparison.
Source: returned comparison Step 11, proof Steps 3--6.
(blueprint: lem-pur-compact-support-strict-scalar-composition-support-realization).
Proof: expand the arrow for F ⊂ L. The selection square is the localized identity
square, so it commutes with the support-model maps for F and those cancel. Arithmetic
selection is restriction along an index functor and acts termwise on the ordinary
proper/open mates, so the F-level selection through the image commutes with the
L/F comparison. Naturality of that comparison moves the F-level balancing in front.
What remains is an equation of isomorphisms under the L-image. The balancing maps
compose: both sides satisfy the counit equation of reductionBalancing_existsUnique,
because the ordinary balancings compose by ((x ⊗ b) ⊗ d) ↦ x ⊗ bd. The image
selections for e and h compose through compositionRetained to the one for h * e.
The L support model is natural in compositionCompleted. -/
theorem supportRealization_coherence
    (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L X)
    (e h : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (hh : PurCompactSupport.Ramification l F L j h) (hhpos : 1 ≤ h)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (comparison l F L j c).app
        ((T l E F i X).obj ((reduction l E X SE).obj M)) ≫
      (image l L c).map ((compositionTower l E F i L j X).hom.app
        ((reduction l E X SE).obj M)) ≫
      (image l L c).map
        ((reductionBalancing l E L (j.comp i) X SE SL (h * e)
          (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos)).hom.app M) ≫
      (reindexImage l L c (h * e) (one_le_mul hhpos hepos)).inv.app
        ((reduction l L X SL).obj
          ((pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) X)).obj M)) ≫
      (subsequence l L Y (h * e)).map
        ((supportModel l L c SL).inv.app
          ((pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) X)).obj M)) =
    (T l F L j Y).map
        ((image l F c).map
          ((reductionBalancing l E F i X SE SF e he hepos).hom.app M)) ≫
      (T l F L j Y).map
        ((reindexImage l F c e hepos).inv.app
          ((reduction l F X SF).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
      (T l F L j Y).map
        ((subsequence l F Y e).map
          ((supportModel l F c SF).inv.app
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
      (compositionSelection l F L j Y e).hom.app
        ((support l F c SF).obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
      (subsequence l L Y e).map
        ((arrow l F L j c SF SL h hh hhpos).app
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
      (compositionRetained l L Y e h hepos hhpos).hom.app
        ((support l L c SL).obj
          ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
      (subsequence l L Y (h * e)).map
        ((support l L c SL).map
          ((compositionCompleted l E F i L j X).hom.app M)) := by
  have hb := reductionBalancing_composition l E F i L j X SE SF SL
    e h he hepos hh hhpos M
  have hs := comparison_selection l F L j c e hepos
    ((reduction l F X SF).obj
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
  have hr := reindexImage_composition l L c e h hepos hhpos
    ((reduction l L X SL).obj
      ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)))
  have hm := (supportModel l L c SL).inv.naturality
    ((compositionCompleted l E F i L j X).hom.app M)
  have hp := support_pasting
    (image l F c) (image l L c) (T l F L j X) (T l F L j Y)
    (subsequence l F X e) (subsequence l F Y e)
    (subsequence l L X e) (subsequence l L X h) (subsequence l L X (h * e))
    (subsequence l L Y e) (subsequence l L Y h) (subsequence l L Y (h * e))
    (comparison l F L j c)
    (compositionSelection l F L j X e) (compositionSelection l F L j Y e)
    (reindexImage l F c e hepos).symm
    (reindexImage l L c e hepos).symm (reindexImage l L c h hhpos).symm
    (reindexImage l L c (h * e) (one_le_mul hhpos hepos)).symm
    (compositionRetained l L X e h hepos hhpos)
    (compositionRetained l L Y e h hepos hhpos)
    ((reductionBalancing l E F i X SE SF e he hepos).hom.app M)
    ((reductionBalancing l F L j X SF SL h hh hhpos).hom.app
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
    ((compositionTower l E F i L j X).hom.app ((reduction l E X SE).obj M) ≫
      (reductionBalancing l E L (j.comp i) X SE SL (h * e)
        (compositionRamification l E F i L j e h he hh)
        (one_le_mul hhpos hepos)).hom.app M)
    ((reduction l L X SL).map ((compositionCompleted l E F i L j X).hom.app M))
    ((support l L c SL).map ((compositionCompleted l E F i L j X).hom.app M))
    ((supportModel l F c SF).app
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
    ((supportModel l L c SL).app
      ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)))
    ((supportModel l L c SL).app
      ((pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) X)).obj M))
    hb hs hr hm
  simpa only [Functor.comp_obj, Functor.map_comp, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    arrow, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] using hp

end Geometry
end WeilConjectures.PurStrictScalar
