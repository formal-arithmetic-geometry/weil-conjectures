/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HorizontalDualityMateComparisons
public import Mathlib.CategoryTheory.Comma.Arrow

import WeilConjectures.AlgebraicGeometry.HorizontalRectangleInverseMateFixedTransport

/-! # Equality of horizontal duality mates with fixed endpoint comparisons

## References

* Stacks Project, Tags 0ATR and 0ATM
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The unit/counit equality for the two horizontal duality mates, with the source
and target comparison maps explicitly constructed, rather than existentially chosen.
(Stacks, Tags 0ATR and 0ATM) -/
theorem horizontal_duality_mate_commutativity
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
          (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y)
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y')
    (c : schemeDerivedQCohCategory Z ⥤
      schemeDerivedQCohCategory (pullback f (h ≫ g)))
    (adjc : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι ⋙
        schemeDerivedDirectImage (pullback.snd f (h ≫ g))) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _ _ _
          (pullback.snd f (h ≫ g)) _ _).fst E.obj E.property) ⊣ c)
    (hβh : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (d : schemeDerivedQCohCategory Z ⥤
      schemeDerivedQCohCategory (pullback (pullback.snd f g) h))
    (adjd : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι ⋙
        schemeDerivedDirectImage (pullback.snd (pullback.snd f g) h)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h))
          _ _ _ _ (pullback.snd (pullback.snd f g) h) _ _).fst E.obj E.property) ⊣ d)
    (hβ₂ : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h
        (pullback.fst (pullback.snd f g) h) pullback.condition E.obj)) :
    let O := Arrow.mk
      ((derivedPullback (pullback.fst (pullback.snd f g) h)).map
        ((schemeDerivedQCohProperty (pullback f g)).ι.map
            (@dualityEquationBaseChangeMap _ X Y Y'
              (QuasiCompact.compactSpace_of_compactSpace f)
              (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
              f g a a' adjf adjf' hβ K)) ≫
        ((schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
            (@dualityEquationBaseChangeMap _ (pullback f g) Y' Z
              (QuasiCompact.compactSpace_of_compactSpace (pullback.snd f g))
              (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
              (pullback.snd f g) h a' d adjf' adjd hβ₂
              (((schemeDerivedQCohProperty Y').lift
                ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
                (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
                  E.obj E.property)).obj K))))
    let G := Arrow.mk ((derivedPullback (pullbackLeftPullbackSndIso f g h).hom).map
        ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι.map
            (@dualityEquationBaseChangeMap _ X Y Z
              (QuasiCompact.compactSpace_of_compactSpace f)
              (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
              f (h ≫ g) a c adjf adjc hβh K)))
    O.hom ≫ (horizontalMateTargetIso f g h c d adjc adjd K).hom =
      (horizontalMateSourceIso f g h (a.obj K).obj).hom ≫ G.hom := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  intro O G
  let α := qcInverseBaseChange f g hβ
  let δ := @qcInverseBaseChange _ (pullback f g) Y' Z _
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
    (pullback.snd f g) _ _ h hβ₂
  have paste := congrArg (fun σ ↦ σ.app K) (mateEquiv_vcomp adjf adjf' adjd α δ)
  simp only [TwoSquare.vComp_app] at paste
  have hS := dualityEquationBaseChangeMap_eq_inverseSquareMate
    f g a a' adjf adjf' hβ K
  have hI := @dualityEquationBaseChangeMap_eq_inverseSquareMate _ (pullback f g) Y' Z _
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
    (pullback.snd f g) _ _ h a' d adjf' adjd hβ₂ ((qcPullback g).obj K)
  rw [← hS, ← hI] at paste
  have hp := (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.congr_map paste
  simp only [Functor.map_comp] at hp
  change _ = O.hom at hp
  have ht := horizontal_rectangle_inverse_mate_fixed_transport
    g f a adjf hβ K h c adjc hβh d adjd hβ₂
  change G.hom ≫ (horizontalMateTargetIso f g h c d adjc adjd K).inv =
    (horizontalMateSourceIso f g h (a.obj K).obj).inv ≫ _ at ht
  rw [hp] at ht
  apply (cancel_mono (horizontalMateTargetIso f g h c d adjc adjd K).inv).mp
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using
      (congrArg (fun φ ↦ (horizontalMateSourceIso f g h (a.obj K).obj).hom ≫ φ) ht).symm

end AlgebraicGeometry
