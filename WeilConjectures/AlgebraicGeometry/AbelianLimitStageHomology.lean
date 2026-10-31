/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianLimitStages
import WeilConjectures.CategoryTheory.ExactDerivedCohomologyCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso

/-! # Cohomology of derived stage transitions

Source: Stacks Tags 0EYM and 0GIU, the canonical exchange maps.
(blueprint: lem-sf-abelian-limit-stage-homology).
-/

@[expose] public section

universe u' u

set_option autoImplicit false

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private lemma plusHomology_hom_app (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory.Plus C) (n : ℤ) :
    (F.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K =
      (F.mapDerivedCategoryHomologyFunctorIso n).hom.app (DerivedCategory.Plus.ι.obj K) := by
  simp only [Functor.comp_obj, mapDerivedCategoryPlusHomologyFunctorIso,
    mapDerivedCategoryPlusCompatibility, Iso.refl_symm, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Iso.refl_hom, NatTrans.comp_app, ObjectProperty.ι_obj, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    NatTrans.id_app, Category.comp_id, Category.id_comp]
  erw [Functor.map_id, Category.comp_id, Category.id_comp]

/-- Naturality in an isomorphism of exact functors, restricted to `D⁺`.
Source: the canonical cohomology identifications in Stacks Tags 0EYM and 0GIU.
(blueprint: lem-sf-abelian-limit-stage-homology). -/
@[reassoc]
private lemma mapDerivedCategoryPlusHomologyFunctorIso_naturality
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory.Plus C) (n : ℤ) :
    e.hom.app ((DerivedCategory.Plus.homologyFunctor C n).obj K) ≫
        (G.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K =
      (F.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.Plus.homologyFunctor D n).map
          ((mapDerivedCategoryPlusNatIso e).hom.app K) := by
  simp only [plusHomology_hom_app]
  change e.hom.app ((DerivedCategory.homologyFunctor C n).obj
      (DerivedCategory.Plus.ι.obj K)) ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.app (DerivedCategory.Plus.ι.obj K) =
    (F.mapDerivedCategoryHomologyFunctorIso n).hom.app (DerivedCategory.Plus.ι.obj K) ≫
      (DerivedCategory.homologyFunctor D n).map
        (DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusNatIso e).hom.app K))
  rw [ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  exact mapDerivedCategoryHomologyFunctorIso_hom_app_naturality e n
    (DerivedCategory.Plus.ι.obj K)

/-- Homology commutes coherently with composition of exact functors on `D⁺`.

Proof: restrict the existing normalized unbounded exact-functor coherence to
bounded-below objects. The inclusion identifies each homology comparison and sends
the bounded-below compositor to the unbounded compositor.
Source: Stacks Tags 0EYM and 0GIU, canonical cohomology comparisons.
(blueprint: lem-sf-abelian-limit-stage-homology). -/
private lemma mapDerivedCategoryPlusHomologyFunctorIso_comp
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) (n : ℤ) :
    ((F ⋙ G).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.Plus.homologyFunctor E n).map
          ((mapDerivedCategoryPlusCompIso F G).hom.app K) =
      G.map ((F.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K) ≫
        (G.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
          (F.mapDerivedCategoryPlus.obj K) := by
  simp only [plusHomology_hom_app]
  change ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom.app
      (DerivedCategory.Plus.ι.obj K) ≫
      (DerivedCategory.homologyFunctor E n).map
        (DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIso F G).hom.app K)) = _
  rw [ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  exact (exactDerivedCohomologyCoherence F G n).1 (DerivedCategory.Plus.ι.obj K)

end CategoryTheory.Functor


namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

omit [HasSmallSiteSheafify A] in
/-- Exact-pullback cohomology comparisons respect the inverse-image composition
isomorphism. This follows by combining naturality in the ordinary composition
isomorphism with the comparison for composition of exact functors.
Source: Stacks Tags 0EYM and 0GIU, composition identifications.
(blueprint: lem-sf-abelian-limit-stage-homology). -/
lemma upperStarCompDerivedPlus_homology {R T V : Scheme.{u}}
    (f : T ⟶ V) (g : V ⟶ R) (fg : T ⟶ R) (hfg : fg = f ≫ g)
    (K : DerivedCategory.Plus (Sheaf R.smallEtaleTopology A)) (p : ℤ) :
    ((upperStar A fg).mapDerivedCategoryPlusHomologyFunctorIso p).hom.app K ≫
        (DerivedCategory.Plus.homologyFunctor _ p).map
          ((upperStarCompDerivedPlus A f g fg hfg).hom.app K) =
      (upperStarComp A f g fg hfg).hom.app
          ((DerivedCategory.Plus.homologyFunctor _ p).obj K) ≫
        (upperStar A f).map
          (((upperStar A g).mapDerivedCategoryPlusHomologyFunctorIso p).hom.app K) ≫
        ((upperStar A f).mapDerivedCategoryPlusHomologyFunctorIso p).hom.app
          ((upperStar A g).mapDerivedCategoryPlus.obj K) := by
  simp only [upperStarCompDerivedPlus, Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp, ← Category.assoc]
  rw [← Functor.mapDerivedCategoryPlusHomologyFunctorIso_naturality]
  rw [Category.assoc, Functor.mapDerivedCategoryPlusHomologyFunctorIso_comp]
  simp only [Category.assoc]

omit [HasSmallSiteSheafify A] in
/-- The composition comparison on derived inverse images agrees with the
single-sheaf comparisons. This is detected on degree-zero homology: the exact
cohomology comparison is compatible with composition, and its value on single
complexes is the ordinary comparison.
Source: Stacks Tags 0EYM and 0GIU, single-sheaf identifications.
(blueprint: lem-sf-abelian-limit-stage-homology). -/
lemma upperStarCompDerivedPlus_single {R T V : Scheme.{u}}
    (f : T ⟶ V) (g : V ⟶ R) (fg : T ⟶ R) (hfg : fg = f ≫ g)
    (F : Sheaf R.smallEtaleTopology A) :
    (upperStarCompDerivedPlus A f g fg hfg).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
        (upperStar A f).mapDerivedCategoryPlus.map
          (((upperStar A g).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
        ((upperStar A f).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((upperStar A g).obj F) =
      ((upperStar A fg).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp A f g fg hfg).hom.app F) := by
  have : ((upperStar A fg).mapDerivedCategoryPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).IsGE 0 :=
    Functor.IsTExact.isGE_obj DerivedCategory.Plus.TStructure.t
      DerivedCategory.Plus.TStructure.t (upperStar A fg).mapDerivedCategoryPlus _ 0
  have : ((upperStar A fg).mapDerivedCategoryPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).IsLE 0 :=
    Functor.IsTExact.isLE_obj DerivedCategory.Plus.TStructure.t
      DerivedCategory.Plus.TStructure.t (upperStar A fg).mapDerivedCategoryPlus _ 0
  apply DerivedCategory.Plus.singleFunctor_hom_ext_of_isGE_of_isLE 0
  apply (cancel_epi
    (((upperStar A fg).mapDerivedCategoryPlusHomologyFunctorIso 0).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).mp
  apply (cancel_mono
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := _) 0).hom.app
      ((upperStar A f).obj ((upperStar A g).obj F)))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% upperStarCompDerivedPlus_homology A f g fg hfg
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0]
  rw [← reassoc_of% (((upperStar A f).mapDerivedCategoryPlusHomologyFunctorIso 0).hom.naturality
    (((upperStar A g).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))]
  rw [(upperStar A f).mapDerivedCategoryPlusHomologyFunctorIso_hom_app_singleFunctor]
  rw [← (upperStar A f).map_comp, ← (upperStar A f).map_comp]
  rw [(upperStar A g).mapDerivedCategoryPlusHomologyFunctorIso_hom_app_singleFunctor]
  have hs := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := _) 0).hom.naturality
    ((upperStarComp A f g fg hfg).hom.app F)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hs
  rw [hs]
  rw [reassoc_of% (upperStar A fg).mapDerivedCategoryPlusHomologyFunctorIso_hom_app_singleFunctor]
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] using
    ((upperStarComp A f g fg hfg).hom.naturality
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := _) 0).hom.app F)).symm

namespace AbelianLimitStage

variable {B W : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- Cohomology of a derived transition, expressed using ordinary inverse image.

Proof: expand the stage transition. Naturality moves the cohomology comparison
past the exchange map and coefficient comparison; compatibility with inverse-image
composition identifies the remaining two comparisons. Thus the derived transition
has precisely the ordinary pullback of the cohomological exchange as its formula.
Source: Stacks Tags 0EYM and 0GIU, construction of the canonical maps.
(blueprint: lem-sf-abelian-limit-stage-homology). -/
lemma transition_homology {α β : LimitStage B W} (φ : LimitStage.Hom α β)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (p : ℤ) :
    ((upperStar A β.π).mapDerivedCategoryPlusHomologyFunctorIso p).hom.app
        ((rightDerivedLowerStarPlus A β.g).obj
          ((upperStar A β.w).mapDerivedCategoryPlus.obj K)) ≫
        (DerivedCategory.Plus.homologyFunctor _ p).map ((transition A φ).app K) =
      (upperStarComp A α.π φ.s β.π φ.wπ.symm).hom.app
          ((DerivedCategory.Plus.homologyFunctor _ p).obj
            ((rightDerivedLowerStarPlus A β.g).obj
              ((upperStar A β.w).mapDerivedCategoryPlus.obj K))) ≫
        (upperStar A α.π).map
          (((upperStar A φ.s).mapDerivedCategoryPlusHomologyFunctorIso p).hom.app
              ((rightDerivedLowerStarPlus A β.g).obj
                ((upperStar A β.w).mapDerivedCategoryPlus.obj K)) ≫
            (DerivedCategory.Plus.homologyFunctor _ p).map
              ((derivedBaseChangeMapPlus A ⟨φ.wg⟩).app
                  ((upperStar A β.w).mapDerivedCategoryPlus.obj K) ≫
                (rightDerivedLowerStarPlus A α.g).map
                  ((upperStarCompDerivedPlus A φ.t β.w α.w φ.ww.symm).inv.app K))) ≫
        ((upperStar A α.π).mapDerivedCategoryPlusHomologyFunctorIso p).hom.app
          ((rightDerivedLowerStarPlus A α.g).obj
            ((upperStar A α.w).mapDerivedCategoryPlus.obj K)) := by
  dsimp only [rightDerivedLowerStarPlus]
  rw [transition_app, Functor.map_comp, ← Category.assoc,
    upperStarCompDerivedPlus_homology]
  simp only [Category.assoc]
  rw [(upperStar A α.π).map_comp, Category.assoc]
  congr 1
  congr 1
  exact (((upperStar A α.π).mapDerivedCategoryPlusHomologyFunctorIso p).hom.naturality
    ((derivedBaseChangeMapPlus A ⟨φ.wg⟩).app
        ((upperStar A β.w).mapDerivedCategoryPlus.obj K) ≫
      (lowerStar A α.g).rightDerivedFunctorPlus.map
        ((upperStarCompDerivedPlus A φ.t β.w α.w φ.ww.symm).inv.app K))).symm

end AbelianLimitStage
end AlgebraicGeometry.Etale
