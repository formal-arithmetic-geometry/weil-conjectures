/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.DerivedInverseImageComposition
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Filtered.Basic
import all WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyComp
import WeilConjectures.AlgebraicGeometry.EtaleSystemConeFunctor
import WeilConjectures.AlgebraicGeometry.RelativeHigherDirectImageContinuity

/-! # Relative continuity for higher direct images of abelian étale sheaves

Source: Stacks Project, Tag 0EYM, lemma-relative-colimit-general, including the
canonical maps in its opening proof paragraphs
(blueprint: lem-sf-relative-direct-image-sheaf-limit).

The helper definitions construct the specified maps from the general-square derived
exchange. The theorem includes the diagram and cocone laws through functors and cocones
with prescribed objects and maps. The final colimit property says that the canonical
comparison is an isomorphism.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] upperStar

/-- The higher direct image `H^p(Rf_*(F[0]))` of an abelian étale sheaf.
Source: Stacks Tag 0EYM, statement
(blueprint: lem-sf-relative-direct-image-sheaf-limit). -/
noncomputable def relativeSheafHigherImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
    ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- Cohomology of the general-square exchange followed by the coefficient map.
The exact-pullback comparison first moves inverse image past cohomology. The single-functor
comparison identifies the derived pullback of `F[0]` with the pullback sheaf in degree zero.
Source: Stacks Tag 0EYM, construction of `ψ` in the opening proof paragraphs
(blueprint: lem-sf-relative-direct-image-sheaf-limit). -/
noncomputable def relativeSheafHigherImageMap
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {b : Y' ⟶ Y} (sq : CommSq a f' f b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F') (p : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} b).obj (relativeSheafHigherImage f F p) ⟶
      relativeSheafHigherImage f' F' p :=
  ((upperStar AddCommGrpCat.{u + 1} b).mapDerivedCategoryPlusHomologyFunctorIso
    (p : ℤ)).hom.app
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
    (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
        (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
          (((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor
            0).hom.app F ≫ (DerivedCategory.Plus.singleFunctor _ 0).map φ))

/-- Transition of the coefficient sheaves pulled back to the limit source, using the
canonical inverse-image composition comparison and the given coefficient transition.
Source: Stacks Tag 0EYM, `F = colim a_i⁻¹ F_i`
(blueprint: lem-sf-relative-direct-image-sheaf-limit). -/
noncomputable def relativeSheafCoefficientTransition
    {I : Type u} [Preorder I] (DU : Iᵒᵖ ⥤ Scheme.{u}) (cU : Cone DU)
    (F : ∀ i : I, Sheaf (DU.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (h : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (DU.map h.op)).obj (F i) ⟶ F j)
    {i j : I} (h : i ⟶ j) :
    (upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i))).obj (F i) ⟶
      (upperStar AddCommGrpCat.{u + 1} (cU.π.app (op j))).obj (F j) :=
  (upperStarComp AddCommGrpCat.{u + 1} (cU.π.app (op j)) (DU.map h.op)
    (cU.π.app (op i)) (cU.w h.op).symm).hom.app (F i) ≫
    (upperStar AddCommGrpCat.{u + 1} (cU.π.app (op j))).map (φ h)

/-- Transition of pulled-back higher direct images: inverse-image composition followed
by the pullback of cohomology of the transition-square exchange and `Rg_j,*(φ_ji)`.
Source: Stacks Tag 0EYM, opening proof paragraphs
(blueprint: lem-sf-relative-direct-image-sheaf-limit). -/
noncomputable def relativeSheafImageTransition
    {I : Type u} [Preorder I] (DU DV : Iᵒᵖ ⥤ Scheme.{u}) (η : DU ⟶ DV)
    (cV : Cone DV)
    (F : ∀ i : I, Sheaf (DU.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (h : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (DU.map h.op)).obj (F i) ⟶ F j)
    (p : ℕ) {i j : I} (h : i ⟶ j) :
    (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj
      (relativeSheafHigherImage (η.app (op i)) (F i) p) ⟶
    (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op j))).obj
      (relativeSheafHigherImage (η.app (op j)) (F j) p) :=
  (upperStarComp AddCommGrpCat.{u + 1} (cV.π.app (op j)) (DV.map h.op)
    (cV.π.app (op i)) (cV.w h.op).symm).hom.app
      (relativeSheafHigherImage (η.app (op i)) (F i) p) ≫
    (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op j))).map
      (relativeSheafHigherImageMap ⟨η.naturality h.op⟩ (F i) (F j) (φ h) p)

/-- The canonical limit-square cocone leg, with coefficient morphism `λ_i`.
Source: Stacks Tag 0EYM, opening proof paragraphs
(blueprint: lem-sf-relative-direct-image-sheaf-limit). -/
noncomputable def relativeSheafImageLeg
    {I : Type u} [Preorder I] (DU DV : Iᵒᵖ ⥤ Scheme.{u}) (η : DU ⟶ DV)
    (cU : Cone DU) (cV : Cone DV) (g : cU.pt ⟶ cV.pt)
    (hg : ∀ i : Iᵒᵖ, cU.π.app i ≫ η.app i = g ≫ cV.π.app i)
    (F : ∀ i : I, Sheaf (DU.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (Flim : Sheaf cU.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (lam : ∀ i : I, (upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i))).obj (F i) ⟶ Flim)
    (p : ℕ) (i : I) :
    (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj
      (relativeSheafHigherImage (η.app (op i)) (F i) p) ⟶
      relativeSheafHigherImage g Flim p :=
  relativeSheafHigherImageMap ⟨hg (op i)⟩ (F i) Flim (lam i) p

private theorem plus_homology_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (n : ℤ) (K : DerivedCategory.Plus A) :
    (P.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K =
      (P.mapDerivedCategoryHomologyFunctorIso n).hom.app (DerivedCategory.Plus.ι.obj K) := by
  simp only [Functor.mapDerivedCategoryPlusHomologyFunctorIso,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Iso.refl_inv, Category.id_comp]
  dsimp only [DerivedCategory.Plus.homologyFunctor, Functor.comp_obj]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  exact Category.comp_id _

private theorem plus_homology_natIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (P Q : A ⥤ B) [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (e : P ≅ Q) (n : ℤ) (K : DerivedCategory.Plus A) :
    e.hom.app ((DerivedCategory.Plus.homologyFunctor A n).obj K) ≫
        (Q.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K =
      (P.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          ((Functor.mapDerivedCategoryPlusNatIso e).hom.app K) := by
  rw [plus_homology_eq, plus_homology_eq]
  change _ = _ ≫ (DerivedCategory.homologyFunctor B n).map
    (DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusNatIso e).hom.app K))
  rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  exact Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality e n _

private theorem plus_homology_comp
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    (P : A ⥤ B) (Q : B ⥤ E) [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (n : ℤ) (K : DerivedCategory.Plus A) :
    ((P ⋙ Q).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.Plus.homologyFunctor E n).map
          ((Functor.mapDerivedCategoryPlusCompIso P Q).hom.app K) =
      Q.map ((P.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K) ≫
        (Q.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app (P.mapDerivedCategoryPlus.obj K)
        := by
  rw [plus_homology_eq, plus_homology_eq, plus_homology_eq]
  change _ ≫ (DerivedCategory.homologyFunctor E n).map
    (DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso P Q).hom.app K)) = _
  rw [Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  exact Functor.mapDerivedCategoryHomologyFunctorIso_comp P Q n _

private theorem single_pullback_comp
    {X Y Z : Scheme.{u}} (a : Y ⟶ X) (b : Z ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b a).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (upperStar AddCommGrpCat.{u + 1} b).mapDerivedCategoryPlus.map
        (((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      ((upperStar AddCommGrpCat.{u + 1} b).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        ((upperStar AddCommGrpCat.{u + 1} a).obj F) =
    ((upperStar AddCommGrpCat.{u + 1} (b ≫ a)).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{u + 1} b a).hom.app F) := by
  rw [upperStarCompDerivedPlus, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.plus_single_comp]
  exact Functor.plus_single_natIso _ 0 F

private theorem single_coefficient_comp
    {X Y Z : Scheme.{u}} (a : Y ⟶ X) (b : Z ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (H : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ G)
    (ψ : (upperStar AddCommGrpCat.{u + 1} b).obj G ⟶ H) :
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b a).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      ((upperStar AddCommGrpCat.{u + 1} (b ≫ a)).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{u + 1} b a).hom.app F ≫
          (upperStar AddCommGrpCat.{u + 1} b).map φ ≫ ψ) =
    (upperStar AddCommGrpCat.{u + 1} b).mapDerivedCategoryPlus.map
      (((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ) ≫
      ((upperStar AddCommGrpCat.{u + 1} b).mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map ψ := by
  apply (cancel_epi ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b a).hom.app
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).1
  simp only [Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc]
  have hn :=
    ((upperStar AddCommGrpCat.{u + 1} b).mapDerivedCategoryPlusSingleFunctor 0).hom.naturality φ
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, reassoc_of% (single_pullback_comp a b F)]

private theorem derived_coefficient_comp
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {a : X' ⟶ X} {a' : X'' ⟶ X'} {b : Y' ⟶ Y} {b' : Y'' ⟶ Y'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    (sq₁ : CommSq a f' f b) (sq₂ : CommSq a' f'' f' b')
    (sq : CommSq (a' ≫ a) f'' f (b' ≫ b))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F'' : Sheaf X''.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F')
    (ψ : (upperStar AddCommGrpCat.{u + 1} a').obj F' ⟶ F'') :
    relativeHigherDirectImageDerivedMap sq F F''
        ((upperStarComp AddCommGrpCat.{u + 1} a' a).hom.app F ≫
          (upperStar AddCommGrpCat.{u + 1} a').map φ ≫ ψ) =
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b' b).hom.app
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (upperStar AddCommGrpCat.{u + 1} b').mapDerivedCategoryPlus.map
        (relativeHigherDirectImageDerivedMap sq₁ F F' φ) ≫
      relativeHigherDirectImageDerivedMap sq₂ F' F'' ψ := by
  dsimp only [relativeHigherDirectImageDerivedMap, rightDerivedLowerStarPlus]
  rw [derivedBaseChangeMapPlus_paste_horiz AddCommGrpCat.{u + 1} sq₁ sq₂ sq]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc]
  rw [← Functor.map_comp, single_coefficient_comp]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₂).naturality
    (((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map φ)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hn
  rw [reassoc_of% hn]

private theorem pullback_homology_comp
    {X Y Z : Scheme.{u}} (a : Y ⟶ X) (b : Z ⟶ Y)
    (n : ℤ) (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (upperStarComp AddCommGrpCat.{u + 1} b a).hom.app
        ((DerivedCategory.Plus.homologyFunctor _ n).obj K) ≫
      (upperStar AddCommGrpCat.{u + 1} b).map
        (((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusHomologyFunctorIso
          n).hom.app K) ≫
      ((upperStar AddCommGrpCat.{u + 1} b).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
        ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.obj K) =
    ((upperStar AddCommGrpCat.{u + 1} (b ≫ a)).mapDerivedCategoryPlusHomologyFunctorIso
      n).hom.app K ≫
      (DerivedCategory.Plus.homologyFunctor _ n).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b a).hom.app K) := by
  rw [upperStarCompDerivedPlus, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp]
  rw [← reassoc_of% (plus_homology_natIso _ _
    (upperStarComp AddCommGrpCat.{u + 1} b a) n K)]
  rw [plus_homology_comp]

set_option maxHeartbeats 2000000 in
-- Normalizing the two homology/mate composites requires a larger elaboration budget.
private theorem higher_image_map_comp
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {a : X' ⟶ X} {a' : X'' ⟶ X'} {b : Y' ⟶ Y} {b' : Y'' ⟶ Y'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    (sq₁ : CommSq a f' f b) (sq₂ : CommSq a' f'' f' b')
    (sq : CommSq (a' ≫ a) f'' f (b' ≫ b))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F'' : Sheaf X''.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F')
    (ψ : (upperStar AddCommGrpCat.{u + 1} a').obj F' ⟶ F'') (p : ℕ) :
    relativeSheafHigherImageMap sq F F''
        ((upperStarComp AddCommGrpCat.{u + 1} a' a).hom.app F ≫
          (upperStar AddCommGrpCat.{u + 1} a').map φ ≫ ψ) p =
      (upperStarComp AddCommGrpCat.{u + 1} b' b).hom.app
        (relativeSheafHigherImage f F p) ≫
      (upperStar AddCommGrpCat.{u + 1} b').map
        (relativeSheafHigherImageMap sq₁ F F' φ p) ≫
      relativeSheafHigherImageMap sq₂ F' F'' ψ p := by
  dsimp only [relativeSheafHigherImageMap, relativeSheafHigherImage,
    rightDerivedLowerStarPlus, Functor.comp_obj]
  change _ ≫ (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
    (relativeHigherDirectImageDerivedMap sq F F'' _) = _
  rw [derived_coefficient_comp sq₁ sq₂ sq F F' F'' φ ψ]
  dsimp only [rightDerivedLowerStarPlus, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  have hc := pullback_homology_comp b b' (p : ℤ)
    ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  dsimp only [rightDerivedLowerStarPlus, Functor.comp_obj] at hc
  erw [← reassoc_of% hc]
  have hn := ((upperStar AddCommGrpCat.{u + 1} b').mapDerivedCategoryPlusHomologyFunctorIso
    (p : ℤ)).hom.naturality (relativeHigherDirectImageDerivedMap sq₁ F F' φ)
  dsimp only [relativeHigherDirectImageDerivedMap, rightDerivedLowerStarPlus,
    Functor.comp_obj, Functor.comp_map] at hn ⊢
  simp only [Functor.map_comp, Category.assoc] at hn ⊢
  erw [← reassoc_of% hn]

private theorem higher_image_map_comp_of_eq
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {a : X' ⟶ X} {a' : X'' ⟶ X'} {b : Y' ⟶ Y} {b' : Y'' ⟶ Y'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    (sq₁ : CommSq a f' f b) (sq₂ : CommSq a' f'' f' b')
    (ad : X'' ⟶ X) (bd : Y'' ⟶ Y)
    (ha : ad = a' ≫ a) (hb : bd = b' ≫ b) (sq : CommSq ad f'' f bd)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F'' : Sheaf X''.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F')
    (ψ : (upperStar AddCommGrpCat.{u + 1} a').obj F' ⟶ F'') (p : ℕ) :
    relativeSheafHigherImageMap sq F F''
        ((upperStarComp AddCommGrpCat.{u + 1} a' a ad ha).hom.app F ≫
          (upperStar AddCommGrpCat.{u + 1} a').map φ ≫ ψ) p =
      (upperStarComp AddCommGrpCat.{u + 1} b' b bd hb).hom.app
        (relativeSheafHigherImage f F p) ≫
      (upperStar AddCommGrpCat.{u + 1} b').map
        (relativeSheafHigherImageMap sq₁ F F' φ p) ≫
      relativeSheafHigherImageMap sq₂ F' F'' ψ p := by
  subst ad bd
  exact higher_image_map_comp sq₁ sq₂ sq F F' F'' φ ψ p

private theorem cone_transition_comp
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (h : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map h.op)).obj (F i) ⟶ F j)
    (hcomp : ∀ (i j k : I) (h : i ⟶ j) (h' : j ⟶ k), φ (h ≫ h') =
      (upperStarComp AddCommGrpCat.{u + 1} (D.map h'.op) (D.map h.op)
        (D.map (h ≫ h').op) (D.map_comp h'.op h.op)).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (D.map h'.op)).map (φ h) ≫ φ h')
    {i j k : I} (h : i ⟶ j) (h' : j ⟶ k) :
    relativeSheafCoefficientTransition D c F φ (i := i) (j := k) (h ≫ h') =
      relativeSheafCoefficientTransition D c F φ (i := i) (j := j) h ≫
      relativeSheafCoefficientTransition D c F φ (i := j) (j := k) h' := by
  dsimp only [relativeSheafCoefficientTransition]
  rw [hcomp]
  simp only [Functor.map_comp]
  have hc := NatTrans.congr_app
    (upperStarComp_assoc' AddCommGrpCat.{u + 1}
      (c.π.app (op k)) (D.map h'.op) (D.map h.op)
      (c.π.app (op j)) (D.map (h ≫ h').op) (c.π.app (op i))
      (c.w h'.op).symm (D.map_comp h'.op h.op) (c.w h.op).symm) (F i)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, op_comp] at hc
  simp only [op_comp]
  rw [← Category.assoc, hc]
  simp only [Category.assoc]
  have hn := (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op k))
    (D.map h'.op) (c.π.app (op j)) (c.w h'.op).symm).hom.naturality_assoc
      (φ h) ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op k))).map (φ h'))
  simp only [Functor.comp_map] at hn
  rw [← hn]

private theorem higher_image_map_identity_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (ha : a = 𝟙 X) (hb : b = 𝟙 Y) (sq : CommSq a f f b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F) [IsIso φ] (p : ℕ) :
    IsIso (relativeSheafHigherImageMap sq F F φ p) := by
  have hex : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
    subst a b
    rw [derivedBaseChangeMapPlus_id]
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app]
    erw [Category.id_comp, Category.id_comp]
    infer_instance
  dsimp only [relativeSheafHigherImageMap, rightDerivedLowerStarPlus]
  infer_instance

private theorem image_map_eq_exchange
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {b : Y' ⟶ Y} (sq : CommSq a f' f b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ F') (p : ℕ) :
    relativeSheafHigherImageMap sq F F' φ p =
      relativeHigherDirectImageExchange sq F F' φ p := rfl

set_option maxHeartbeats 2000000 in
-- The kernel checks a large comparison across the thin-skeleton equivalence.
private theorem continuity_preorder
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DU DV : Iᵒᵖ ⥤ Scheme.{u}) (η : DU ⟶ DV)
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (DU.map h)]
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (DV.map h)]
    [∀ i : Iᵒᵖ, QuasiCompact (η.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (η.app i)]
    (cU : Cone DU) (hcU : IsLimit cU) (cV : Cone DV) (hcV : IsLimit cV)
    (g : cU.pt ⟶ cV.pt)
    (hg : ∀ i : Iᵒᵖ, cU.π.app i ≫ η.app i = g ≫ cV.π.app i)
    (F : ∀ i : I, Sheaf (DU.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (h : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (DU.map h.op)).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (DU.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (DU.obj (op i))).hom.app (F i))
    (hφcomp : ∀ (i j k : I) (h : i ⟶ j) (h' : j ⟶ k), φ (h ≫ h') =
      (upperStarComp AddCommGrpCat.{u + 1} (DU.map h'.op) (DU.map h.op)
        (DU.map (h ≫ h').op) (DU.map_comp h'.op h.op)).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (DU.map h'.op)).map (φ h) ≫ φ h')
    (C : I ⥤ Sheaf cU.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : ∀ i : I, C.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i))).obj (F i))
    (hC : ∀ (i j : I) (h : i ⟶ j), C.map h =
      (e i).hom ≫ relativeSheafCoefficientTransition DU cU F φ h ≫ (e j).inv)
    (cF : Cocone C) (hcF : IsColimit cF) (p : ℕ)
    (D : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eD : ∀ i : I, D.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj
        (relativeSheafHigherImage (η.app (op i)) (F i) p))
    (hD : ∀ (i j : I) (h : i ⟶ j), D.map h =
      (eD i).hom ≫ relativeSheafImageTransition DU DV η cV F φ p h ≫ (eD j).inv)
    (c : Cocone D) (hc : IsColimit c)
    (legs : D ⟶ (Functor.const I).obj (relativeSheafHigherImage g cF.pt p))
    (hlegs : ∀ i : I, legs.app i = (eD i).hom ≫
      relativeSheafImageLeg DU DV η cU cV g hg F cF.pt
        (fun j ↦ (e j).inv ≫ cF.ι.app j) p i) :
    IsIso (hc.desc { pt := relativeSheafHigherImage g cF.pt p, ι := legs }) := by
  classical
  let E := ThinSkeleton.equivalence I
  let Q := E.functor
  have : IsFiltered (ThinSkeleton I) := IsFiltered.of_equivalence E.symm
  have : IsDirectedOrder (ThinSkeleton I) := IsFiltered.isDirectedOrder _
  have : Nonempty (ThinSkeleton I) := IsFiltered.nonempty
  let DU' := Q.op ⋙ DU
  let DV' := Q.op ⋙ DV
  have : ∀ {i j : (ThinSkeleton I)ᵒᵖ} (a : i ⟶ j), IsAffineHom (DU'.map a) :=
    fun a ↦ inferInstanceAs (IsAffineHom (DU.map (Q.op.map a)))
  have : ∀ {i j : (ThinSkeleton I)ᵒᵖ} (a : i ⟶ j), IsAffineHom (DV'.map a) :=
    fun a ↦ inferInstanceAs (IsAffineHom (DV.map (Q.op.map a)))
  have : ∀ i : (ThinSkeleton I)ᵒᵖ, QuasiCompact ((Functor.whiskerLeft Q.op η).app i) :=
    fun i ↦ inferInstanceAs (QuasiCompact (η.app (Q.op.obj i)))
  have : ∀ i : (ThinSkeleton I)ᵒᵖ, QuasiSeparated ((Functor.whiskerLeft Q.op η).app i) :=
    fun i ↦ inferInstanceAs (QuasiSeparated (η.app (Q.op.obj i)))
  let η' := Functor.whiskerLeft Q.op η
  let cU' := cU.whisker Q.op
  let cV' := cV.whisker Q.op
  let F' := fun i : ThinSkeleton I ↦ F (Q.obj i)
  let φ' := fun {i j : ThinSkeleton I} (h : i ⟶ j) ↦ φ (Q.map h)
  have hid' : ∀ i : ThinSkeleton I, φ' (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (DU'.map_id (op i)))).hom.app
        (F' i) ≫ (upperStarId AddCommGrpCat.{u + 1} (DU'.obj (op i))).hom.app (F' i) := by
    intro i
    exact hφid (Q.obj i)
  have hcomp' : ∀ (i j k : ThinSkeleton I) (h : i ⟶ j) (h' : j ⟶ k),
      φ' (h ≫ h') =
      (upperStarComp AddCommGrpCat.{u + 1} (DU'.map h'.op) (DU'.map h.op)
        (DU'.map (h ≫ h').op) (DU'.map_comp h'.op h.op)).hom.app (F' i) ≫
      (upperStar AddCommGrpCat.{u + 1} (DU'.map h'.op)).map (φ' h) ≫ φ' h' := by
    intro i j k h h'
    exact hφcomp _ _ _ (Q.map h) (Q.map h')
  let legs' : (Q ⋙ D) ⟶ (Functor.const (ThinSkeleton I)).obj
      (relativeSheafHigherImage g cF.pt p) := Functor.whiskerLeft Q legs
  have hiso := higherDirectImage_relative_continuity DU' DV' η'
    cU' (hcU.whiskerEquivalence E.op) cV' (hcV.whiskerEquivalence E.op) g
    (fun i ↦ hg (Q.op.obj i)) F' φ' hid' hcomp' (Q ⋙ C)
    (fun i ↦ e (Q.obj i)) (by
      intro i j h
      simpa [relativeSheafCoefficientTransition, cU', DU', F', φ',
        Cone.whisker, Category.assoc] using
        hC _ _ (Q.map h))
    (cF.whisker Q) (hcF.whiskerEquivalence E) p (Q ⋙ D)
    (fun i ↦ eD (Q.obj i)) (by
      intro i j h
      simpa [relativeSheafImageTransition, relativeSheafHigherImage, image_map_eq_exchange,
        cV', DV', DU', η', F', φ', Cone.whisker, Category.assoc] using
        hD _ _ (Q.map h))
    (c.whisker Q) (hc.whiskerEquivalence E) legs' (by
      intro i
      simpa [relativeSheafImageLeg, relativeSheafHigherImage, image_map_eq_exchange,
        legs', cU', cV', F', Cone.whisker, Cocone.whisker] using hlegs (Q.obj i))
  have heq : (hc.whiskerEquivalence E).desc
      { pt := relativeSheafHigherImage g cF.pt p, ι := legs' } =
      hc.desc { pt := relativeSheafHigherImage g cF.pt p, ι := legs } := by
    apply (hc.whiskerEquivalence E).hom_ext
    intro i
    rw [IsColimit.fac]
    change legs.app (Q.obj i) = c.ι.app (Q.obj i) ≫ _
    exact (hc.fac { pt := relativeSheafHigherImage g cF.pt p, ι := legs } (Q.obj i)).symm
  change IsIso ((hc.whiskerEquivalence E).desc
    { pt := relativeSheafHigherImage g cF.pt p, ι := legs' }) at hiso
  rwa [heq] at hiso

/-- Relative continuity for higher direct images of compatible abelian étale sheaves.

Source: Stacks Tag 0EYM, lemma-relative-colimit-general, statement and second proof
(blueprint: lem-sf-relative-direct-image-sheaf-limit).

Proof:
1. Pull the coefficient system to the source cone using `etale_system_cone_functor`
   and choose its categorical colimit.
2. Prove composition of the degreewise coefficient exchanges by horizontal derived
   mate pasting, compatibility of the single comparisons, and naturality of the
   exact-pullback homology comparisons. Inverse-image associativity then gives
   composition of the prescribed pulled-back transitions. Identity transitions
   are invertible by the identity-square formula, and idempotent by composition,
   hence identities. This constructs the higher-image functor.
3. Apply the same exchange composition formula to a transition square followed
   by a projection square. The coefficient colimit equation gives naturality of
   the prescribed limit-square legs.
4. Reindex the supplied diagrams and cones along the thin-skeleton equivalence.
   Its source is a directed partial order. Apply the existing conditional theorem
   `higherDirectImage_relative_continuity`, whose exchanges are definitionally
   the maps here. Equivalence preserves the given limits and colimits; uniqueness
   of colimit descent identifies its comparison with the original comparison.
5. The resulting isomorphism, the higher-image colimit cocone and its factorization
   equations give precisely the witnesses required in the statement.
-/
theorem relativeDirectImageSheaf_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DU DV : Iᵒᵖ ⥤ Scheme.{u}) (η : DU ⟶ DV)
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (DU.map h)]
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (DV.map h)]
    [∀ i : Iᵒᵖ, QuasiCompact (η.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (η.app i)]
    (cU : Cone DU) (hcU : IsLimit cU) (cV : Cone DV) (hcV : IsLimit cV)
    (g : cU.pt ⟶ cV.pt)
    (hg : ∀ i : Iᵒᵖ, cU.π.app i ≫ η.app i = g ≫ cV.π.app i)
    (F : ∀ i : I, Sheaf (DU.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (h : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (DU.map h.op)).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, φ (𝟙 i) =
      eqToHom (congrArg (fun f ↦ (upperStar AddCommGrpCat.{u + 1} f).obj (F i))
        (DU.map_id (op i))) ≫ (upperStarId AddCommGrpCat.{u + 1} (DU.obj (op i))).hom.app
          (F i))
    (hφcomp : ∀ (i j k : I) (h : i ⟶ j) (h' : j ⟶ k), φ (h ≫ h') =
      (upperStarComp AddCommGrpCat.{u + 1} (DU.map h'.op) (DU.map h.op)
        (DU.map (h ≫ h').op) (DU.map_comp h'.op h.op)).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (DU.map h'.op)).map (φ h) ≫ φ h') :
    ∃ (C : I ⥤ Sheaf cU.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
      (e : ∀ i : I, C.obj i ≅
        (upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i))).obj (F i))
      (cF : Cocone C),
      (∀ (i j : I) (h : i ⟶ j), C.map h =
        (e i).hom ≫ relativeSheafCoefficientTransition DU cU F φ h ≫ (e j).inv) ∧
      Nonempty (IsColimit cF) ∧
      ∀ p : ℕ, ∃ (D : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
        (eD : ∀ i : I, D.obj i ≅
          (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj
            (relativeSheafHigherImage (η.app (op i)) (F i) p))
        (c : Cocone D) (t : c.pt ≅ relativeSheafHigherImage g cF.pt p),
        (∀ (i j : I) (h : i ⟶ j), D.map h =
          (eD i).hom ≫ relativeSheafImageTransition DU DV η cV F φ p h ≫ (eD j).inv) ∧
        (∀ i : I, c.ι.app i ≫ t.hom = (eD i).hom ≫
          relativeSheafImageLeg DU DV η cU cV g hg F cF.pt
            (fun j ↦ (e j).inv ≫ cF.ι.app j) p i) ∧
        Nonempty (IsColimit c) := by
  classical
  have hid : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (DU.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (DU.obj (op i))).hom.app (F i) := by
    intro i
    rw [hφid]
    congr 1
    simp only [eqToIso.hom, eqToHom_app]
  obtain ⟨C, e, hCraw⟩ := etale_system_cone_functor DU cU F φ hid hφcomp
  have hC : ∀ (i j : I) (h : i ⟶ j), C.map h =
      (e i).hom ≫ relativeSheafCoefficientTransition DU cU F φ h ≫ (e j).inv := by
    intro i j h
    simpa only [relativeSheafCoefficientTransition, Category.assoc] using hCraw i j h
  refine ⟨C, e, colimit.cocone C, ?_, ⟨colimit.isColimit C⟩, ?_⟩
  · exact hC
  · intro p
    let H := fun i : I ↦ relativeSheafHigherImage (η.app (op i)) (F i) p
    let ψ := fun {i j : I} (h : i ⟶ j) ↦
      relativeSheafHigherImageMap ⟨η.naturality h.op⟩ (F i) (F j) (φ h) p
    have hψcomp : ∀ (i j k : I) (h : i ⟶ j) (h' : j ⟶ k), ψ (h ≫ h') =
        (upperStarComp AddCommGrpCat.{u + 1} (DV.map h'.op) (DV.map h.op)
          (DV.map (h ≫ h').op) (DV.map_comp h'.op h.op)).hom.app (H i) ≫
        (upperStar AddCommGrpCat.{u + 1} (DV.map h'.op)).map (ψ h) ≫ ψ h' := by
      intro i j k h h'
      dsimp only [ψ]
      rw [hφcomp]
      exact higher_image_map_comp_of_eq ⟨η.naturality h.op⟩ ⟨η.naturality h'.op⟩
        (DU.map (h ≫ h').op) (DV.map (h ≫ h').op)
        (DU.map_comp h'.op h.op) (DV.map_comp h'.op h.op)
        ⟨η.naturality (h ≫ h').op⟩ (F i) (F j) (F k) (φ h) (φ h') p
    have hTcomp {i j k : I} (h : i ⟶ j) (h' : j ⟶ k) :
        relativeSheafImageTransition DU DV η cV F φ p (i := i) (j := k) (h ≫ h') =
          relativeSheafImageTransition DU DV η cV F φ p (i := i) (j := j) h ≫
          relativeSheafImageTransition DU DV η cV F φ p (i := j) (j := k) h' :=
      cone_transition_comp DV cV H ψ hψcomp (i := i) (j := j) (k := k) h h'
    have hTid (i : I) :
        relativeSheafImageTransition DU DV η cV F φ p (i := i) (j := i) (𝟙 i) = 𝟙 _ := by
      have : IsIso (φ (𝟙 i)) := by rw [hφid]; infer_instance
      have : IsIso (ψ (𝟙 i)) := higher_image_map_identity_isIso _ _ _
        (DU.map_id (op i)) (DV.map_id (op i)) _ (F i) (φ (𝟙 i)) p
      have : IsIso (relativeSheafImageTransition DU DV η cV F φ p (i := i) (j := i) (𝟙 i)) := by
        dsimp only [relativeSheafImageTransition]
        change IsIso (_ ≫ (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).map (ψ (𝟙 i)))
        infer_instance
      apply (cancel_epi
        (relativeSheafImageTransition DU DV η cV F φ p (i := i) (j := i) (𝟙 i))).1
      simpa only [Category.comp_id, Category.id_comp] using (hTcomp (𝟙 i) (𝟙 i)).symm
    let D : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      { obj := fun i ↦ (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj (H i)
        map := fun {i j} h ↦
          relativeSheafImageTransition DU DV η cV F φ p (i := i) (j := j) h
        map_id := hTid
        map_comp := hTcomp }
    let lam := fun i : I ↦ (e i).inv ≫ (colimit.cocone C).ι.app i
    have hlam {i j : I} (h : i ⟶ j) : lam i =
        relativeSheafCoefficientTransition DU cU F φ (i := i) (j := j) h ≫ lam j := by
      dsimp only [lam]
      rw [← (colimit.cocone C).w h, hC]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    let legs : D ⟶ (Functor.const I).obj
        (relativeSheafHigherImage g (colimit.cocone C).pt p) :=
      { app := fun i ↦ relativeSheafImageLeg DU DV η cU cV g hg F (colimit.cocone C).pt lam p i
        naturality := by
          intro i j h
          dsimp only [Functor.const_obj_map, D]
          erw [Category.comp_id]
          dsimp only [relativeSheafImageLeg]
          rw [hlam h]
          simpa only [relativeSheafImageTransition, relativeSheafCoefficientTransition,
            Category.assoc] using
            (higher_image_map_comp_of_eq ⟨η.naturality h.op⟩ ⟨hg (op j)⟩
              (cU.π.app (op i)) (cV.π.app (op i)) (cU.w h.op).symm (cV.w h.op).symm
              ⟨hg (op i)⟩ (F i) (F j) (colimit.cocone C).pt (φ h) (lam j) p).symm }
    have hiso := continuity_preorder DU DV η cU hcU cV hcV g hg F φ hid hφcomp
      C e hC (colimit.cocone C) (colimit.isColimit C) p D (fun i ↦ Iso.refl _)
      (by
        intro i j h
        dsimp only [D, Iso.refl_hom, Iso.refl_inv]
        erw [Category.id_comp, Category.comp_id])
      (colimit.cocone D) (colimit.isColimit D) legs
      (by
        intro i
        dsimp only [legs, Iso.refl_hom, lam]
        erw [Category.id_comp])
    let c : Cocone D := { pt := relativeSheafHigherImage g (colimit.cocone C).pt p, ι := legs }
    have : IsIso (colimit.desc D c) := hiso
    refine ⟨D, fun i ↦ Iso.refl _, colimit.cocone D, asIso (colimit.desc D c), ?_, ?_,
      ⟨colimit.isColimit D⟩⟩
    · intro i j h
      dsimp only [D, Iso.refl_hom, Iso.refl_inv]
      erw [Category.id_comp, Category.comp_id]
    · intro i
      simp only [Iso.refl_hom, Category.id_comp]
      exact colimit.ι_desc c i

end AlgebraicGeometry.Etale
