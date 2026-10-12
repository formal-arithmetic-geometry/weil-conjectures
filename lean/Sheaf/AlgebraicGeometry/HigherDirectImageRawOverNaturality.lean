/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
import Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

import Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom

/-! # Raw cohomology pullback and the higher-image comparison

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-naturality).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Raw cohomology with coefficients restricted from W. -/
noncomputable abbrev higherDirectImageRawOverPresheaf
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (B : Over W) :=
  higherDirectImagePresheaf Λ (B.hom ≫ k) q
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G))

/-- The canonical raw comparison, with its underlying abelian target made explicit. -/
noncomputable abbrev higherDirectImageRawOverComparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (B : Over W) :
    higherDirectImageRawOverPresheaf Λ k G q B ⟶
      (higherDirectImage Λ (B.hom ≫ k) q
        (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
  higherDirectImagePresheafToSheaf Λ (B.hom ≫ k) q
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G))

/-- Pullback of a raw cohomology class for coefficients restricted from W.
The factors are pullback composition, the single-functor comparison, pullback
of the class, shift comparison, and the canonical coefficient identification.
Source: Stacks Project, Tag 09Z1, canonical cohomology comparison maps. -/
noncomputable def higherDirectImageRawOverPullback
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w])).hom.app _) ≫
    (((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    D+((f.left)^*[ModuleCat.{u + 1} Λ]).map z ≫
    (D+((f.left)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) ≫
    (shiftFunctor _ q).map
      ((((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
            (Over.w f).symm).inv.app G))

private lemma raw_presheaf_map_apply
    (Λ : Type (u + 1)) [CommRing Λ] {Y S : Scheme.{u}} (h : Y ⟶ S) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {T U : S.Etale} (a : T ⟶ U) (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (higherDirectImagePresheaf Λ h q K).map a.op z =
      (DerivedCategory.Plus.singleFunctor _ 0).map
        (((h)^*[ModuleCat.{u + 1} Λ]).map ((freeSheaf Λ S).map a)) ≫ z := rfl

private lemma pullback_class_naturality
    {C D E D' E' : Type*} [Category* C] [Category* D] [Category* E]
    [Category* D'] [Category* E']
    (F : C ⥤ D) (G : C ⥤ E) (L : D ⥤ E)
    (SD : D ⥤ D') (SE : E ⥤ E') (LD : D' ⥤ E')
    (c : G ⟶ F ⋙ L) (t : SD ⋙ LD ≅ L ⋙ SE)
    {X Y : C} (a : X ⟶ Y) {Z : D'} {Z' : E'}
    (z : SD.obj (F.obj Y) ⟶ Z) (e : LD.obj Z ⟶ Z') :
    SE.map (c.app X) ≫ t.inv.app (F.obj X) ≫
        LD.map (SD.map (F.map a) ≫ z) ≫ e =
      SE.map (G.map a) ≫ SE.map (c.app Y) ≫ t.inv.app (F.obj Y) ≫ LD.map z ≫ e := by
  have hc := c.naturality a
  have ht := t.inv.naturality (F.map a)
  change G.map a ≫ c.app Y = c.app X ≫ L.map (F.map a) at hc
  change SE.map (L.map (F.map a)) ≫ t.inv.app (F.obj Y) =
    t.inv.app (F.obj X) ≫ LD.map (SD.map (F.map a)) at ht
  rw [LD.map_comp, Category.assoc, ← reassoc_of% ht,
    ← SE.map_comp_assoc, ← hc, SE.map_comp, Category.assoc]

/-- The comparison component of raw pullback with the higher direct image map.
Source: Stacks Project, Tags 03Q8 and 09Z1; canonical derived-Hom comparison.
(blueprint: sbc-lem-higher-image-raw-over-comparison).
The proof expands the adjunction comparison, applies the triangle identity,
and identifies the resulting shifted homology map with the canonical transition.
-/
theorem higherDirectImageRawOverPullback_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverComparison Λ k G q A).app (op U)
        (higherDirectImageRawOverPullback Λ k G q f U z) =
    ((higherDirectImageOverMap Λ k G q f).hom.app (op U))
      ((higherDirectImageRawOverComparison Λ k G q B).app (op U) z) := by
  sorry

/-- Restriction component of raw pullback naturality.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-restriction).
The proof is the naturality of the pullback composition and single-complex
comparison maps under restriction of the étale test object.
-/
theorem higherDirectImageRawOverPullback_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U))
    (T : S.Etale) (a : T ⟶ U) :
      higherDirectImageRawOverPullback Λ k G q f T
        ((higherDirectImageRawOverPresheaf Λ k G q B).map a.op z) =
      (higherDirectImageRawOverPresheaf Λ k G q A).map a.op
            (higherDirectImageRawOverPullback Λ k G q f U z) := by
  sorry

/-- Raw pullback intertwines the fixed cohomology-presheaf comparison with the
canonical higher-image transition. This requires no limit or qcqs assumptions.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-over-naturality).

Proof: Expand the raw class comparison as derived adjunction followed by degree-zero
homology and evaluation at the identity generator of the free module sheaf of U.
Expand the transition as unit, pullback composition, and counit. Naturality of the
unit moves the class through pullback, and the triangle identity cancels the
counit against the unit in its adjoint image. The pullback composition comparison
on single complexes then gives the first two factors of the raw pullback. Shift
compatibility gives its fourth factor; the last factor is the shifted coefficient
identification. Naturality of homology and evaluation proves the equality.
For restriction along a : T -> U, use naturality of the pullback composition
and single-functor isomorphisms in the free sheaf of U. Functoriality moves its
precomposition through pullback; associativity gives the second equality.
The comparisons are the fixed constructions, not arbitrarily chosen isomorphisms. -/
theorem higherDirectImageRawOverPullback_toSheaf
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverComparison Λ k G q A).app (op U)
        (higherDirectImageRawOverPullback Λ k G q f U z) =
    ((higherDirectImageOverMap Λ k G q f).hom.app (op U))
      ((higherDirectImageRawOverComparison Λ k G q B).app (op U) z) ∧
    ∀ (T : S.Etale) (a : T ⟶ U),
      higherDirectImageRawOverPullback Λ k G q f T
        ((higherDirectImageRawOverPresheaf Λ k G q B).map a.op z) =
      (higherDirectImageRawOverPresheaf Λ k G q A).map a.op
            (higherDirectImageRawOverPullback Λ k G q f U z)  := by
  exact ⟨higherDirectImageRawOverPullback_comparison Λ k G q f U z,
    fun T a => higherDirectImageRawOverPullback_restriction Λ k G q f U z T a⟩

end AlgebraicGeometry.Etale
