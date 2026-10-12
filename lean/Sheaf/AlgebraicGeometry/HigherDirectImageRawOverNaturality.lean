/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

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
            (higherDirectImageRawOverPullback Λ k G q f U z) := by
  sorry

end AlgebraicGeometry.Etale
