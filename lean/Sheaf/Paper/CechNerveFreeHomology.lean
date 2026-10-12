/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Sheaf.AlgebraicTopology.SetCechNerveFreeResolution
import Sheaf.Paper.ImagePresheafSheafificationIso

/-!
# Free-module homology of a Čech nerve

Source: Stacks Project, Hypercoverings, Lemma 01GC (lemma-compare-cosk0),
with the same contraction over a commutative ring instead of ℤ
(blueprint: lem-weil-pbc-cech-nerve-free-homology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The sheafified free-module Čech nerve of a presheaf map surjective after
sheafification has zero positive homology; its canonical augmentation induces an
isomorphism on degree-zero homology to the free-module sheaf on the target.

Source: Stacks Project, Hypercoverings, Lemma 01GC (lemma-compare-cosk0),
lines 590--660, with free R-modules in place of free abelian groups.
(blueprint: lem-weil-pbc-cech-nerve-free-homology).

Proof:
1. Replace G by the image presheaf G' of F → G. The Čech nerve is unchanged,
and the augmentation factors through R[G'].
2. Objectwise apply lem-weil-pbc-set-cech-nerve-free-resolution to F(U) → G'(U).
Choosing a preimage in each nonempty fibre contracts its free R-module nerve.
Thus positive homology vanishes and the augmentation identifies H₀ with R[G'(U)].
3. Homology of module presheaves is sectionwise, and these augmentation-induced
identifications commute with restrictions: use
lem-weil-pbc-site-r-module-presheaf-sheafification-exact, clause (1).
4. By clause (2) of that lemma, additive exact sheafification commutes with
homology, giving zero positive homology and H₀ ≅ R[G']#.
5. Apply lem-weil-pbc-image-presheaf-sheafification-iso to G' → G, then
lem-weil-pbc-free-module-sheafification-local-iso to its free-module map.
The resulting H₀ ≅ R[G]# is induced by the original augmentation R[F]# → R[G]#.
-/
theorem freeModule_cechNerve_homology
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Type (u)) [CommRing R]
    (f : Arrow (Cᵒᵖ ⥤ Type (u)))
    (hsurj : Sheaf.IsLocallySurjective
      ((presheafToSheaf J.toGrothendieck (Type (u))).map f.hom)) :
    (∀ i : ℕ, 0 < i → IsZero
      (((AlgebraicTopology.alternatingFaceMapComplex
        (Sheaf J.toGrothendieck (ModuleCat.{u} R))).obj
          (f.cechNerve ⋙
            (Functor.whiskeringRight Cᵒᵖ (Type (u)) (ModuleCat.{u} R)).obj
              (ModuleCat.free R) ⋙
            presheafToSheaf J.toGrothendieck (ModuleCat.{u} R))).homology i)) ∧
    IsIso (HomologicalComplex.homologyMap
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        ((SimplicialObject.Augmented.whiskeringObj _ _
          ((Functor.whiskeringRight Cᵒᵖ (Type (u)) (ModuleCat.{u} R)).obj
            (ModuleCat.free R) ⋙
            presheafToSheaf J.toGrothendieck (ModuleCat.{u} R))).obj
          f.augmentedCechNerve)) 0) := by
  sorry

end CategoryTheory
