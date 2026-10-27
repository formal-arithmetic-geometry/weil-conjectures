/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.IndEtaleQcqsDirectImageBaseChange

/-! # Open terms of localization under affine ind-etale pullback

Source: Stacks Project, Tags 03Q9 and 0A45.
(blueprint: lem-per-ind-etale-open-localization-comparison).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- Ind-etale pullback identifies the open terms and their canonical units.
This statement concerns ordinary open direct images, with no closed support functor.

Source: Stacks Project, Tag 03Q9, applied to the complementary open, and
sites-cohomology Tag 07A7 for compatibility of exchange with the unit.
(blueprint: lem-per-ind-etale-open-localization-comparison).

Proof: The complements of the two closed immersions form a Cartesian square:
the inverse image of a complement is the complement of the inverse image.
The open immersion into the Noetherian target is quasi-compact and quasi-separated.
For every point of T', choose an affine neighbourhood of its image in T; its
inverse image is affine since g is affine, and its section map is the given
ind-etale map. Apply ordinary affine locally ind-etale direct-image base change
to j and j* K. Transport from the chosen fibre product to U' and use inverse-image
composition to identify q* j* K with j'* g* K. This constructs the isomorphism E.
To prove the displayed equation, transpose under j'* adjoint to Rj'*. The exchange
mate and the inverse-image compositor reduce its left side to the identity by
the triangle identity for j; the right side transposes to the identity by the
triangle identity for j'. This also covers empty complements and arbitrary lower
bounds. No constructibility or torsion assumption on K is used. -/
theorem indEtale_openLocalization_comparison
    (A : Type (u + 1)) [CommRing A]
    {Z Z' T T' U U' : Scheme.{u}} [IsNoetherian T] [IsNoetherian T']
    (i : Z ⟶ T) (i' : Z' ⟶ T') [IsClosedImmersion i] [IsClosedImmersion i']
    (j : U ⟶ T) (j' : U' ⟶ T') [IsOpenImmersion j] [IsOpenImmersion j']
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hij' : Set.range i'.base = (Set.range j'.base)ᶜ)
    (h : Z' ⟶ Z) (g : T' ⟶ T) [IsAffineHom g]
    (hg : ∀ V : T.Opens, IsAffineOpen V →
      RingHom.IndEtaleAcrossUniverses (g.app V).hom)
    (sq : IsPullback h i' i g)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ∃ E :
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj
        ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlus.obj
          ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj K)) ≅
      (lowerStar (ModuleCat.{u + 1} A) j').rightDerivedFunctorPlus.obj
        ((upperStar (ModuleCat.{u + 1} A) j').mapDerivedCategoryPlus.obj
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj K)),
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).derivedPlus.unit.app K) ≫
        E.hom =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j').derivedPlus.unit.app
        ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj K) := by sorry

end AlgebraicGeometry.Etale
