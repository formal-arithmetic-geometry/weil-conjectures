/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.ConstructibleSheaf.DerivedMorphismDescentShift
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.Concentrated
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekInvertible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Gluing comparisons along the affine line

The inputs of the gluing half of blueprint `prop-pur-a1-invariance`
(`AlgebraicGeometry.Etale.existsUnique_iso_leftDerivedUpperStar_of_etale`):

* the unit section of `𝔸¹_S` is a closed immersion meeting every fibre, and the affine line
  commutes with fibre products;
* a shift and twist of a lisse rank-one sheaf is invertible, and is a sheaf placed in one
  degree (`AlgebraicGeometry.Etale.exists_iso_tateTwist_singleFunctor_obj`);
* *agreement on overlaps*: two comparisons normalized at the unit section have the same
  restriction to the overlap of an étale cover, comparisons out of an invertible object being
  determined at the unit section
  (`AlgebraicGeometry.Etale.conj_leftDerivedUpperStar_eq_of_section`);
* *gluing*: an isomorphism between pullbacks of invertible objects concentrated in one degree
  whose two restrictions to the overlap agree descends
  (`AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_map_hom_eq_of_isPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

end Etale

end AlgebraicGeometry
