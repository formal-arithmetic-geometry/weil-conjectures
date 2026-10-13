/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import Sheaf.Algebra.Homology.SingleComplexAffineBaseChange

/-! # Affine source opens in the single-complex induction

Source: Stacks Project, Tags 0DJ8 and 0DJ9, affine case.
(blueprint: lem-pc-single-complex-open-affine).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The affine base case, with a source open in the coordinates used by induction.
Source: Stacks Project, Tag 0DJ9, affine-open paragraph, and Tag 0DJ8.
(blueprint: lem-pc-single-complex-open-affine).

Proof: The inverse image U' of the affine U is affine since both bases are affine.
Restriction preserves quasi-coherent cohomology and the stalk condition: the local
rings at points of an open subscheme are the original local rings, and the canonical
pullback composition maps transport phi to its restriction. Identify U, U', S, S'
with the spectra of their global section rings. Transport the cartesian square,
objects and phi along these isomorphisms. Apply singleComplexAffineBaseChange.
Naturality of the derived adjunction counits and pullback composition comparisons
identifies its comparison with singleComplexOpenComparison. Transport invertibility
back. For the empty affine open both derived categories are zero and the same
comparison is invertible. No boundedness hypothesis is used. -/
theorem singleComplexOpenComparison_affine
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ U) := by sorry

end AlgebraicGeometry
