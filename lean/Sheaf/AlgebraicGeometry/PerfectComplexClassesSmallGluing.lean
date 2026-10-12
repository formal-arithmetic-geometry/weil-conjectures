/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplexClassesSmallOnOpen
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Gluing smallness of perfect isomorphism classes

Source: Step 2 of lem-pc-perfect-complexes-compact-set, using Stacks Project,
Tags 08BV and 08DR (blueprint: lem-pc-perfect-classes-small-gluing).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Smallness of perfect isomorphism classes glues across a quasi-compact open
and an affine open when it holds on both opens and their intersection.
Source: Step 2 of lem-pc-perfect-complexes-compact-set; Stacks Project,
Tags 08BV and 08DR (blueprint: lem-pc-perfect-classes-small-gluing).

Proof: For an open immersion `f : Y ⟶ X` with image `U ⊔ V`, pull back `U` and
`V` to opens of `Y`. They cover `Y`; their images in `X` are `U` and `V`, and
the intersection has image `U ⊓ V`. These opens and `Y` are quasi-compact;
quasi-separatedness is inherited from `X`. Transport the given derived-category
structures on the localized open sites of
`Y` along the equivalences with module sheaves on its open subschemes. Iterating
localization identifies their further open sites with open sites of `Y`, so this
also supplies all the local structures required by the three hypotheses, in the
same universe `w`; no fresh localization in universe `w` is assumed. Obtain small
skeletons from those hypotheses.
Restrict a perfect object to the three opens. Restriction preserves perfectness
by restricting its strictly perfect local models, and preserves quasi-coherence.
Use `schemeDerived_mayerVietoris_triangle` to express the object as a cocone of
the second map in its triangle. Replace the three restrictions by skeleton
representatives and transport that map along the resulting direct-image
isomorphisms. For a fixed triple of representatives the possible maps are
`u`-small: compute derived morphisms by a K-injective resolution in the category
of `u`-valued module sheaves on the `u`-small open site. Chain maps are `u`-small,
and homotopy classes are quotients of that small type; comparison with the
chosen localization is fully faithful (Mathlib's
`CochainComplex.IsKInjective.Qh_map_bijective`). Thus this holds even when its morphism
universe `w` is larger than `u`. The type of triples together with such a map
is `u`-small. Cocones of a fixed map are unique up to isomorphism, by the
morphism-of-triangles axiom and the two-out-of-three isomorphism lemma.
Restrict the type of maps to those admitting a perfect quasi-coherent cocone.
Each such map determines a unique skeleton class of cocones by the preceding
uniqueness argument; only this class, not an arbitrary cocone object, is selected.
Every perfect object supplies such a map. The resulting map surjects onto the
skeleton of perfect objects of `Y`, so that skeleton is
`u`-small. This proves the required property for every `f` and every choice of
derived-category structures. Empty opens cause no exception: their derived
category has only the zero isomorphism class. -/
theorem perfectComplex_classesSmallOnOpen_union (X : Scheme.{u})
    [QuasiSeparatedSpace X] (U V : X.Opens) (hU : IsCompact (U : Set X))
    (hV : IsAffineOpen V)
    (pU : PerfectComplexClassesSmallOnOpen.{u, w} X U)
    (pV : PerfectComplexClassesSmallOnOpen.{u, w} X V)
    (pUV : PerfectComplexClassesSmallOnOpen.{u, w} X (U ⊓ V)) :
    PerfectComplexClassesSmallOnOpen.{u, w} X (U ⊔ V) := by sorry

end AlgebraicGeometry.Scheme
