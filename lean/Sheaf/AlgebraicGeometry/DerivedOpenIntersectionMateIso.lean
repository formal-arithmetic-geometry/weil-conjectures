/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction

/-! # The restriction mate for the intersection of two opens

Source: Stacks Project, Tags 08FE and 08DG.
(blueprint: lem-sc-derived-open-intersection-mate-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
-- The transported overlap restriction requires additional instance search.
set_option maxHeartbeats 1600000 in
-- The derived composition comparison requires a larger elaboration budget.
/-- Restricting the canonical mate from the direct image on P to the direct image
on O ∩ P gives an isomorphism on O. This concerns a single direct-image summand;
it does not construct a difference diagram or assert invertibility of a matrix.
Source: Stacks Project, Cohomology, Tag 08FE and the split restriction calculation
in the proof of Tag 08DG.
(blueprint: lem-sc-derived-open-intersection-mate-iso).

Proof: write W = O ∩ P. For a K-injective complex I representing B on P,
restriction to W is K-injective by Tag 08BS. Both (RjP_* B)|O and
(RjW_*(B|W))|O are therefore computed by direct image to O of I|W,
by Tag 08FE. On an open T of O both complexes have sections I(T ∩ P).
The displayed mate is the identity under these identifications: its adjoint
is the restriction of the P counit, transported through the canonical
composition comparison. This follows sectionwise from the restriction
counit and its triangle identity; deriving preserves the equality.
Thus it is an isomorphism. Changing either adjunction on the fixed pair
of functors conjugates the mate by natural automorphisms of the right
adjoints and does not affect invertibility. This also handles empty opens
and the empty intersection, when the corresponding complexes are zero. -/
theorem derived_open_intersection_mate_isIso
    (X : Scheme.{u}) (O P W : X.Opens) (hW : W = O ⊓ P) (i : W ⟶ P)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings P.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (adjP : (schemeOpenRestriction X P).mapDerivedCategory ⊣ schemeDerivedDirectImage P.ι)
    (adjW : (schemeOpenRestriction X W).mapDerivedCategory ⊣ schemeDerivedDirectImage W.ι)
    (B : schemeDerivedCategory P.toScheme) :
    let sP := (schemeOpenOverlapRestriction X i).mapDerivedCategory;
    let eP := schemeDerivedOpenRestrictionCompIso X i;
    IsIso ((schemeOpenRestriction X O).mapDerivedCategory.map
      ((adjW.homEquiv ((schemeDerivedDirectImage P.ι).obj B) (sP.obj B))
        (eP.inv.app _ ≫ sP.map (adjP.counit.app B)))) := by sorry

end AlgebraicGeometry
