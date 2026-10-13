/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction

/-! # Invertible cross components of the open difference map

Source: Stacks Project, Tags 08DG and 08FE, restriction of the overlap counit.
(blueprint: lem-sc-derived-open-cross-components-iso).
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
-- Threefold transported overlap restrictions require additional instance search.
set_option maxHeartbeats 1600000 in
-- Transported threefold restrictions require the same instance budget as the parent theorem.
/-- The adjoint overlap counits are invertible on the opposite open. This concerns
only the individual summands, without choosing a difference diagram or a gluing object.
Source: Stacks Project, Cohomology, Tag 08DG (lemma-glue), the restriction of the
second arrow to U and V; Tag 08FE (lemma-restrict-direct-image).
(blueprint: lem-sc-derived-open-cross-components-iso).

Proof: first use the derived adjunctions obtained from exact open restriction.
The open pushforwards are fully faithful, so their derived counits are invertible.
By Tag 08FE the restriction of RjV_* B to U identifies with the pushforward from
W = U ∩ V to U of B restricted to W. The same identification applies to the
restriction of RjW_* (sV B) to U. Under these comparisons the adjoint b of the
overlap counit is the identity: at the underived level all maps evaluate on the
same intersection open, and the unit and counit cancel by their triangle identity.
Compute the derived comparison on K-injective resolutions. Open restrictions
preserve K-injectivity, so the same sectionwise identity represents rU(b).
Thus rU(b) is invertible. The symmetric calculation identifies rV(a) with the
pushforward from W to V of c, followed by the corresponding invertible comparison.
It is invertible because c is an isomorphism. For adjunctions other than the
canonical derived adjunctions, uniqueness of adjoints identifies their counits
with the canonical ones followed by natural automorphisms; naturality and the
triangle identities show that the adjoint components change by automorphisms
on their source and target. Invertibility therefore holds for the adjunctions
specified in the statement. When either open or W is empty the same calculations
take place in the zero derived category, and no covering premise is used. -/
theorem derived_open_cross_components_isIso
    (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (c : (schemeOpenOverlapRestriction X
        (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory.obj A ≅
      (schemeOpenOverlapRestriction X
        (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory.obj B)
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjW : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι) :
    let rU := (schemeOpenRestriction X U).mapDerivedCategory;
    let rV := (schemeOpenRestriction X V).mapDerivedCategory;
    let sU := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory;
    let sV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory;
    let rW := (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory;
    let eU := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U);
    let eV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V);
    let AU := (schemeDerivedDirectImage U.ι).obj A;
    let BV := (schemeDerivedDirectImage V.ι).obj B;
    let a := adjW.homEquiv AU (sV.obj B)
      (eU.inv.app AU ≫ sU.map (adjU.counit.app A) ≫ c.hom);
    let b := adjW.homEquiv BV (sV.obj B)
      (eV.inv.app BV ≫ sV.map (adjV.counit.app B));
    IsIso (rU.map b) ∧ IsIso (rV.map a) := by sorry

end AlgebraicGeometry
