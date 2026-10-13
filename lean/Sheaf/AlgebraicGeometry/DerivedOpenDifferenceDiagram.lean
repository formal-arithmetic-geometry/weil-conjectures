/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps

/-! # The difference diagram before derived open gluing

Source: Stacks Project, Tag 08DG, the difference arrow and its split restrictions.
(blueprint: lem-sc-derived-open-difference-diagram).
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
-- The threefold transported restriction needs additional instance search.
set_option maxHeartbeats 1600000 in
-- The derived restriction functors and their comparisons need this elaboration budget.
/-- The difference arrow has split normal form on each of the two opens.
The middle and last objects are the explicit direct-image sum and overlap image.
This constructs their maps, not a glued object.
Source: Stacks Project, Cohomology, Tag 08DG, construction of the difference arrow;
Tag 08FE for restriction of direct images
(blueprint: lem-sc-derived-open-difference-diagram).

Proof: write W = U ∩ V and use the exact restriction functors rU, rV, rW and
sU, sV displayed below. Their canonical composition comparisons are eU and eV.
The underived open adjunction is `(Scheme.Modules.restrictAdjunction O.ι).ofNatIsoLeft
(Scheme.Modules.overFunctorEquiv O).symm`; derive it with
`Adjunction.mapDerivedCategoryRightDerivedAdjunction`. Call these adjunctions
adjU, adjV and adjW. Take E = RjU_* A ⊕ RjV_* B and D = RjW_* (sV B).
The adjunction counits define
pU : rU E → A and pV : rV E → B by projection onto the corresponding summand.
The adjoint of c on the U summand and the negative of the adjoint of the identity
on the V summand define d : E → D. Explicitly, adjW.homEquiv sends
(eU⁻¹ on RjU A, then sU of adjU.counit on A, then c) to the U component;
it sends (eV⁻¹ on RjV B, then sV of adjV.counit on B) to the V component.
Take biprod.desc of the first and the negative of the second. The projections are
rU(biprod.fst) followed by adjU.counit and rV(biprod.snd) followed by adjV.counit.
The restriction counit k is adjW.counit on sV B, a map rW D → sV B.
Naturality and the triangle identities of the three derived open adjunctions give
(eU⁻¹ followed by sU pU followed by c) minus (eV⁻¹ followed by sV pV) = rW d
followed by k. Here the equivalence unit in eU and eV is precisely the comparison
between restriction on the over-category and restriction on the open subscheme.
By Tag 08FE, on U the V summand of E and D both identify with the same derived
pushforward from W to U; d on this summand is minus its identity. The U summand
restricts to A, with pU its identity and pU zero on the other summand. Thus the
matrix (pU, rU d) is invertible: its diagonal is (1, -1), and subtracting the
lower-left entry gives its explicit inverse. On V the analogous matrix has
invertible diagonal given by the identity on B and the direct image of c after
interchanging summands, hence is invertible too.
These sectionwise adjunction and matrix calculations remain valid for empty opens
or empty W, when the corresponding category is zero. No covering hypothesis is
needed for these local calculations, though it is retained for the caller. -/
theorem derived_open_difference_diagram
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (c : (schemeOpenOverlapRestriction X
        (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory.obj A ≅
      (schemeOpenOverlapRestriction X
        (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory.obj B) :
    let rU := (schemeOpenRestriction X U).mapDerivedCategory;
    let rV := (schemeOpenRestriction X V).mapDerivedCategory;
    let sU := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory;
    let sV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory;
    let rW := (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory;
    let eU := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U);
    let eV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V);
    let E := (schemeDerivedDirectImage U.ι).obj A ⊞ (schemeDerivedDirectImage V.ι).obj B;
    let D := (schemeDerivedDirectImage (U ⊓ V).ι).obj (sV.obj B);
    ∃ (d : E ⟶ D)
      (pU : rU.obj E ⟶ A) (pV : rV.obj E ⟶ B)
      (k : rW.obj D ⟶ sV.obj B),
      IsIso (biprod.lift pU (rU.map d)) ∧
      IsIso (biprod.lift pV (rV.map d)) ∧
      eU.inv.app E ≫ sU.map pU ≫ c.hom - eV.inv.app E ≫ sV.map pV = rW.map d ≫ k := by
  sorry

end AlgebraicGeometry
