/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.DerivedOpenLocalization
import Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction
import Sheaf.AlgebraicGeometry.SchemeDerivedHomGluing

/-! # Gluing morphisms between fixed objects on an open union

Source: Stacks Project, Tag 08BW.
(blueprint: lem-sc-open-union-hom-gluing).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Compatible local maps between restrictions of two fixed ambient objects glue on
an open union. The conclusion constructs a map, and does not construct objects
or local isomorphisms. No lift to a morphism on all of X is asserted.
Source: Stacks Project, Tag 08BW, exactness at the local Hom pair, on W union V.
(blueprint: lem-sc-open-union-hom-gluing).

Proof: Set Y = W union V and pull W and V back to covering opens of Y. Restrict
G and E to Y. Transport the local morphisms a and b through the canonical derived
equivalences for the pulled-back open schemes. Their transported forms are
kW(G) followed by a followed by kW(E) inverse, and similarly for V. The canonical
composition comparison for a chain of open inclusions is obtained from
Modules.overMapCompOverEquiv, overFunctorEquiv, restrictFunctorComp and
restrictFunctorCongr. Its naturality and the equivalence triangle identities
identify compatibility of these transported maps with exactly the hypothesis
using sW and sV. Apply scheme_derived_hom_gluing on Y to the two fixed objects
L(G), L(E) and this compatible pair. Transport its two restriction equations
back and compose on the right with kW(E) and kV(E); cancellation of each
comparison and its inverse gives the displayed equations. Additional derived
categories on the pulled-back opens in Hom universe w are obtained from
nonempty_derivedOpenLocalization and open_derived_localization_adjunction.
Empty opens, a disjoint intersection, and the empty union are included by
Mayer--Vietoris exactness; uniqueness is neither needed nor asserted. -/
theorem exists_open_union_hom
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    (G E : schemeDerivedCategory X) :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ W ⊔ V)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_right : V ⟶ W ⊔ V)
    ∀ (a : JW.obj G ⟶ JW.obj E) (b : JV.obj G ⟶ JV.obj E),
      sW.inv.app G ≫ SW.map a ≫ sW.hom.app E =
        sV.inv.app G ≫ SV.map b ≫ sV.hom.app E →
      ∃ (α : L.obj G ⟶ L.obj E),
        PW.map α ≫ kW.hom.app E = kW.hom.app G ≫ a ∧
        PV.map α ≫ kV.hom.app E = kV.hom.app G ≫ b := by sorry

end AlgebraicGeometry.Scheme
