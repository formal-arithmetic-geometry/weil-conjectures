/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.DerivedOpenGluing
import Sheaf.AlgebraicGeometry.DerivedOpenLocalization
import Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction

/-! # Relative two-open gluing without local finiteness conditions

Source: Stacks Project, Tag 08DG, Lemma cohomology-lemma-glue.
(blueprint: lem-sc-relative-open-gluing).
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
/-- Glue derived objects and compatible maps on the union, using ambient relative
restriction. No perfectness or support is asserted.
Source: Stacks Project, Tag 08DG, Lemma cohomology-lemma-glue.
(blueprint: lem-sc-relative-open-gluing).

Proof: Put Y = W union V. Pull W and V back along Y.ι to opens U and Z of Y.
They cover Y; U.toScheme, Z.toScheme and their intersection are canonically
isomorphic to W.toScheme, V.toScheme and (W intersect V).toScheme. The exact
module-sheaf equivalences for these isomorphisms induce derived equivalences.
Transport A, B and c to U, Z and their intersection. Exact restriction commutes
with this transport: compose Modules.overMapCompOverEquiv, overFunctorEquiv,
restrictFunctorComp and restrictFunctorCongr for the inclusion identities, then
apply mapDerivedCategoryNatIso and mapDerivedCategoryCompIso. The comparisons
identify restriction of L(E) to U and Z with JW(E) and JV(E), by kW and kV.
Naturality and the unit/counit identities identify the transported overlap
compatibility with the displayed hypothesis involving sW and sV. Apply
derived_open_gluing on Y to the transported data and target L(E). For any
additional fixed-universe localizations, first use nonempty_derivedOpenLocalization
on Y and open_derived_localization_adjunction on its opens. Transport the resulting
local isomorphisms back along the derived equivalences and compose the map equations
with kW and kV. This gives F, alpha, iW and iV and exactly the stated equations.
No witnesses are chosen to define data elsewhere: this is an existential theorem.
The argument uses all derived complexes, with no boundedness, perfectness,
quasi-coherence, quasi-compactness or support assumptions. Empty W or V and empty
Y are included, since pullback opens still cover and all equivalences remain valid. -/
theorem exists_relative_open_gluing
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory W.toScheme) (B : schemeDerivedCategory V.toScheme) :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ W ⊔ V)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_right : V ⟶ W ⊔ V)
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    ∀ (c : SW.obj A ≅ SV.obj B) (E : schemeDerivedCategory X)
      (a : A ⟶ JW.obj E) (b : B ⟶ JV.obj E),
      SW.map a ≫ sW.hom.app E = c.hom ≫ SV.map b ≫ sV.hom.app E →
      ∃ (F : schemeDerivedCategory (W ⊔ V).toScheme) (α : F ⟶ L.obj E),
        ∃ (iW : PW.obj F ≅ A) (iV : PV.obj F ≅ B),
          PW.map α ≫ kW.hom.app E = iW.hom ≫ a ∧
          PV.map α ≫ kV.hom.app E = iV.hom ≫ b := by sorry

end AlgebraicGeometry.Scheme
