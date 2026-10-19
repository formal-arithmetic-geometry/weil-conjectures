/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.AmbientOpenGluingObject
import Sheaf.AlgebraicGeometry.OpenUnionHomGluing

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

set_option maxHeartbeats 1600000 in
-- Elaborating the derived restriction comparisons needs this larger budget.
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Glue derived objects and compatible maps on the union, using ambient relative
restriction. No perfectness or support is asserted.
Source: Stacks Project, Tag 08DG, Lemma cohomology-lemma-glue.
(blueprint: lem-sc-relative-open-gluing).

Proof: Apply exists_ambient_open_gluing_object to obtain G on X and local
isomorphisms jW, jV with their overlap transition equation. Compose them with
a and b. Expand functoriality on these composites, substitute the assumed
compatibility of a and b, and postcompose the transition equation with SV(b)
and sV(E). This gives compatible local maps between the fixed objects G and E.
Apply exists_open_union_hom to obtain alpha on Y = W union V. Set F = L(G),
iW = kW(G) followed by jW and iV = kV(G) followed by jV. Reassociating the
two restriction equations for alpha gives exactly the required equations.
No witnesses are chosen to define data elsewhere: this is an existential theorem.
The argument uses all derived complexes, with no boundedness, perfectness,
quasi-coherence, quasi-compactness or support assumptions. Empty opens and empty
Y are included by the two input theorems. -/
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
          PV.map α ≫ kV.hom.app E = iV.hom ≫ b := by
  dsimp only
  intro c E a b hab
  obtain ⟨G, jW, jV, ht⟩ := exists_ambient_open_gluing_object X W V A B c
  have hcompat :
      (schemeDerivedOpenRestrictionCompIso X
        (homOfLE inf_le_left : W ⊓ V ⟶ W)).inv.app G ≫
          (schemeOpenOverlapRestriction X
            (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory.map (jW.hom ≫ a) ≫
          (schemeDerivedOpenRestrictionCompIso X
            (homOfLE inf_le_left : W ⊓ V ⟶ W)).hom.app E =
      (schemeDerivedOpenRestrictionCompIso X
        (homOfLE inf_le_right : W ⊓ V ⟶ V)).inv.app G ≫
          (schemeOpenOverlapRestriction X
            (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory.map (jV.hom ≫ b) ≫
          (schemeDerivedOpenRestrictionCompIso X
            (homOfLE inf_le_right : W ⊓ V ⟶ V)).hom.app E := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hab]
    simpa only [Category.assoc] using congrArg
      (fun t ↦ t ≫
        (schemeOpenOverlapRestriction X
          (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory.map b ≫
        (schemeDerivedOpenRestrictionCompIso X
          (homOfLE inf_le_right : W ⊓ V ⟶ V)).hom.app E) ht
  obtain ⟨α, hW, hV⟩ := exists_open_union_hom X W V G E
    (jW.hom ≫ a) (jV.hom ≫ b) hcompat
  refine ⟨(schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory.obj G, α,
    (schemeDerivedOpenRestrictionCompIso X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).app G ≪≫ jW,
    (schemeDerivedOpenRestrictionCompIso X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).app G ≪≫ jV, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Iso.app_hom, Category.assoc] using hW
  · simpa only [Iso.trans_hom, Iso.app_hom, Category.assoc] using hV

end AlgebraicGeometry.Scheme
