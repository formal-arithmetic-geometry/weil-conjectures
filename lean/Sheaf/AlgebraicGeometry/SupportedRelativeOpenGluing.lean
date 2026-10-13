/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.DerivedOpenGluing
import Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction

/-! # Supported gluing relative to an ambient scheme

Source: Stacks Project, Tag 08DG; Tag 08CM for local perfectness.
(blueprint: lem-sc-supported-relative-open-gluing).
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
/-- Glue arbitrary supported perfect local objects and compatible maps on W union V.
Neither affineness nor a stabilization of either source is assumed.
Source: Stacks Project, Tags 08DG and 08CM, used in Tag 09IM.
(blueprint: lem-sc-supported-relative-open-gluing).

Proof: Set Y=W union V and pull W and V back to opens of Y. They cover Y and are
canonically isomorphic as open subschemes to W and V. Transport A and B through these
isomorphisms and the exact module over-equivalences. The corresponding equivalence on the
intersection transports c. The natural composition comparisons for restriction identify
the given compatibility equation with the hypothesis of derived_open_gluing on Y for
the target E restricted to Y. That theorem supplies F, its two restriction isomorphisms,
and a map alpha with the required equations. Transport those equations back to the
relative functors PW and PV; the composition comparison kW (respectively kV) identifies
iterated restriction of E with its direct restriction to W (respectively V).
For a point of Y choose W or V containing it. A strictly perfect neighbourhood model
of A or B, restricted and transported to the corresponding open of Y, is a model of F.
This gives IsPerfect Y F. Exact restriction identifies each homology stalk of F with
the corresponding stalk of A or B. Off T that stalk is zero by hAT or hBT, so F is
supported on T intersect Y. No compactness, closedness of T, or boundedness of E is used.
If a member of the cover is empty, choose the other at each point; if Y is empty,
the perfectness and support conclusions are vacuous. -/
theorem exists_supported_relative_open_gluing
    (X : Scheme.{u}) (W V : X.Opens) (T : Set X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ O : W.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [∀ O : V.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    [∀ O : (W ⊔ V).toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (W ⊔ V).toScheme.toRingedSpace).over O))]
    (A : schemeDerivedCategory W.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : IsPerfect W.toScheme A) (hB : IsPerfect V.toScheme B)
    (hAT : ∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj A).val.presheaf x)))
    (hBT : ∀ (i : ℤ) (x : V.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) i).obj B).val.presheaf x))) :
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
        IsPerfect (W ⊔ V).toScheme F ∧
        (∀ (i : ℤ) (x : (W ⊔ V).toScheme), x.val ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace)) i).obj F).val.presheaf
              x))) ∧
        ∃ (iW : PW.obj F ≅ A) (iV : PV.obj F ≅ B),
          PW.map α ≫ kW.hom.app E = iW.hom ≫ a ∧
          PV.map α ≫ kV.hom.app E = iV.hom ≫ b := by sorry

end AlgebraicGeometry.Scheme
