/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AffinePerfectMapLift
import Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction

/-! # Supported affine overlap data

Source: Stacks Project, Tag 09IM, the construction on the affine member before gluing.
(blueprint: lem-sc-supported-affine-overlap-map).
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
/-- Construct the affine member and its compatible overlap map; no object on the union
is asserted. Source: Stacks Project, Tag 09IM, first two-open paragraph, Tags 08EK and 08EH.
(blueprint: lem-sc-supported-affine-overlap-map).

Proof: Restrict R to W and transport its strictly perfect neighbourhood models through
Modules.overEquiv, intersecting each neighbourhood with W. The stabilized restriction A
is perfect, since biproducts and shifts preserve bounded finite-free retract models.
Exact restriction and its stalk comparison show that A is supported on T intersect W.
The overlap W intersect V is compact by quasi-separatedness. On V the pullback of T is
closed, and its complement is compact: intersect the compact open V with the compact
open complement of T and transport through the open embedding. Apply the affine supported
extension theorem to R restricted to this overlap. Identify its restriction with A on the
overlap using the exact functors' biproduct and shift comparisons. Compose the inverse of
this identification with the restricted first-projection map a. Restriction of E to V
has quasi-coherent cohomology by the open restriction criterion. Apply affine perfect map
lifting to the overlap map: its augmented source B is perfect and supported on T intersect
V, and its augmentation is invertible on the overlap. Compose this inverse augmentation
with the previous identification to get c:A|overlap ≅ B|overlap. The lifting identity gives
the stated compatibility of a and b, with the canonical iterated restriction comparisons.
Empty W, V, the overlap, or T require no separate choices; the same zero restrictions and
supported affine extension and lifting theorems apply. -/
theorem exists_supported_affine_overlap_map
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W V : X.Opens) (hW : IsCompact (W : Set X)) (hV : IsAffineOpen V)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ O : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ O : W.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [∀ O : V.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory X)
    (R : schemeDerivedCategory X) (β : R ⟶ E.obj)
    (hR : (∀ x : X, x ∈ W → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
              DerivedCategory.Q.obj K)))
    (hRT : (∀ (i : ℤ) (x : X), x ∈ W → x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x)))) :
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    let A := JW.obj R ⊞ (JW.obj R)⟦(1 : ℤ)⟧
    let a : A ⟶ JW.obj E.obj := biprod.fst ≫ JW.map β
    IsPerfect W.toScheme A ∧
      (∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj A).val.presheaf x))) ∧
      ∃ (B : schemeDerivedCategory V.toScheme) (b : B ⟶ JV.obj E.obj)
        (c : SW.obj A ≅ SV.obj B),
        IsPerfect V.toScheme B ∧
        (∀ (i : ℤ) (x : V.toScheme), x.val ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) i).obj B).val.presheaf
              x))) ∧
        SW.map a ≫ kW.hom.app E.obj = c.hom ≫ SV.map b ≫ kV.hom.app E.obj := by sorry

end AlgebraicGeometry.Scheme
