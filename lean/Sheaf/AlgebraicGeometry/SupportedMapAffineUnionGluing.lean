/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AffinePerfectMapLift
import Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension
import Sheaf.AlgebraicGeometry.DerivedOpenGluing
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction

/-! # Supported perfect gluing on the union with an affine open

Source: Stacks Project, Tag 09IM, two-open construction before ambient extension.
(blueprint: lem-sc-supported-map-affine-union-gluing).
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
/-- The affine construction produces a perfect supported source on the union itself.
There is no ambient extension in this statement. The supplied natural comparison `c`
identifies iterated restriction through the union with direct restriction to `U`.
Source: Stacks Project, Tag 09IM, proof assuming a two-open cover, using Tags 08EK,
08EH, and 08DG.
(blueprint: lem-sc-supported-map-affine-union-gluing).

Proof: Restrict the source R to W. Intersect each strictly perfect neighbourhood
with W and transport its bounded finite-free retract model through Modules.overEquiv;
this proves perfectness on W. Exact restriction identifies the cohomology stalks,
so the source is supported on T intersect W. Restrict E to the union and its two
opens; exact restriction preserves quasi-coherent cohomology. Quasi-separatedness
makes W intersect V compact, since both W and V are compact opens. It also makes
V intersect the open complement of T compact. Thus the affine supported extension
lemma on V extends the source on W intersect V after adjoining its shift. Compose
its overlap identification with the first projection and the restricted beta.
Affine perfect map lifting supplies a tensor augmentation, invertible on the
overlap, with a lifted map to E restricted to V. Its perfect source remains
supported on T intersect V. Derived open gluing on Y = W union V combines this
map with the first-projection map on W. The resulting F is perfect at every point
of Y and its cohomology stalks vanish outside T, by the two local identifications.
Restrict the W identification to U; the biproduct and shift comparisons identify
it with R restricted to U plus its shift. For the canonical comparison k this gives
an isomorphism e0 and the required map identity with k. For an arbitrary c, let t = k.symm
followed by c, a natural
automorphism of direct restriction J. Postcompose e0 with the biproduct of t at R
and the shift of that same isomorphism. The first projection of this biproduct
is the old first projection followed by t at R. Naturality of t at beta then
changes the equation with k into the equation with c. This does not require c
to commute with shifts. No extension from Y to X occurs here.
If U, W, V or T is empty, the same construction applies with the zero restrictions;
if V is already contained in W the stabilized source on W supplies the gluing. -/
theorem exists_supported_map_affine_union_gluing
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (U W V : X.Opens) (hUW : U ≤ W) (hW : IsCompact (W : Set X))
    (hV : IsAffineOpen V) (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    [∀ O : (W ⊔ V).toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (W ⊔ V).toScheme.toRingedSpace).over O))]
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
    let Y := W ⊔ V
    let L := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Y ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Y))
        (D := SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace))
        (Modules.overEquiv Y)
    let H := Equivalence.inverse
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Y))
        (D := SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace))
        (Modules.overEquiv Y) ⋙
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (le_trans hUW le_sup_left)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
    let J := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
    ∀ c : L.mapDerivedCategory ⋙ H.mapDerivedCategory ≅ J.mapDerivedCategory,
    ∃ (F : schemeDerivedCategory Y.toScheme) (α : F ⟶ L.mapDerivedCategory.obj E.obj),
      IsPerfect Y.toScheme F ∧
      (∀ (i : ℤ) (x : Y.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace)) i).obj F).val.presheaf x))) ∧
      ∃ e : H.mapDerivedCategory.obj F ≅
          J.mapDerivedCategory.obj R ⊞ (J.mapDerivedCategory.obj R)⟦(1 : ℤ)⟧,
        H.mapDerivedCategory.map α ≫ c.hom.app E.obj =
          e.hom ≫ biprod.fst ≫ J.mapDerivedCategory.map β := by sorry

end AlgebraicGeometry.Scheme
