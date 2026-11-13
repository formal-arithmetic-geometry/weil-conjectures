/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapStageEquivalence

/-! # Pullback comparisons for nested open subschemes

## References

* Stacks Project, Tags 08DW and 0D5S.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory
namespace AlgebraicGeometry
attribute [local irreducible] perfectHomComposition

attribute [local instance] Functor.additive_of_preserves_binary_products


/-- The restricted maps form a square over the two nested open inclusions
(Stacks, Tag 08DW). -/
theorem perfectOverlapNestedRestrictedMaps
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W) :
    g.resLE W T hT ≫ Y.homOfLE (leOfHom iY) =
      X.homOfLE (leOfHom iX) ≫ g.resLE U P hP := by
  apply (cancel_mono U.ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]
  rw [← Category.assoc, Scheme.homOfLE_ι]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Compare pullback and exact restriction around the nested restricted square
(Stacks, Tags 08DW and 0D5S). -/
@[irreducible] noncomputable def perfectOverlapNestedPullbackSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W) :
    derivedPullback (g.resLE U P hP) ⋙
        (schemeOpenOverlapRestriction X iX).mapDerivedCategory ≅
      (schemeOpenOverlapRestriction Y iY).mapDerivedCategory ⋙
        derivedPullback (g.resLE W T hT) :=
  Functor.isoWhiskerLeft _ (overlapOpenInclusionPullbackIso X iX).symm ≪≫
    perfectHomComposition (X.homOfLE (leOfHom iX)) (g.resLE U P hP) ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k)
      (perfectOverlapNestedRestrictedMaps g iY iX hP hT).symm) ≪≫
    (perfectHomComposition (g.resLE W T hT) (Y.homOfLE (leOfHom iY))).symm ≪≫
    Functor.isoWhiskerRight (overlapOpenInclusionPullbackIso Y iY) _


end AlgebraicGeometry
