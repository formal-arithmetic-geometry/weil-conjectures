/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFreeProjective
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkClosedPushforwardHomology

/-! # Bounded projective models of closed-pushforward stalks

## References

* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Taking stalks of a local strictly perfect model gives a bounded complex of projectives
with the homology of the restricted source stalk in degree zero. -/
theorem strictPerfectClosedPushforward_stalkModel
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (x : Z) (U : Y.Opens) (hx : i x ∈ U)
    (K : CochainComplex
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hK : Y.IsStrictlyPerfect U K)
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings Y.toRingedSpace) U).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) ≅
      DerivedCategory.Q.obj K) :
    ∃ L : CochainComplex (ModuleCat.{u} (Y.presheaf.stalk (i x))) ℤ,
      (∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (L.X j)) ∧
      (∀ j : ℤ, Projective (L.X j)) ∧
      Nonempty (L.homology 0 ≅
        ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
          (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))) ∧
      (∀ j : ℤ, j ≠ 0 → IsZero (L.homology j)) := by
  let S := openModuleStalkFunctor Y U ⟨i x, hx⟩
  let L := (S.mapHomologicalComplex (.up ℤ)).obj K
  obtain ⟨hzero, hother⟩ := openModuleStalk_closedPushforward_homology i x U hx K e
  refine ⟨L, ?_, ?_, hzero, hother⟩
  · obtain ⟨a, b, hab⟩ := hK.1
    exact ⟨a, b, fun j hj ↦ S.map_isZero (hab j hj)⟩
  · intro j
    obtain ⟨m, ι, π, hιπ⟩ := hK.2 j
    have : Projective (S.obj (SheafOfModules.free
        (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin m)))) :=
      openModuleStalk_free_projective Y U ⟨i x, hx⟩ m
    exact (show Retract (L.X j) (S.obj (SheafOfModules.free
      (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin m)))) from
        ⟨S.map ι, S.map π, by
          change S.map ι ≫ S.map π = 𝟙 (S.obj (K.X j))
          rw [← S.map_comp, hιπ, S.map_id]⟩).projective

end AlgebraicGeometry
