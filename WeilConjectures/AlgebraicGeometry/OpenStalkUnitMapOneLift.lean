/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.OpenStalkUnitMapOneLiftBridge
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkHomLift

/-! # One unit-source open-site stalk map lifts on one neighbourhood

## References

* [Stacks, Tag 01CP]
* [Stacks, Sheaves, Tag 00A0]
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A map from the stalk of the unit module lifts on one neighbourhood. -/
theorem exists_open_stalk_unit_map_one_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (t : (openModuleStalkFunctor X U ⟨x, hxU⟩).obj
      (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)) ⟶
      (openModuleStalkFunctor X U ⟨x, hxU⟩).obj N) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U),
      let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU)
      let S := openModuleStalkFunctor X V ⟨x, hxV⟩
      let F := SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)
      ∃ (a : R ⋙ S ≅ openModuleStalkFunctor X U ⟨x, hxU⟩)
        (k : R.obj F ⟶ R.obj N),
        S.map k = a.hom.app F ≫ t ≫ a.inv.app N := by
  let E := (Modules.overEquiv U).functor
  let F := SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)
  let D := ModuleCat.restrictScalars (U.ι.stalkMap ⟨x, hxU⟩).hom
  have : D.IsEquivalence := by
    change (ModuleCat.restrictScalars
      (RingEquiv.ofBijective (U.ι.stalkMap ⟨x, hxU⟩).hom
        (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap ⟨x, hxU⟩))).toRingHom).IsEquivalence
    infer_instance
  let q := D.preimage t
  have : (E.obj F).IsFiniteLocallyFree := by
    change (SheafOfModules.unit U.toScheme.ringCatSheaf).IsFiniteLocallyFree
    have : (SheafOfModules.unit U.toScheme.ringCatSheaf).IsInvertible :=
      SheafOfModules.instIsInvertibleUnit.{u, u, u}
    exact SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  obtain ⟨A, hxA, f, hf⟩ := Modules.exists_restrict_stalk_hom_lift
    (E.obj F) (E.obj N) ⟨x, hxU⟩ q
  obtain ⟨V, hxV, hVU, a, k, hk⟩ :=
    exists_open_stalk_hom_of_subscheme_lift X U x hxU F N q A hxA f hf
  refine ⟨V, hxV, hVU, a, k, ?_⟩
  change (openModuleStalkFunctor X V ⟨x, hxV⟩).map k =
    a.hom.app F ≫ D.map (D.preimage t) ≫ a.inv.app N at hk
  simpa only [Functor.map_preimage] using hk


end
end AlgebraicGeometry.Scheme
