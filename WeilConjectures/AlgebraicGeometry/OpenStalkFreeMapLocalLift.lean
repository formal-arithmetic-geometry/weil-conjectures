/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison
import WeilConjectures.AlgebraicGeometry.OpenStalkFreeMapOneLift
import WeilConjectures.AlgebraicGeometry.OpenStalkRestrictionTransport

/-! # Local lifting from a finite free open-site stalk

## References

* [Stacks, Tag 01CP]
* [Stacks, Sheaves, Tag 00A0]
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

private theorem restriction_lift_stalk
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {R : A ⥤ B} {Q : B ⥤ C} {P : A ⥤ C} {S : C ⥤ D} {T : B ⥤ D} {H : A ⥤ D}
    (c : R ⋙ Q ≅ P) (d : Q ⋙ S ≅ T) (a : R ⋙ T ≅ H) (e : P ⋙ S ≅ H)
    (hc : ∀ M, S.map (c.hom.app M) ≫ e.hom.app M = d.hom.app (R.obj M) ≫ a.hom.app M)
    {F N : A} (t : H.obj F ⟶ H.obj N) (k : R.obj F ⟶ R.obj N)
    (hk : T.map k = a.hom.app F ≫ t ≫ a.inv.app N) :
    S.map (c.inv.app F ≫ Q.map k ≫ c.hom.app N) =
      e.hom.app F ≫ t ≫ e.inv.app N := by
  apply (cancel_mono (e.hom.app N)).1
  simp only [Category.assoc, e.inv_hom_id_app, Category.comp_id, Functor.map_comp]
  rw [hc N]
  have hd : S.map (Q.map k) ≫ d.hom.app (R.obj N) =
      d.hom.app (R.obj F) ≫ T.map k := d.hom.naturality k
  rw [← Category.assoc (S.map (Q.map k)), hd]
  simp only [Category.assoc]
  rw [hk]
  simp only [Category.assoc, a.inv_hom_id_app, Category.comp_id]
  rw [← Category.assoc (d.hom.app _), ← hc F]
  simp only [← Category.assoc, ← S.map_comp, c.inv_hom_id_app, S.map_id,
    Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One map from a finite free stalk lifts on every sufficiently small neighbourhood,
in the coordinates of the canonical comparisons `openModuleStalkRestrictionComparison`
(Stacks, Tag 01CP). -/
theorem exists_open_stalk_free_map_local_lifts
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) :
    ∀ (m : ℕ) (N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (t : (openModuleStalkFunctor X U ⟨x, hxU⟩).obj
        (SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ⟶
        (openModuleStalkFunctor X U ⟨x, hxU⟩).obj N),
      ∃ (V : X.Opens) (_hxV : x ∈ V) (_hVU : V ≤ U),
        ∀ (W : X.Opens) (hxW : x ∈ W) (_hWV : W ≤ V) (hWU : W ≤ U),
          let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE hWU)
          ∃ g : R.obj (SheafOfModules.free
              (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ⟶
              R.obj N,
            (openModuleStalkFunctor X W ⟨x, hxW⟩).map g =
              (openModuleStalkRestrictionComparison X U W hWU x hxU hxW).hom.app _ ≫ t ≫
                (openModuleStalkRestrictionComparison X U W hWU x hxU hxW).inv.app N := by
  classical
  have he := exists_openStalk_restriction_transport X U x hxU
  intro m N t
  let F := SheafOfModules.free
    (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))
  obtain ⟨V, hxV, hVU, a, k, hk⟩ := exists_open_stalk_free_map_one_lift
    X U x hxU m N t
  refine ⟨V, hxV, hVU, ?_⟩
  intro W hxW hWV hWU
  obtain ⟨c, d, -, hc⟩ := he V hxV hVU a W hxW hWV hWU
  let Q := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWV)
  let g := c.inv.app F ≫ Q.map k ≫ c.hom.app N
  refine ⟨g, ?_⟩
  exact restriction_lift_stalk c d a
    (openModuleStalkRestrictionComparison X U W hWU x hxU hxW) hc t k hk

end
end AlgebraicGeometry.Scheme
