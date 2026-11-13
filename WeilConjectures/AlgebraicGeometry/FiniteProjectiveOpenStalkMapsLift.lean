/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.OpenStalkFreeMapLocalLift
/-! # Finite-interval lifting for finite-projective open-site terms

## References

* Stacks Project, Tags 09RE and 01CP.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section
/-- Simultaneously lift a finite family of stalk maps with finite-projective sources.
(Stacks, Tag 01CP, Tag 09RE, Tag 0BC7) -/
theorem exists_finite_projective_open_stalk_maps_lift
    (X : Scheme.{u}) (V : X.Opens) (x : X) (hxV : x ∈ V)
    (T : X.Opens) (hTV : T ≤ V) (hxT : x ∈ T)
    (I : Type u) [Finite I]
    (M N : I → SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (hM : ∀ q, ∃ m : ℕ,
      ∃ (ι : M q ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)) ⟶ M q),
        ι ≫ π = 𝟙 (M q))
    (h : ∀ q, (openModuleStalkFunctor X V ⟨x, hxV⟩).obj (M q) ⟶
      (openModuleStalkFunctor X V ⟨x, hxV⟩).obj (N q)) :
    ∃ (Z : X.Opens) (hZT : Z ≤ T) (hxZ : x ∈ Z),
      let R := SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (hZT.trans hTV))
      let S := openModuleStalkFunctor X Z ⟨x, hxZ⟩
      let F := openModuleStalkFunctor X V ⟨x, hxV⟩
      ∃ (e : R ⋙ S ≅ F) (k : ∀ q, R.obj (M q) ⟶ R.obj (N q)),
        ∀ q, S.map (k q) = (e.app (M q)).hom ≫ h q ≫ (e.app (N q)).inv := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let F := openModuleStalkFunctor X V ⟨x, hxV⟩
  choose m ι π hsplit using hM
  have he := exists_open_stalk_free_map_local_lifts X V x hxV
  let e := fun (W : X.Opens) (hxW : x ∈ W) (hWV : W ≤ V) ↦
    openModuleStalkRestrictionComparison X V W hWV x hxV hxW
  choose D hxD hDV g hg using fun q ↦ he (m q) (N q) (F.map (π q) ≫ h q)
  let Z : X.Opens := T ⊓ ⨅ q, D q
  have hZT : Z ≤ T := inf_le_left
  have hZD (q : I) : Z ≤ D q := inf_le_right.trans (iInf_le D q)
  have hxZ : x ∈ Z := by
    refine ⟨hxT, ?_⟩
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxD
  let R := SheafOfModules.overMap (moduleRings X.toRingedSpace)
    (homOfLE (hZT.trans hTV))
  let S := openModuleStalkFunctor X Z ⟨x, hxZ⟩
  let E : R ⋙ S ≅ F := e Z hxZ (hZT.trans hTV)
  let k (q : I) : R.obj (M q) ⟶ R.obj (N q) :=
    R.map (ι q) ≫ g q Z hxZ (hZD q) (hZT.trans hTV)
  refine ⟨Z, hZT, hxZ, E, k, ?_⟩
  intro q
  change S.map (R.map (ι q) ≫ g q Z hxZ (hZD q) (hZT.trans hTV)) = _
  rw [S.map_comp, hg q Z hxZ (hZD q) (hZT.trans hTV)]
  change S.map (R.map (ι q)) ≫
    (E.hom.app _ ≫ (F.map (π q) ≫ h q) ≫ E.inv.app (N q)) = _
  have hn := E.hom.naturality (ι q)
  change S.map (R.map (ι q)) ≫ E.hom.app _ = E.hom.app _ ≫ F.map (ι q) at hn
  calc
    _ = (S.map (R.map (ι q)) ≫ E.hom.app _) ≫
        F.map (π q) ≫ h q ≫ E.inv.app (N q) := by simp only [Category.assoc]
    _ = E.hom.app (M q) ≫ (F.map (ι q) ≫ F.map (π q)) ≫
        h q ≫ E.inv.app (N q) := by rw [hn]; simp only [Category.assoc]
    _ = E.hom.app (M q) ≫ h q ≫ E.inv.app (N q) := by
      rw [← F.map_comp, hsplit q, F.map_id, Category.id_comp]
end
end AlgebraicGeometry.Scheme
