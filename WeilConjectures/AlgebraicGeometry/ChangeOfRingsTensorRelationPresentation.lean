/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMaps
import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorBalancingUniversal

/-! # Change of rings as a tensor relation cokernel

## References

* Stacks Project, Tags 01SB and 0089
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

set_option maxHeartbeats 800000 in
-- The nested tensor and restriction-of-scalars types need extra elaboration heartbeats.
/-- The tensor relation presentation, without any quasi-coherence hypotheses.
(Stacks, Tags 01SB and 0089). -/
theorem changeOfRings_tensor_relation_presentation (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let S := tensorObj C.toModule P₀
    ∃ (δ : tensorObj B.toModule S ⟶ S)
      (e : (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
        (SheafOfModules.changeOfRings.{u, u, u} φ.right P) ≅ cokernel δ),
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        δ.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀) c (b • p) -
            tmulSection (M := C.toModule) (N := P₀) (φ.right.hom.app (op W) b * c) p) ∧
      (∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        e.hom.val.app (op W)
          ((((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W))
              (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p)) =
          (cokernel.π δ).app W (tmulSection (M := C.toModule) (N := P₀) c p)) := by
  classical
  dsimp only
  let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
  let S := tensorObj C.toModule P₀
  let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
    (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
  obtain ⟨a, d, g, ha, hd, hg, hag⟩ :=
    exists_changeOfRings_tensor_action_maps Y B C φ P
  have hu := changeOfRings_tensor_balancing_universal Y B C φ P a d g ha hd hg
  let δ : tensorObj B.toModule S ⟶ S := a - d
  have hδg : δ ≫ g = 0 := by
    rw [Preadditive.sub_comp, hag, sub_self]
  let q := cokernel.π δ
  have hq : a ≫ q = d ≫ q := by
    apply sub_eq_zero.mp
    rw [← Preadditive.sub_comp]
    exact cokernel.condition δ
  obtain ⟨h, hh, huniq⟩ := hu (cokernel δ) q hq
  let k : cokernel δ ⟶ T := cokernel.desc δ g hδg
  have hqk : q ≫ k = g := cokernel.π_desc δ g hδg
  have hhk : h ≫ k = 𝟙 T := by
    obtain ⟨t, ht, htuniq⟩ := hu T g hag
    apply (htuniq (h ≫ k) ?_).trans (htuniq (𝟙 T) ?_).symm
    · rw [← Category.assoc, hh, hqk]
    · exact Category.comp_id g
  have hkh : k ≫ h = 𝟙 (cokernel δ) := by
    apply (cancel_epi q).mp
    rw [← Category.assoc, hqk, hh, Category.comp_id]
  let e : T ≅ cokernel δ :=
    { hom := h
      inv := k
      hom_inv_id := hhk
      inv_hom_id := hkh }
  refine ⟨δ, e, ?_, ?_⟩
  · intro W b c p
    change (a - d).app W _ = _
    rw [Hom.sub_app]
    change a.app W _ - d.app W _ = _
    rw [ha W b c p, hd W b c p]
  · intro W c p
    change h.val.app (op W) _ = _
    rw [← hg W c p]
    exact congrArg (fun f : S ⟶ cokernel δ ↦
      f.app W (tmulSection (M := C.toModule) (N := P₀) c p)) hh

end AlgebraicGeometry.Scheme.Modules
