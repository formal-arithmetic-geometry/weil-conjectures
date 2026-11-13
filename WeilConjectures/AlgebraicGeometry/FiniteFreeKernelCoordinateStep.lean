/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.QuasiCoherentSubmoduleIdeal

/-!
# Removing one coordinate from a finite free kernel

## References

* Stacks Project, Tag 01XF
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
-- Elaborating the nested kernel universal property and image transports needs a larger budget.
/-- Removing the distinguished coordinate gives a short exact sequence of kernels
with a quasi-coherent ideal quotient. (Stacks, Tag 01XF.) -/
theorem finite_free_kernel_coordinate_step (X : Scheme.{u})
    {I : Type u} [Finite I]
    (p : SheafOfModules.free (R := X.ringCatSheaf) (Option I) ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    ∃ J : X.IdealSheafData, J.toModules.IsQuasicoherent ∧
      ∃ (a : kernel (SheafOfModules.freeMap (R := X.ringCatSheaf) some ≫ p) ⟶ kernel p)
        (b : kernel p ⟶ J.toModules) (w : a ≫ b = 0),
        (ShortComplex.mk a b w).ShortExact := by
  classical
  let inc := SheafOfModules.freeMap (R := X.ringCatSheaf) (some : I → Option I)
  let q := inc ≫ p
  let r : SheafOfModules.free (R := X.ringCatSheaf) (Option I) ⟶
      SheafOfModules.free I :=
    Sigma.desc (fun i ↦ match i with
      | none => 0
      | some j => SheafOfModules.ιFree j)
  let t : SheafOfModules.free (R := X.ringCatSheaf) (Option I) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
    Sigma.desc (fun i ↦ match i with
      | none => 𝟙 _
      | some _ => 0)
  let s := SheafOfModules.ιFree (R := X.ringCatSheaf) (none : Option I)
  have hir : inc ≫ r = 𝟙 _ := by
    apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I)
    intro i
    change SheafOfModules.ιFree i ≫ inc ≫ r = SheafOfModules.ιFree i ≫ 𝟙 _
    rw [← Category.assoc, SheafOfModules.ιFree_freeMap]
    simp [r, SheafOfModules.ιFree]
  have hit : inc ≫ t = 0 := by
    apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I)
    intro i
    change SheafOfModules.ιFree i ≫ inc ≫ t = SheafOfModules.ιFree i ≫ 0
    rw [← Category.assoc, SheafOfModules.ιFree_freeMap]
    simp [t, SheafOfModules.ιFree]
  have hsplit : r ≫ inc + t ≫ s = 𝟙 _ := by
    apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (Option I))
    intro i
    change SheafOfModules.ιFree i ≫ (r ≫ inc + t ≫ s) =
      SheafOfModules.ιFree i ≫ 𝟙 _
    rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
    cases i with
    | none => simp [r, t, s, SheafOfModules.ιFree]
    | some i =>
      simp only [r, t, SheafOfModules.ιFree, Sigma.ι_comp_desc, zero_comp, add_zero,
        Category.comp_id]
      exact SheafOfModules.ιFree_freeMap some i
  have : Mono inc := mono_of_mono_fac hir
  let a : kernel q ⟶ kernel p := kernel.map q p inc (𝟙 _) (by simp [q])
  let v := kernel.ι p ≫ t
  have ha : a ≫ kernel.ι p = kernel.ι q ≫ inc := by simp [a]
  have hav : a ≫ v = 0 := by
    dsimp [v]
    rw [← Category.assoc, ha, Category.assoc, hit, comp_zero]
  have : Mono a := by
    have : Mono (a ≫ kernel.ι p) := by rw [ha]; infer_instance
    exact mono_of_mono a (kernel.ι p)
  have hkernel : IsLimit (KernelFork.ofι a hav) := by
    apply KernelFork.IsLimit.ofι'
    intro T k hk
    have hrec : (k ≫ kernel.ι p ≫ r) ≫ inc = k ≫ kernel.ι p := by
      have h := congrArg (fun f ↦ (k ≫ kernel.ι p) ≫ f) hsplit
      have hkts : (k ≫ kernel.ι p) ≫ (t ≫ s) = 0 := by
        calc
          (k ≫ kernel.ι p) ≫ (t ≫ s) = (k ≫ v) ≫ s := by
            simp only [v, Category.assoc]
          _ = 0 := by rw [hk, zero_comp]
      simp only [Preadditive.comp_add, Category.comp_id, hkts, add_zero] at h
      simpa only [Category.assoc] using h
    have hkq : (k ≫ kernel.ι p ≫ r) ≫ q = 0 := by
      change (k ≫ kernel.ι p ≫ r) ≫ (inc ≫ p) = 0
      rw [← Category.assoc, hrec]
      simp
    refine ⟨kernel.lift q (k ≫ kernel.ι p ≫ r) hkq, ?_⟩
    apply (cancel_mono (kernel.ι p)).mp
    simp only [Category.assoc, ha, kernel.lift_ι_assoc]
    exact hrec
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : (SheafOfModules.free (R := X.ringCatSheaf) (Option I)).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_free (R := X.ringCatSheaf) (Option I)
  have hqc := Scheme.Modules.isQuasicoherent_kernel p
  have := Scheme.Modules.isQuasicoherent_cokernel v
  have := Scheme.Modules.isQuasicoherent_kernel (cokernel.π v)
  obtain ⟨J, hJ, ⟨e⟩⟩ := quasiCoherent_submodule_ideal X (Abelian.image.ι v)
  let b₀ := Abelian.factorThruImage v
  have hw₀ : a ≫ b₀ = 0 := by
    apply (cancel_mono (Abelian.image.ι v)).mp
    simp [b₀, Category.assoc, hav]
  have hbkernel : IsLimit (KernelFork.ofι a hw₀) :=
    isKernelOfComp (Abelian.image.ι v) v hkernel hw₀ (Abelian.image.fac v)
  have hs₀ : (ShortComplex.mk a b₀ hw₀).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ hbkernel }
  have hw : a ≫ (b₀ ≫ e.hom) = 0 := by simp [← Category.assoc, hw₀]
  refine ⟨J, hJ, a, b₀ ≫ e.hom, hw, ?_⟩
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := ShortComplex.mk a b₀ hw₀)
      (S₂ := ShortComplex.mk a (b₀ ≫ e.hom) hw) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp)) hs₀

end AlgebraicGeometry
