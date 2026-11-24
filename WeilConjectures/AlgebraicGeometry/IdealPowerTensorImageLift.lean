/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelIdealIntersectionBound
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.IdealTensorMultiplicationKernelControl
import WeilConjectures.AlgebraicGeometry.IdealTensorRestrictedMultiplicationImage

/-!
# Lifting a higher ideal-product image into an ideal-power tensor product

## References

* Stacks Project, Tag 01YB
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- A sufficiently high ideal product lifts through tensor multiplication.
(Stacks, Tag 01YB) -/
theorem ideal_power_tensor_image_lift
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (H : X.Modules)
    (hH : RingedSpace.IsCoherent X.toRingedSpace H) (n : ℕ) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    ∃ (m : ℕ) (a : idealModuleProduct (I ^ (n + m)).toModulesι H ⟶
        (I ^ n).toModules ⊗ H),
      a ≫ ((I ^ n).toModulesι ▷ H ≫ (λ_ H).hom) =
        idealModuleProductι (I ^ (n + m)).toModulesι H := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have : H.IsQuasicoherent :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X H).mp hH |>.1
  let T := (I ^ n).toModules ⊗ H
  let μ : T ⟶ H := (I ^ n).toModulesι ▷ H ≫ (λ_ H).hom
  obtain ⟨hT, hK, hz⟩ := ideal_tensor_multiplication_kernel_control I H hH n
  obtain ⟨m, hm⟩ := coherent_kernel_ideal_intersection_bound I T H μ hT hK n
  let j := idealModuleProductι (idealSheafPower I.toModulesι m).2 T
  have hj : Mono j := by dsimp [j, idealModuleProductι]; infer_instance
  have hzero : idealModuleProductι (idealSheafPower I.toModulesι n).2 (Limits.kernel μ) = 0 :=
    hz.eq_zero_of_src _
  have hinj (W : X.Opens) : Function.Injective ((j ≫ μ).app W) := by
    have hji : Function.Injective (j.app W) :=
      (ModuleCat.mono_iff_injective _).mp
        ((SheafOfModules.evaluation X.ringCatSheaf (.op W)).map_mono j)
    have hkill (z : Γ(idealModuleProduct (idealSheafPower I.toModulesι m).2 T, W))
        (h : (j ≫ μ).app W z = 0) : z = 0 := by
      have hk : j.app W z ∈ Set.range ((Limits.kernel.ι μ).app W) := by
        apply (Set.ext_iff.mp (range_map_kernelι W μ) _).mpr
        exact h
      have hh := hm W ⟨⟨z, rfl⟩, hk⟩
      rw [hzero, Limits.zero_comp] at hh
      obtain ⟨w, hw⟩ := hh
      apply hji
      simpa using hw.symm
    intro x y hxy
    exact sub_eq_zero.mp (hkill (x - y) (by simp only [map_sub, hxy, sub_self]))
  have hf : Mono (j ≫ μ) := by
    constructor
    intro Z a b hab
    apply hom_ext
    intro W
    ext s
    apply hinj W
    exact congrArg (fun f ↦ f.app W s) hab
  obtain ⟨e, he⟩ := ideal_tensor_restricted_multiplication_image I H n m
  refine ⟨m, e.hom ≫ (Limits.imageMonoIsoSource (j ≫ μ)).hom ≫ j, ?_⟩
  calc
    (e.hom ≫ (Limits.imageMonoIsoSource (j ≫ μ)).hom ≫ j) ≫ μ =
        e.hom ≫ Limits.image.ι (j ≫ μ) := by
      simp only [Category.assoc, Limits.imageMonoIsoSource_hom_self]
    _ = idealModuleProductι (I ^ (n + m)).toModulesι H := he

end AlgebraicGeometry.Scheme.Modules
