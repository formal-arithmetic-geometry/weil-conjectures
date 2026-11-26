/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.FiniteCoefficientTensorKernelClosedFiber
import Mathlib.RingTheory.Smooth.Quotient

/-!
# Vanishing of the tensor-map kernel modulo the target maximal ideal

For local rings `A₀ → A → B` and `A₀ → C → B` with `A → B` flat, a surjective tensor map
`F : C ⊗[A₀] A → B` whose closed-fibre kernel on `C` is `m₀ C` has kernel `K` with `K = m_A K`.

## Implementation details

Tensoring the exact sequence `0 → K → D → B → 0` (with `D = C ⊗[A₀] A`) with `A / m_A` keeps
`K / m_A K → D / m_A D` injective by flatness of `B`. Residue surjectivity reduces every class
of `D / m_A D` to some `c ⊗ 1`, and the kernel equality shows that `D / m_A D → B / m_A B` is
injective; hence `K / m_A K = 0`. Finiteness, Noetherianity, completeness and formal smoothness
are not used.

## References

* [Stacks, Remark 07NS] (4)
* [Stacks, Tag 07NQ]
-/

@[expose] public section

universe u v w z

namespace RingHom

/-- Under the hypotheses of `finite_coefficient_tensor_kernel_reduction`, every element of the
kernel `K` of `C ⊗[A₀] A → B` vanishes in `K / m_A K`. -/
theorem finite_coefficient_tensor_kernel_reduction_quotient
    {A₀ : Type u} {A : Type v} {B : Type w} {C : Type z}
    [CommRing A₀] [CommRing A] [CommRing B] [CommRing C]
    [Algebra A₀ A] [Algebra A₀ C]
    [IsLocalRing A₀] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    (α : A₀ →+* A) (hα : algebraMap A₀ A = α) [IsLocalHom α]
    (hres : Function.Bijective (IsLocalRing.ResidueField.map α))
    (γ : A₀ →+* C) (hγ : algebraMap A₀ C = γ) [IsLocalHom γ]
    (φ : A →+* B) [IsLocalHom φ]
    (ψ : C →+* B) [IsLocalHom ψ] (hψγ : ψ.comp γ = φ.comp α)
    (F : TensorProduct A₀ C A →+* B)
    (hF : ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a)
    (hflat : RingHom.Flat φ) (hsurj : Function.Surjective F)
    (hker : RingHom.ker
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ)).comp ψ) =
      (IsLocalRing.maximalIdeal A₀).map γ) :
    ∀ x : TensorProduct A₀ C A, x ∈ RingHom.ker F →
    Submodule.mkQ (((IsLocalRing.maximalIdeal A).map
        (Algebra.TensorProduct.includeRight (R := A₀) (A := C)).toRingHom) •
        (RingHom.ker F : Submodule (TensorProduct A₀ C A) (TensorProduct A₀ C A))) x = 0 := by
  have _hcompat := hψγ
  let : Algebra A (TensorProduct A₀ C A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra A B := φ.toAlgebra
  have : Module.Flat A B := hflat
  let f : TensorProduct A₀ C A →ₗ[A] B :=
    { F.toAddMonoidHom with
      map_smul' := fun a x ↦ by
        change F ((1 ⊗ₜ[A₀] a) * x) = φ a * F x
        rw [map_mul, hF, map_one, one_mul] }
  have hclosed := finite_coefficient_tensor_kernel_closed_fiber α hα hres.2 γ hγ φ ψ
    F hF hker
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero _).2
  have hxI : x ∈ (IsLocalRing.maximalIdeal A) •
      (⊤ : Submodule A (TensorProduct A₀ C A)) := by
    rw [Ideal.smul_top_eq_map]
    exact hclosed hx
  have hxK : x ∈ f.ker := hx
  have hxIK : x ∈ (IsLocalRing.maximalIdeal A) • f.ker := by
    rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat _ f hsurj]
    exact ⟨hxK, hxI⟩
  change x ∈ (((IsLocalRing.maximalIdeal A).map
    (algebraMap A (TensorProduct A₀ C A))) •
      (RingHom.ker F : Submodule (TensorProduct A₀ C A) (TensorProduct A₀ C A))).restrictScalars A
  rw [Ideal.smul_restrictScalars]
  exact hxIK

/-- If `φ` is flat and `C ⊗[A₀] A → B` is surjective with the correct closed-fibre kernel, then
its kernel `K` satisfies `K ≤ m_A K`. -/
theorem finite_coefficient_tensor_kernel_reduction
    {A₀ : Type u} {A : Type v} {B : Type w} {C : Type z}
    [CommRing A₀] [CommRing A] [CommRing B] [CommRing C]
    [Algebra A₀ A] [Algebra A₀ C]
    [IsLocalRing A₀] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    (α : A₀ →+* A) (hα : algebraMap A₀ A = α) [IsLocalHom α]
    (hres : Function.Bijective (IsLocalRing.ResidueField.map α))
    (γ : A₀ →+* C) (hγ : algebraMap A₀ C = γ) [IsLocalHom γ]
    (φ : A →+* B) [IsLocalHom φ]
    (ψ : C →+* B) [IsLocalHom ψ] (hψγ : ψ.comp γ = φ.comp α)
    (F : TensorProduct A₀ C A →+* B)
    (hF : ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a)
    (hflat : RingHom.Flat φ) (hsurj : Function.Surjective F)
    (hker : RingHom.ker
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ)).comp ψ) =
      (IsLocalRing.maximalIdeal A₀).map γ) :
    (RingHom.ker F : Submodule (TensorProduct A₀ C A) (TensorProduct A₀ C A)) ≤
      ((IsLocalRing.maximalIdeal A).map
        (Algebra.TensorProduct.includeRight (R := A₀) (A := C)).toRingHom) •
      (RingHom.ker F : Submodule (TensorProduct A₀ C A) (TensorProduct A₀ C A)) := by
  intro x hx
  have hq := finite_coefficient_tensor_kernel_reduction_quotient α hα hres γ hγ φ ψ hψγ F hF
    hflat hsurj hker x hx
  exact (Submodule.Quotient.mk_eq_zero _).mp hq

end RingHom
