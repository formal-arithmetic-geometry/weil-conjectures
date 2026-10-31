/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Mathlib.Algebra.Module.Torsion
public import Mathlib.LinearAlgebra.TensorProduct.Basic

import Mathlib.RingTheory.Flat.Localization

/-!
# Affine torsion comparison for a Cartier-factor blow-up chart

Source: Stacks Project, Divisors, Tag 080H, proof of
`lemma-strict-transform-different-centers`, algebra reduction paragraph
(blueprint: lem-trf-strict-transform-affine-torsion-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open AlgebraicGeometry

namespace AlgebraicGeometry

/--
The proof is the affine calculation in Tag 080H, performed after localization.
Put `B = A[I/a]`, `L = A_a`, and `S = {a^n}`. The inclusion `i : B → L`
is a localization of modules at `S`: powers of `a` act invertibly on `L`,
every fraction has a numerator from `A` and hence from `B`, and injectivity
of the inclusion gives the equality criterion with denominator one.

Tensor-localization, after commuting the tensor factors, shows that
`f : M ⊗_A B → L ⊗_A M` is a localization at `S`. The target is also the
localization of `M`, through `m ↦ 1 ⊗ m`. The hypothesis `Γ_(x)(M) = 0`
implies that multiplication by `x` on `M` is injective. Mathlib's
`IsSMulRegular.of_isLocalizedModule` preserves this injectivity on `L ⊗_A M`.

If `(xa)^n z = 0`, then `x^n a^n f(z) = 0`. Injectivity of multiplication
by `a^n` and then by `x^n` gives `f(z) = 0`. The localization kernel criterion
therefore supplies `r` with `a^r z = 0`. Conversely `a^n z = 0` immediately
implies `(xa)^n z = x^n a^n z = 0`. Exponent zero causes no exception: its
witness forces `z = 0`. The argument uses only that `B` is an `A`-subalgebra
of `A_a`, so the hypotheses `ha` and `hx` need no further use.
Source: Stacks Project, Divisors, Tag 080H, proof of
`lemma-strict-transform-different-centers`, algebra reduction paragraph
(blueprint: lem-trf-strict-transform-affine-torsion-comparison).
-/
theorem strictTransform_affine_torsion_comparison
    {A : Type u} [CommRing A] (I : Ideal A) (a x : A) (ha : a ∈ I)
    (hx : x ∈ nonZeroDivisors A) (M : Type v) [AddCommGroup M] [Module A M]
    (hM : Submodule.powTorsion A M x = ⊥) :
    Submodule.powTorsion A (TensorProduct A M (AffineBlowup.chartRing I a)) a =
      Submodule.powTorsion A (TensorProduct A M (AffineBlowup.chartRing I a)) (x * a) := by
  have _ha := ha
  have _hx := hx
  let B := AffineBlowup.chartRing I a
  let L := Localization.Away a
  let S := Submonoid.powers a
  let i : B →ₗ[A] L := B.val.toLinearMap
  have hi : IsLocalizedModule S i :=
    { map_units := IsLocalizedModule.map_units (Algebra.linearMap A L)
      surj := fun z ↦ by
        obtain ⟨⟨c, s⟩, hs⟩ := IsLocalizedModule.surj S (Algebra.linearMap A L) z
        exact ⟨⟨algebraMap A B c, s⟩, by
          change s • z = B.val (algebraMap A B c)
          rw [B.val.commutes]
          exact hs⟩
      exists_of_eq := fun h ↦ ⟨1, by simpa using Subtype.ext h⟩ }
  let f : TensorProduct A M B →ₗ[A] TensorProduct A L M :=
    (i.rTensor M).comp (TensorProduct.comm A M B).toLinearMap
  have ht : IsLocalizedModule S (i.rTensor M) :=
    inferInstanceAs (IsLocalizedModule S (TensorProduct.AlgebraTensorModule.rTensor A M i))
  have hf : IsLocalizedModule S f :=
    IsLocalizedModule.of_linearEquiv_right S (i.rTensor M) (TensorProduct.comm A M B)
  have hreg : IsSMulRegular M x := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro m hm
    have hm' : m ∈ Submodule.powTorsion A M x :=
      Submodule.mem_powTorsion_iff.mpr ⟨1, by simpa using hm⟩
    simpa [hM] using hm'
  have hregL := hreg.of_isLocalizedModule L S (TensorProduct.mk A L M 1)
  have hreg' : IsSMulRegular (TensorProduct A L M) x := by
    simpa only [IsSMulRegular, algebraMap_smul] using hregL
  ext z
  simp only [Submodule.mem_powTorsion_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [mul_pow, mul_smul, hn, smul_zero]⟩
  · rintro ⟨n, hn⟩
    have hz : f z = 0 := by
      apply (hreg'.pow n).right_eq_zero_of_smul
      apply (IsLocalizedModule.smul_injective f (⟨a ^ n, n, rfl⟩ : S))
      simp only [Submonoid.smul_def, smul_zero, smul_comm (a ^ n), ← map_smul,
        ← mul_smul, ← mul_pow, hn, map_zero]
    obtain ⟨⟨s, r, rfl⟩, hs⟩ := (IsLocalizedModule.eq_zero_iff S f).mp hz
    exact ⟨r, hs⟩

end AlgebraicGeometry
