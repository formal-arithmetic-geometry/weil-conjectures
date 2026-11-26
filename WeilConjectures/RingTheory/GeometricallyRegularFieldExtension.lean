/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import WeilConjectures.FieldTheory.MakeSeparable
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import WeilConjectures.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import WeilConjectures.RingTheory.RegularRingFaithfullyFlatDescent
import WeilConjectures.RingTheory.RegularRingSmoothAscent

/-!
# Geometric regularity under finitely generated field extensions

A geometrically regular Noetherian algebra over `k` remains Noetherian and regular after
base change to any finitely generated field extension of `k`.

## Implementation details

Embed `K` in `K'` with `k'/k` and `K'/K` finite purely inseparable and `K'/k'` separable.
Then `K'` is the fraction field of a smooth `k'`-subalgebra `B`, so `K' ⊗[k] A` is a
localization of `(k' ⊗[k] A) ⊗[k'] B`, which is regular by smooth ascent. Regularity then
descends along the faithfully flat map `K ⊗[k] A → K' ⊗[k] A`.

## References

* [Stacks, Tag 0381]
* [Stacks, Tag 030R]
* [Stacks, Tag 037X]
* [Stacks, Tag 00T4]
* [Stacks, Tag 07NF]
* [Stacks, Tag 07NG]
-/

@[expose] public section

universe u v w

namespace Algebra

/-- A geometrically regular Noetherian algebra remains Noetherian and regular after any
finitely generated field extension. Finite generation is as a field, not as an algebra. -/
theorem isRegularRing_tensorProduct_of_isGeometricallyRegular
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (hA : IsGeometricallyRegular k A)
    (K : Type w) [Field K] [Algebra k K]
    (hK : (⊤ : IntermediateField k K).FG) : IsRegularRing (TensorProduct k K A) := by
  obtain ⟨k', K', hk', hK', akk', akK', ak'K', aKK', ht₁, ht₂,
    hf₁, hp₁, hf₂, hp₂, hsep⟩ :=
    exists_finite_purelyInseparable_separable_extension k K hK
  let := hk'
  let := hK'
  let := akk'
  let := akK'
  let := ak'K'
  let := aKK'
  have := ht₁
  have := ht₂
  have := hf₁
  have := hp₁
  have := hf₂
  have := hp₂
  have : EssFiniteType k K := IntermediateField.fg_top_iff.mp hK
  have : EssFiniteType k K' := EssFiniteType.comp k K K'
  have : EssFiniteType k' K' := EssFiniteType.of_comp k k' K'
  obtain ⟨B, hB, hfrac⟩ := FieldTheory.exists_smooth_subalgebra_fraction_field
    (IntermediateField.fg_top k' K') hsep
  have : Smooth k' B := hB
  have : IsFractionRing B K' := hfrac
  let C := TensorProduct k k' A
  have : IsRegularRing C := by
    have : Small.{max u v} k' := Module.Finite.small k k'
    have : IsPurelyInseparable k (Shrink.{max u v} k') :=
      (Shrink.algEquiv k k').symm.isPurelyInseparable
    have : IsRegularRing (TensorProduct k (Shrink.{max u v} k') A) :=
      hA.2 (Shrink.{max u v} k')
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.congr (Shrink.algEquiv k k')
        (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv
  let D := TensorProduct k' C B
  have : IsRegularRing D := isRegularRing_of_smooth C D
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let F := TensorProduct B D K'
  have : IsLocalization (Algebra.algebraMapSubmonoid D (nonZeroDivisors B)) F :=
    IsLocalization.tensor (S := D) (A := K') (nonZeroDivisors B)
  have : IsRegularRing F := by
    let M := Algebra.algebraMapSubmonoid D (nonZeroDivisors B)
    apply RingTheory.isRegularRing_of_localization D F M (algebraMap D F)
    · exact IsLocalization.map_units F
    · intro y
      obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj M y
      obtain ⟨z, hz⟩ := IsLocalization.map_units F s
      refine ⟨r, s, ↑z⁻¹, z⁻¹.isUnit, ?_, ?_⟩
      · rw [← hz]
        exact z.mul_inv
      · calc
          y = (y * algebraMap D F s) * ↑z⁻¹ := by rw [← hz]; simp
          _ = algebraMap D F r * ↑z⁻¹ := by rw [hy]
    · intro r hr
      exact (IsLocalization.map_eq_zero_iff M F r).mp hr
  have : IsRegularRing (TensorProduct k K' A) := by
    let e := (Algebra.TensorProduct.comm B D K').toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : K' ≃ₐ[K'] K')
        (Algebra.TensorProduct.commRight k' B C).symm).toRingEquiv.trans
        ((Algebra.TensorProduct.cancelBaseChange k' B K' K' C).toRingEquiv.trans
          (Algebra.TensorProduct.cancelBaseChange k k' K' K' A).toRingEquiv))
    exact IsRegularRing.of_ringEquiv e
  let E := TensorProduct k K A
  have : IsRegularRing (TensorProduct K E K') := by
    exact IsRegularRing.of_ringEquiv
      ((Algebra.TensorProduct.comm K E K').trans
        (Algebra.TensorProduct.cancelBaseChange k K K K' A)).symm.toRingEquiv
  exact IsRegularRing.of_faithfullyFlat E (TensorProduct K E K')

end Algebra
