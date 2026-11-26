/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.RingTheory.Finiteness.Small

/-!
# Geometric regularity under compatible field and ring isomorphisms

Geometric regularity is invariant under compatible isomorphisms of the base field and of the
algebra.

## Implementation details

A finite purely inseparable extension `L` of `k'` becomes one of `k` through `σ`, and
`l ⊗ a ↦ l ⊗ e(a)` gives `L ⊗[k] A ≃+* L ⊗[k'] B`. If `L` lives in a larger universe than
the one tested by `IsGeometricallyRegular k A`, it is first replaced by `Shrink L`.

## References

* [Stacks, Tag 0382]
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- Geometric regularity is invariant under compatible field and ring isomorphisms. -/
theorem isGeometricallyRegular_of_fieldIso
    {k : Type u} {k' : Type v} {A : Type w} {B : Type z}
    [Field k] [Field k'] [CommRing A] [CommRing B] [Algebra k A] [Algebra k' B]
    (σ : k ≃+* k') (e : A ≃+* B)
    (hcompat : ∀ x : k, ∀ a : A, e (x • a) = σ x • e a)
    (hA : IsGeometricallyRegular k A) : IsGeometricallyRegular k' B := by
  let : Algebra k k' := σ.toRingHom.toAlgebra
  let : Algebra k B := ((algebraMap k' B).comp σ.toRingHom).toAlgebra
  have : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eA : A ≃ₐ[k] B :=
    { e with
      commutes' := fun x ↦ by
        change e (algebraMap k A x) = algebraMap k' B (σ x)
        simpa only [Algebra.smul_def, mul_one, map_one] using hcompat x 1 }
  have : IsNoetherianRing A := hA.1
  refine ⟨isNoetherianRing_of_ringEquiv A e, ?_⟩
  intro L _ _ _ _
  let : Algebra k L := ((algebraMap k' L).comp σ.toRingHom).toAlgebra
  have : IsScalarTower k k' L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite k k' :=
    Module.Finite.of_surjective (Algebra.linearMap k k') σ.surjective
  have : Module.Finite k L := Module.Finite.trans k' L
  have : IsPurelyInseparable k k' :=
    ⟨inferInstance, fun x _ ↦ σ.surjective x⟩
  have : IsPurelyInseparable k L := IsPurelyInseparable.trans k k' L
  have : Small.{max u w} L := Module.Finite.small k L
  have : IsPurelyInseparable k (Shrink.{max u w} L) :=
    (Shrink.algEquiv k L).symm.isPurelyInseparable
  have : IsRegularRing (TensorProduct k (Shrink.{max u w} L) A) :=
    hA.2 (Shrink.{max u w} L)
  have : IsRegularRing (TensorProduct k L A) :=
    IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.congr (Shrink.algEquiv k L)
        (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv
  have : TensorProduct.CompatibleSMul k k' L B := ⟨by
    intro x l b
    obtain ⟨x, rfl⟩ := σ.surjective x
    change (algebraMap k k' x • l) ⊗ₜ[k] b = l ⊗ₜ[k] (algebraMap k k' x • b)
    simp only [algebraMap_smul, TensorProduct.smul_tmul]⟩
  let e₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L) eA
  let e₂ := Algebra.TensorProduct.equivOfCompatibleSMul k k' k L B
  exact IsRegularRing.of_ringEquiv (e₁.trans e₂.symm).toRingEquiv

end Algebra
