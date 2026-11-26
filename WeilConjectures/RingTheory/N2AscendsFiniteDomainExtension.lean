/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink

/-!
# N-2 ascends along a finite extension of Noetherian domains

If `A ⊆ B` is a finite extension of Noetherian domains and `A` is N-2, then `B` is N-2.

## Implementation details

The fraction field `E` of `B` is finite over the fraction field `K` of `A`, so every finite
extension of `E` is finite over `K`. The integral closure of `A` in it is finite over `A` by N-2,
and it equals the integral closure of `B` since `B` is integral over `A`; the same generators
show it is finite over `B`.

## References

* [Stacks, Tag 032I]
-/

@[expose] public section

universe uA uB uK uE

set_option autoImplicit false

/-- If `A ⊆ B` is a finite extension of Noetherian domains and `A` is N-2, then `B` is N-2.
-/
theorem isN2_of_finite_domain_extension (A : Type uA) (B : Type uB)
    (K : Type uK) (E : Type uE) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra B E] [IsFractionRing B E]
    (hAB : Function.Injective (algebraMap A B)) (hA : IsN2 A K) : IsN2 B E := by
  let : Algebra A E := (algebraMap B E).comp (algebraMap A B) |>.toAlgebra
  let : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hinj : Function.Injective (algebraMap A E) :=
    (IsFractionRing.injective B E).comp hAB
  let : Algebra K E := (IsFractionRing.lift hinj : K →+* E).toAlgebra
  let : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq fun a ↦
    (IsFractionRing.lift_algebraMap hinj a).symm
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hAB
  -- Localize the finite generators instead of first constructing their span as a field.
  have : FiniteDimensional K E := by
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := B)
    exact Module.finite_def.mpr <|
      (span_eq_top_localization_localization K (nonZeroDivisors A) E hs) ▸
        Submodule.fg_span (Set.toFinite _)
  intro M _ _ _ _ _
  let : Algebra K M := ((algebraMap E M).comp (algebraMap K E)).toAlgebra
  let : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra A M := ((algebraMap B M).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A K M := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap B M (algebraMap A B a) =
      algebraMap E M (IsFractionRing.lift hinj (algebraMap A K a))
    rw [IsFractionRing.lift_algebraMap hinj]
    exact IsScalarTower.algebraMap_apply B E M (algebraMap A B a)
  have : FiniteDimensional K M := Module.Finite.trans E M
  -- IsN2 tests fields in K's universe; finite-dimensionality lets us shrink M to it.
  have : Small.{uK} M := Module.Finite.small K M
  let : IsScalarTower A K (Shrink.{uK} M) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      apply (Shrink.algEquiv A M).injective
      rw [AlgEquiv.commutes]
      change algebraMap A M a =
        (Shrink.algEquiv K M) (algebraMap K (Shrink.{uK} M) (algebraMap A K a))
      rw [AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply A K M a
  have : Module.Finite A (integralClosure A (Shrink.{uK} M)) := hA (Shrink.{uK} M)
  have : Module.Finite A (integralClosure A M) :=
    Module.Finite.equiv (Shrink.algEquiv A M).mapIntegralClosure.toLinearEquiv
  let f : integralClosure A M →ₗ[A] integralClosure B M :=
    { toFun := fun x ↦ ⟨x.1, x.2.tower_top⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hf : Function.Surjective f := by
    intro x
    exact ⟨⟨x.1, isIntegral_trans x.1 x.2⟩, rfl⟩
  have : Module.Finite A (integralClosure B M) := Module.Finite.of_surjective f hf
  exact Module.Finite.of_restrictScalars_finite A B (integralClosure B M)
