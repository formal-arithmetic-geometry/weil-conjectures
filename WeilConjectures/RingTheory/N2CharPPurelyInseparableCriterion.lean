/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Algebra.CharP.Basic
import WeilConjectures.FieldTheory.NormalExtensionFixedField
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# In characteristic p, N-2 is tested on finite purely inseparable extensions

In positive characteristic, a Noetherian domain is N-2 if its integral closure is finite in every
finite purely inseparable extension of its fraction field.

## Implementation details

A finite extension `L/K` is contained in a finite normal extension `M/K`, which splits as a
purely inseparable extension `M_insep/K` followed by a separable extension `M/M_insep`. The
integral closure `R'` of `R` in `M_insep` is finite by hypothesis, hence a Noetherian normal
domain, so its integral closure in the separable extension `M` is finite over `R'`. The
integral closure of `R` in `M`, and hence in `L`, embeds into it and is finite by
Noetherianity.

## Main statements

* `isN2_of_finite_purelyInseparable_integralClosure`: in positive characteristic,
  finiteness of integral closures in finite purely inseparable extensions implies N-2.

## References

* [Stacks, Tag 032N]
-/

@[expose] public section

universe u v

/-- In positive characteristic, a Noetherian domain is N-2 if its integral closure is
finite over it in every finite purely inseparable extension of its fraction field. -/
theorem isN2_of_finite_purelyInseparable_integralClosure
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (h : ∀ (L : Type v) [Field L] [Algebra K L] [Algebra R L]
      [IsScalarTower R K L] [FiniteDimensional K L] [IsPurelyInseparable K L],
      Module.Finite R (integralClosure R L)) :
    IsN2 R K := by
  classical
  intro L _ _ _ _ _
  let M : Type v := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let : Algebra R M := ((algebraMap K M).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K M := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq' (by
    ext r
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply K L M])
  let S : Type v := IntermediateField.fixedField (⊤ : Subgroup (M ≃ₐ[K] M))
  obtain ⟨hpi, hsep, _⟩ := Normal.fixedField_purelyInseparable_and_galois K M
  have : IsPurelyInseparable K S := hpi
  have : Algebra.IsSeparable S M := hsep
  let : Algebra R S := ((algebraMap K S).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K S := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_eq' (by
    ext r
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    rfl)
  let A : Type v := integralClosure R S
  have : Module.Finite R A := h S
  have : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  have : IsIntegrallyClosed A := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : IsFractionRing A S := integralClosure.isFractionRing_of_finite_extension K S
  let : Algebra A M := ((algebraMap S M).comp (integralClosure R S).val.toRingHom).toAlgebra
  have : IsScalarTower A S M := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R A M := IsScalarTower.of_algebraMap_eq' (by
    ext r
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    rfl)
  -- Explicit scalar structures avoid searching for a nonexistent S-action on the closure.
  let algC : Algebra A (integralClosure A M) := (integralClosure A M).algebra
  let : SMul A (integralClosure A M) := algC.toSMul
  let : Module A (integralClosure A M) := Algebra.toModule
  have : IsScalarTower A (integralClosure A M) M :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite A (integralClosure A M) :=
    IsIntegralClosure.finite A S M (integralClosure A M)
  let algRC : Algebra R (integralClosure A M) := (integralClosure A M).algebra'
  let : SMul R (integralClosure A M) := algRC.toSMul
  let : Module R (integralClosure A M) := Algebra.toModule
  have : IsScalarTower R A (integralClosure A M) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite R (integralClosure A M) := Module.Finite.trans A _
  let f : integralClosure R M →ₗ[R] integralClosure A M :=
    { toFun := fun x ↦ ⟨x.val, x.property.tower_top⟩
      map_add' := fun x y ↦ Subtype.ext rfl
      map_smul' := fun r x ↦ Subtype.ext (by simp [Algebra.smul_def]) }
  have : Module.Finite R (integralClosure R M) :=
    Module.Finite.of_injective f (fun x y hxy ↦
      Subtype.ext (congrArg (fun z : integralClosure A M ↦ (z : M)) hxy))
  let g := (IsScalarTower.toAlgHom R L M).mapIntegralClosure.toLinearMap
  exact Module.Finite.of_injective g (fun x y hxy ↦
    Subtype.ext ((algebraMap L M).injective (congrArg Subtype.val hxy)))
