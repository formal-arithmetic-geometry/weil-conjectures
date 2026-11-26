/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteModuleComplete

/-!
# Complete local base change along a surjection and its closed fibre

Base change of a Noetherian complete local algebra `T` over `R` along a surjective local map
`R → A` is again complete local, with closed fibre identified with that of `T`.

## Implementation details

With `I = ker(R → A)`, the tensor product `T ⊗[R] A` is identified with `T/IT`, which is
Noetherian complete local since `IT ⊆ m_T`. Its closed fibre over `A` is `T/m_R T`, since a
surjective local map maps `m_R` onto `m_A`. No flatness, regularity or formal smoothness is
required.

## References

* [Stacks, Tag 07NR], final base change
* [Stacks, Tag 00DF]
* [Stacks, Tag 0325]
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- The structural part of complete local base change. -/
private theorem complete_local_baseChange_structure
    (R : Type w) (A : Type u) (T : Type w)
    [CommRing R] [CommRing A] [CommRing T]
    [IsLocalRing R] [IsLocalRing A] [IsLocalRing T]
    [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    [Algebra R A] [Algebra R T]
    [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap R T)]
    (hq : Function.Surjective (algebraMap R A)) :
    letI : Algebra A (T ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
    ∃ _hlocal : IsLocalRing (T ⊗[R] A),
      IsNoetherianRing (T ⊗[R] A) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (T ⊗[R] A)) (T ⊗[R] A) ∧
      IsLocalHom (algebraMap A (T ⊗[R] A)) ∧
      (IsLocalRing.maximalIdeal T).map (algebraMap T (T ⊗[R] A)) =
        IsLocalRing.maximalIdeal (T ⊗[R] A) := by
  let : Algebra A (T ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let I := RingHom.ker (algebraMap R A)
  have hI : I ≤ IsLocalRing.maximalIdeal R := by
    intro r hr
    rw [← IsLocalRing.maximalIdeal_comap (algebraMap R A)]
    change algebraMap R A r ∈ IsLocalRing.maximalIdeal A
    rw [show algebraMap R A r = 0 from hr]
    exact Ideal.zero_mem _
  have hproper : I.map (algebraMap R T) ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal T).ne_top
      ((Ideal.map_mono hI).trans (IsLocalRing.map_maximalIdeal_le (algebraMap R T)))
  let : Nontrivial (T ⧸ I.map (algebraMap R T)) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  let eA : (R ⧸ I) ≃ₐ[R] A :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R A) hq
  let eC := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) eA)
  let : Nontrivial (T ⊗[R] A) := eC.symm.toEquiv.nontrivial
  have hsurj : Function.Surjective (algebraMap T (T ⊗[R] A)) :=
    Algebra.TensorProduct.includeLeft_surjective T T hq
  let hlocal : IsLocalRing (T ⊗[R] A) :=
    IsLocalRing.of_surjective' (algebraMap T (T ⊗[R] A)) hsurj
  have hnoeth : IsNoetherianRing (T ⊗[R] A) :=
    isNoetherianRing_of_surjective T _ (algebraMap T (T ⊗[R] A)) hsurj
  have hmax := IsLocalRing.map_maximalIdeal_of_surjective
    (algebraMap T (T ⊗[R] A)) hsurj
  have : Module.Finite T (T ⊗[R] A) :=
    Module.Finite.of_surjective (Algebra.linearMap T (T ⊗[R] A)) hsurj
  have hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal (T ⊗[R] A))
      (T ⊗[R] A) := by
    rw [← hmax, IsAdicComplete.map_algebraMap_iff]
    exact finite_module_complete_over_complete_noetherian T _ _
  have hlocalT : IsLocalHom (algebraMap T (T ⊗[R] A)) :=
    IsLocalHom.of_surjective _ hsurj
  have hlocalA : IsLocalHom (algebraMap A (T ⊗[R] A)) := by
    constructor
    intro a hu
    obtain ⟨r, rfl⟩ := hq a
    apply (algebraMap R A).isUnit_map
    apply isUnit_of_map_unit (algebraMap R T)
    apply isUnit_of_map_unit (algebraMap T (T ⊗[R] A))
    convert hu using 1
    simp only [Algebra.TensorProduct.algebraMap_apply]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
  exact ⟨hlocal, hnoeth, hcomplete, hlocalA, hmax⟩

/-- The closed-fibre identification after the structural base-change theorem. -/
private theorem complete_local_baseChange_closedFiber_equiv
    (R : Type w) (A : Type u) (T : Type w) (E : Type v)
    [CommRing R] [CommRing A] [CommRing T] [CommRing E]
    [IsLocalRing R] [IsLocalRing A] [IsLocalRing T]
    [Algebra R A] [Algebra R T] [Algebra A E]
    [IsLocalHom (algebraMap R A)]
    (hq : Function.Surjective (algebraMap R A))
    (e : (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T)) ≃+* E)
    (he : ∀ r : R,
      e (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R T))
        (algebraMap R T r)) = algebraMap A E (algebraMap R A r)) :
    letI : Algebra A (T ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
    Nonempty (((T ⊗[R] A) ⧸
      (IsLocalRing.maximalIdeal A).map (algebraMap A (T ⊗[R] A))) ≃ₐ[A] E) := by
  let : Algebra A (T ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra R E := ((algebraMap A E).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A E := IsScalarTower.of_algebraMap_eq' rfl
  let K := (IsLocalRing.maximalIdeal R).map (algebraMap R T)
  let fT : T →+* E := e.toRingHom.comp (Ideal.Quotient.mk K)
  let f : T →ₐ[R] E := { fT with commutes' := he }
  let F₀ := Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R A E)
    (fun _ _ ↦ Commute.all _ _)
  let F : (T ⊗[R] A) →ₐ[A] E :=
    { __ := F₀.toRingHom, commutes' := by
        intro a
        change F₀ (1 ⊗ₜ[R] a) = algebraMap A E a
        simp [F₀] }
  have hsurjT : Function.Surjective (algebraMap T (T ⊗[R] A)) :=
    Algebra.TensorProduct.includeLeft_surjective T T hq
  have hcomp : F.toRingHom.comp (algebraMap T (T ⊗[R] A)) = fT := by
    ext t
    change F₀ (t ⊗ₜ[R] 1) = fT t
    simp [F₀, f]
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (e.symm y)
    refine ⟨algebraMap T (T ⊗[R] A) t, ?_⟩
    change (F.toRingHom.comp (algebraMap T (T ⊗[R] A))) t = y
    rw [hcomp]
    change e (Ideal.Quotient.mk K t) = y
    rw [ht, e.apply_symm_apply]
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A (T ⊗[R] A))
  have hker : RingHom.ker F.toRingHom = J := by
    rw [← Ideal.map_comap_of_surjective (algebraMap T (T ⊗[R] A)) hsurjT
      (RingHom.ker F.toRingHom), RingHom.comap_ker, hcomp]
    have hk : RingHom.ker fT = K := by
      dsimp [fT]
      rw [RingHom.ker_comp_of_injective _ e.injective, Ideal.mk_ker]
    rw [hk]
    dsimp [K, J]
    rw [Ideal.map_map, ← IsLocalRing.map_maximalIdeal_of_surjective
      (algebraMap R A) hq, Ideal.map_map]
    congr 1
    ext r
    change (algebraMap T (T ⊗[R] A)) (algebraMap R T r) =
      (algebraMap A (T ⊗[R] A)) (algebraMap R A r)
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
  exact ⟨(Ideal.quotientEquivAlgOfEq A hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)⟩

set_option linter.unusedVariables false in
/-- Base change of a complete local algebra along a surjective local map remains
complete local, and preserves an identified closed fibre compatibly with the new base. -/
theorem complete_local_baseChange_closedFiber
    (R : Type w) (A : Type u) (T : Type w) (E : Type v)
    [CommRing R] [CommRing A] [CommRing T] [CommRing E]
    [IsLocalRing R] [IsLocalRing A] [IsLocalRing T]
    [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    [Algebra R A] [Algebra R T] [Algebra A E]
    [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap R T)]
    (hq : Function.Surjective (algebraMap R A))
    (e : (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T)) ≃+* E)
    (he : ∀ r : R,
      e (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R T))
        (algebraMap R T r)) = algebraMap A E (algebraMap R A r)) :
    letI : Algebra A (T ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
    ∃ hlocal : IsLocalRing (T ⊗[R] A),
      IsNoetherianRing (T ⊗[R] A) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (T ⊗[R] A)) (T ⊗[R] A) ∧
      IsLocalHom (algebraMap A (T ⊗[R] A)) ∧
      (IsLocalRing.maximalIdeal T).map (algebraMap T (T ⊗[R] A)) =
        IsLocalRing.maximalIdeal (T ⊗[R] A) ∧
      Nonempty (((T ⊗[R] A) ⧸
        (IsLocalRing.maximalIdeal A).map (algebraMap A (T ⊗[R] A))) ≃ₐ[A] E) := by
  let : Algebra A (T ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨hlocal, hnoeth, hcomplete, hlocalhom, hmax⟩ :=
    complete_local_baseChange_structure R A T hq
  let : IsLocalRing (T ⊗[R] A) := hlocal
  let : IsNoetherianRing (T ⊗[R] A) := hnoeth
  let : IsAdicComplete (IsLocalRing.maximalIdeal (T ⊗[R] A))
      (T ⊗[R] A) := hcomplete
  let : IsLocalHom (algebraMap A (T ⊗[R] A)) := hlocalhom
  refine ⟨hlocal, hnoeth, hcomplete, hlocalhom, hmax, ?_⟩
  exact complete_local_baseChange_closedFiber_equiv R A T E hq e he

end Algebra
