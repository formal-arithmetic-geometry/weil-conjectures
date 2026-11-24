/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.BasisIffBasisQuotientOfNilpotent
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Lifting a residue basis to a power quotient of a flat algebra

Every fixed lift of a residue basis of a flat algebra over a local ring gives a basis modulo
each positive power of the maximal ideal.

## References

* Stacks Project, Tag 07QM(4), using Tags 00HI and 051F.
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Every fixed lift of a residue basis gives a basis modulo each positive power of the
maximal ideal. No Noetherianity or finiteness of the basis is required. -/
theorem flatAlgebra_power_basis
    (A : Type u) (C : Type v) [CommRing A] [IsLocalRing A]
    [CommRing C] [Algebra A C] [Module.Flat A C]
    {X : Type w}
    (b : Module.Basis X (A ⧸ IsLocalRing.maximalIdeal A)
      (C ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A C)))
    (x : X → C)
    (hx : ∀ i, Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) (x i) = b i)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ b' : Module.Basis X (A ⧸ (IsLocalRing.maximalIdeal A) ^ r)
      (C ⧸ ((IsLocalRing.maximalIdeal A) ^ r).map (algebraMap A C)),
      ∀ i, b' i = Ideal.Quotient.mk
        (((IsLocalRing.maximalIdeal A) ^ r).map (algebraMap A C)) (x i) := by
  classical
  let n := IsLocalRing.maximalIdeal A
  let I := n ^ r
  let R := A ⧸ I
  let M := C ⧸ I.map (algebraMap A C)
  let N := C ⧸ n.map (algebraMap A C)
  have hle : I ≤ n := Ideal.pow_le_self (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hr))
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hle
  have : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing R :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hm : IsLocalRing.maximalIdeal R = n.map (Ideal.Quotient.mk I) :=
    (IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).symm
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal R) := by
    refine ⟨r, ?_⟩
    rw [hm, ← Ideal.map_pow]
    exact Ideal.map_quotient_self I
  have : Module.Flat R M :=
    Module.Flat.of_linearEquiv (TensorProduct.quotIdealMapEquivQuotTensor C I).toLinearEquiv
  let k := A ⧸ n
  let m := IsLocalRing.maximalIdeal R
  let Q := m • (⊤ : Submodule R M)
  let ek : (R ⧸ m) ≃+* k :=
    (Ideal.quotEquivOfEq hm).trans (DoubleQuot.quotQuotEquivQuotOfLE hle)
  let : Algebra R N := Ideal.Quotient.algebraQuotientOfLEComap
    (hle.trans Ideal.le_comap_map)
  have : IsScalarTower A R N := IsScalarTower.of_algebraMap_eq fun a ↦ rfl
  let : Algebra (R ⧸ m) N := Algebra.compHom N ek.toRingHom
  have : IsScalarTower R (R ⧸ m) N := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  let f : M →ₗ[R] N :=
    (Ideal.Quotient.factorₐ A (Ideal.map_mono hle)).toLinearMap.extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective (I := I))
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective (Ideal.map_mono hle)
  have hker : Q = LinearMap.ker f := by
    dsimp only [Q, m]
    rw [Ideal.smul_top_eq_map, hm, Ideal.map_map]
    have hcomp : (algebraMap R M).comp (Ideal.Quotient.mk I) =
        (Ideal.Quotient.mk (I.map (algebraMap A C))).comp (algebraMap A C) := by
      ext a
      rfl
    rw [hcomp, ← Ideal.map_map,
      ← Ideal.Quotient.factor_ker (Ideal.map_mono hle)]
    rfl
  let eq : (M ⧸ Q) ≃ₗ[R ⧸ m] N :=
    ((Submodule.quotEquivOfEq _ _ hker).trans
      (f.quotKerEquivOfSurjective hf)).extendScalarsOfSurjective
        (Ideal.Quotient.mk_surjective (I := m))
  let bk : Module.Basis X (R ⧸ m) N := b.mapCoeffs ek.symm (by
    intro c z
    change ek (ek.symm c) • z = c • z
    rw [ek.apply_symm_apply])
  apply (Module.basis_iff_basisQuotient_of_nilpotent hnil
    (fun i ↦ Ideal.Quotient.mk (I.map (algebraMap A C)) (x i))).mp
  refine ⟨bk.map eq.symm, ?_⟩
  intro i
  apply eq.injective
  change eq (eq.symm (bk i)) =
    eq (Q.mkQ (Ideal.Quotient.mk (I.map (algebraMap A C)) (x i)))
  rw [eq.apply_symm_apply]
  rw [show bk i = b i from Module.Basis.mapCoeffs_apply _ _ _ _]
  change b i = f (Ideal.Quotient.mk (I.map (algebraMap A C)) (x i))
  exact (hx i).symm

end Algebra
