/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Tangent vectors at a rational point

Let `ε : A →ₐ[k] k` be a `k`-point of a `k`-algebra `A`, with ideal `I = ker ε`. A tangent vector
at `ε` is a linear form on the cotangent space `I / I²`; it gives a point derivation `A → k`
at `ε`.

## Main definitions

- `AlgHom.cotangentDerivation`: the point derivation at `ε` of a linear form on `I / I²`.
-/

@[expose] public section

namespace AlgHom

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k)

theorem sub_algebraMap_mem_ker (a : A) : a - algebraMap k A (ε a) ∈ RingHom.ker ε := by
  simp [RingHom.mem_ker]

/-- The point derivation `a ↦ φ (a - ε a)` at the `k`-point `ε` attached to a linear form `φ` on
the cotangent space at `ε`. -/
noncomputable def cotangentDerivation (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) : A →ₗ[k] k where
  toFun a := φ ((RingHom.ker ε).toCotangent ⟨_, ε.sub_algebraMap_mem_ker a⟩)
  map_add' a b := by
    rw [← map_add, ← map_add]
    congr 2
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' c a := by
    rw [RingHom.id_apply, ← map_smul, ← LinearMap.map_smul_of_tower]
    congr 2
    ext
    simp [Algebra.smul_def, mul_sub]

variable {ε}

theorem cotangentDerivation_apply (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) (a : A) :
    ε.cotangentDerivation φ a =
      φ ((RingHom.ker ε).toCotangent ⟨_, ε.sub_algebraMap_mem_ker a⟩) :=
  rfl

theorem cotangentDerivation_of_mem (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) {a : A}
    (ha : a ∈ RingHom.ker ε) :
    ε.cotangentDerivation φ a = φ ((RingHom.ker ε).toCotangent ⟨a, ha⟩) := by
  rw [cotangentDerivation_apply]
  congr 2
  ext
  simp [RingHom.mem_ker.1 ha]

/-- The point derivation of a linear form on the cotangent space satisfies the Leibniz rule at
`ε`. -/
theorem cotangentDerivation_mul (φ : (RingHom.ker ε).Cotangent →ₗ[k] k) (a b : A) :
    ε.cotangentDerivation φ (a * b) =
      ε a * ε.cotangentDerivation φ b + ε b * ε.cotangentDerivation φ a := by
  have hmem := ε.sub_algebraMap_mem_ker
  have h : (RingHom.ker ε).toCotangent ⟨_, hmem (a * b)⟩ =
      ε a • (RingHom.ker ε).toCotangent ⟨_, hmem b⟩ +
        ε b • (RingHom.ker ε).toCotangent ⟨_, hmem a⟩ := by
    rw [← algebraMap_smul A (ε a), ← algebraMap_smul A (ε b), ← map_smul, ← map_smul, ← map_add,
      Ideal.toCotangent_eq]
    have h' : a * b - algebraMap k A (ε (a * b)) -
        (algebraMap k A (ε a) * (b - algebraMap k A (ε b)) +
          algebraMap k A (ε b) * (a - algebraMap k A (ε a))) =
        (a - algebraMap k A (ε a)) * (b - algebraMap k A (ε b)) := by
      simp only [map_mul]
      ring
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, h', pow_two]
    exact Ideal.mul_mem_mul (hmem a) (hmem b)
  simp only [cotangentDerivation_apply, h, map_add, map_smul, smul_eq_mul]

end AlgHom
