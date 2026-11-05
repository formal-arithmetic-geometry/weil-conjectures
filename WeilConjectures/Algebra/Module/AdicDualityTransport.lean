/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology
public import WeilConjectures.Algebra.Module.RationalPerfectPairing

/-!
# Transport of finite-level duality to an extension of `ℚ_p`

This file proves the linear algebra of the transport of Poincaré duality from the finite
coefficient rings `ℤ/ℓᵐ` to `ℚ̄_ℓ` (blueprint `sk-thm-transport`,
`thm-pod-derived-poincare-duality`), in the following abstract form
(`LinearMap.exists_isPerfPair_of_finiteLevel`).

Let `A`, `B` be finitely generated `ℤ_p`-modules (the integral cohomology groups `Hⁱ(X, ℤ_ℓ)`,
`H^{2d-i}(X, ℤ_ℓ)`) with endomorphisms `F_A`, `F_B` (Frobenius), and let `V`, `W` be their
extensions of scalars to a field `K ⊇ ℤ_p` (e.g. `ℚ̄_ℓ`), with the induced endomorphisms. Suppose
that for every `m`:

* there are maps `ρ : A ⟶ Eₘ`, `σ : B ⟶ Fₘ` to modules (the cohomology groups with coefficients
  `ℤ/ℓᵐ`) whose kernels are `pᵐ A`, `pᵐ B` and whose images contain `pᵉ Eₘ`, `pᵉ Fₘ` for a fixed
  `e` (the Bockstein sequences, when `pᵉ` kills the torsion of the cohomology);
* there is a pairing `Qₘ : Eₘ × Fₘ ⟶ ℤ_p / pᵐ`, nondegenerate on both sides (finite-level
  Poincaré duality), whose restriction along `ρ`, `σ` is a `c`-similitude for `F_A`, `F_B`.

The finite-level pairings need not be compatible with each other. Then there is a perfect
`K`-bilinear pairing `V × W ⟶ K` which is a `c`-similitude for the induced endomorphisms. It is
obtained by compactness (`LinearMap.exists_isSimilitude_of_forall_level`) on the free quotients
of `A` and `B`, followed by extension of scalars (`LinearMap.isPerfPair_of_span_eq_top`).
-/

@[expose] public section

open Function

namespace LinearMap

variable {p : ℕ} [Fact p.Prime]

section Torsion

variable {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]

/-- Over `ℤ_p`, a torsion element is killed by a power of `p`. -/
lemma exists_pow_smul_eq_zero_of_mem_torsion {a : A} (ha : a ∈ Submodule.torsion ℤ_[p] A) :
    ∃ n : ℕ, (p : ℤ_[p]) ^ n • a = 0 := by
  obtain ⟨⟨r, hr⟩, hra⟩ := ha
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  refine ⟨r.valuation, ?_⟩
  have hr' : r • a = 0 := hra
  set u := PadicInt.unitCoeff hr0
  have hu : r = ↑u * (p : ℤ_[p]) ^ r.valuation := PadicInt.unitCoeff_spec hr0
  have h1 : ((↑u⁻¹ : ℤ_[p]) * r) • a = 0 := by
    rw [mul_smul, hr', smul_zero]
  rwa [hu, ← mul_assoc, Units.inv_mul, one_mul] at h1

end Torsion

section Descent

variable {A B M : Type*} [AddCommGroup A] [Module ℤ_[p] A] [AddCommGroup B] [Module ℤ_[p] B]
  [AddCommGroup M] [Module ℤ_[p] M]

end Descent

section Transport

variable {A B : Type*} [AddCommGroup A] [Module ℤ_[p] A] [Module.Finite ℤ_[p] A]
  [AddCommGroup B] [Module ℤ_[p] B] [Module.Finite ℤ_[p] B]
  (FA : A →ₗ[ℤ_[p]] A) (FB : B →ₗ[ℤ_[p]] B) (c : ℤ_[p]) (e : ℕ)
  {E F : ℕ → Type*} [∀ m, AddCommGroup (E m)] [∀ m, Module ℤ_[p] (E m)]
  [∀ m, AddCommGroup (F m)] [∀ m, Module ℤ_[p] (F m)]
  (ρ : ∀ m, A →ₗ[ℤ_[p]] E m) (σ : ∀ m, B →ₗ[ℤ_[p]] F m)
  (Q : ∀ m, E m →ₗ[ℤ_[p]] F m →ₗ[ℤ_[p]] ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m})

end Transport

end LinearMap
