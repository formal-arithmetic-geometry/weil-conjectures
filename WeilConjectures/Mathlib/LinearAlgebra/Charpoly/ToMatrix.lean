/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Dual
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The reverse characteristic polynomial of an endomorphism

## Main declarations

* `LinearMap.charpolyRev`: the reverse characteristic polynomial `det (1 - t • f)` of an
  endomorphism `f` of a finite free module.
* `LinearMap.charpoly_dualMap`: the characteristic polynomial is invariant under transposition.
* `LinearMap.C_det_mul_charpolyRev`: if `f * g = c • 1`, then `det (1 - t • g)` is determined by
  the characteristic polynomial of `f`.
-/

@[expose] public section

open Module Polynomial

namespace LinearMap

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- The reverse characteristic polynomial `det (1 - t • f)` of an endomorphism `f` of a finite
free module, defined as the reverse of the characteristic polynomial. -/
noncomputable def charpolyRev (f : M →ₗ[R] M) : R[X] := f.charpoly.reverse

theorem charpolyRev_def (f : M →ₗ[R] M) : f.charpolyRev = f.charpoly.reverse := rfl

theorem charpolyRev_toMatrix {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Basis ι R M)
    (f : M →ₗ[R] M) : (toMatrix b b f).charpolyRev = f.charpolyRev := by
  rw [charpolyRev_def, ← charpoly_toMatrix f b, Matrix.reverse_charpoly]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The characteristic polynomial of the transpose of an endomorphism agrees with the
characteristic polynomial of the endomorphism. -/
theorem charpoly_dualMap (f : V →ₗ[K] V) : f.dualMap.charpoly = f.charpoly := by
  classical
  set b := Module.finBasis K V with hb
  rw [← charpoly_toMatrix f b, ← charpoly_toMatrix f.dualMap b.dualBasis, LinearMap.dualMap_def,
    LinearMap.toMatrix_transpose, Matrix.charpoly_transpose]

/-- If `f * g = c • 1`, then the reverse characteristic polynomial of `g` is determined by the
characteristic polynomial of `f`. -/
theorem C_det_mul_charpolyRev {f g : V →ₗ[K] V} {c : K} (h : f * g = c • 1) :
    C f.det * g.charpolyRev = C ((-1) ^ finrank K V) * f.charpoly.comp (C c * X) := by
  classical
  set b := Module.finBasis K V with hb
  have hmul : toMatrix b b f * toMatrix b b g = c • 1 := by
    rw [← toMatrix_mul, h]
    simp
  have := Matrix.C_det_mul_charpolyRev hmul
  rwa [charpolyRev_toMatrix, charpoly_toMatrix, det_toMatrix, Fintype.card_fin] at this

end LinearMap
