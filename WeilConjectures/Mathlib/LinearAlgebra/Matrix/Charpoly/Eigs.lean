/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.Mathlib.Algebra.Polynomial.AlgebraMap
public import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Eigenvalues of an endomorphism of a vector space over an algebraically closed field

Over an algebraically closed field the characteristic polynomial of an endomorphism of a finite
dimensional vector space splits. This file records the descriptions of the characteristic
polynomial, of its reverse, of the determinant and of the traces of the polynomials in the
endomorphism that follow, all in terms of the roots of the characteristic polynomial counted with
multiplicity.

## Main results

- `LinearMap.maxGenEigenspace_ne_bot_iff_mem_roots_charpoly`: the generalized eigenvalues of `f`
  are the roots of its characteristic polynomial, and `LinearMap.sum_map_roots_charpoly` rewrites
  a sum over the roots as a sum over the generalized eigenvalues weighted by the dimensions of the
  maximal generalized eigenspaces.
- `LinearMap.charpoly_eq_prod_roots`: the characteristic polynomial of `f` is `∏ (X - μ)`.
- `LinearMap.charpolyRev_eq_prod_roots`: its reverse is `∏ (1 - μ * X)`.
- `LinearMap.card_roots_charpoly`: the number of roots is the dimension of the space.
- `LinearMap.det_eq_prod_roots_charpoly`: the determinant of `f` is the product of the roots.
- `LinearMap.zero_notMem_roots_charpoly`: `0` is not a root as soon as `f` is invertible.
- `LinearMap.trace_aeval_eq_sum_eval_roots_charpoly`: the trace of `q(f)` is `∑ q(μ)`, with the
  specialisations `LinearMap.trace_eq_sum_roots_charpoly`,
  `LinearMap.trace_pow_eq_sum_pow_roots_charpoly` and `Matrix.trace_pow_eq_sum_pow_roots_charpoly`
  for the trace and for the power sums `∑ μ ^ m` of the roots.
- `Matrix.charpolyRev_eq_prod_roots`: the reciprocal characteristic polynomial `det (1 - t • A)`
  of a matrix is `∏ (1 - μ * t)`.
-/

@[expose] public section

open Module Polynomial Set

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The generalized eigenvalues of `f` are exactly the roots of its characteristic polynomial. -/
theorem maxGenEigenspace_ne_bot_iff_mem_roots_charpoly (f : V →ₗ[K] V) (μ : K) :
    End.maxGenEigenspace f μ ≠ ⊥ ↔ μ ∈ f.charpoly.roots := by
  classical
  rw [ne_eq, ← Submodule.finrank_eq_zero, finrank_maxGenEigenspace_eq, ← count_roots, ← ne_eq,
    Multiset.count_ne_zero]

/-- The finite set of generalized eigenvalues of `f` is the set of roots of its characteristic
polynomial. -/
theorem maxGenEigenspace_ne_bot_toFinset_eq_roots_toFinset [DecidableEq K] (f : V →ₗ[K] V)
    (hfin : {μ : K | End.maxGenEigenspace f μ ≠ ⊥}.Finite) :
    hfin.toFinset = f.charpoly.roots.toFinset := by
  ext μ
  simp [maxGenEigenspace_ne_bot_iff_mem_roots_charpoly]

/-- A sum over the roots of the characteristic polynomial of `f`, counted with multiplicity, is
the sum over the generalized eigenvalues of `f` weighted by the dimensions of the corresponding
maximal generalized eigenspaces. -/
theorem sum_map_roots_charpoly {M : Type*} [AddCommMonoid M] (f : V →ₗ[K] V) (g : K → M)
    (hfin : {μ : K | End.maxGenEigenspace f μ ≠ ⊥}.Finite) :
    (f.charpoly.roots.map g).sum
      = ∑ μ ∈ hfin.toFinset, finrank K (End.maxGenEigenspace f μ) • g μ := by
  classical
  rw [Finset.sum_multiset_map_count, maxGenEigenspace_ne_bot_toFinset_eq_roots_toFinset f hfin]
  exact Finset.sum_congr rfl fun μ _ ↦ by rw [count_roots, ← finrank_maxGenEigenspace_eq]

/-- If `g - c` is nilpotent on a `g`-invariant submodule `p`, then the trace of `g` on `p` is
`c` times the dimension of `p`. -/
theorem trace_restrict_of_isNilpotent_sub_algebraMap {p : Submodule K V} {g : V →ₗ[K] V}
    (hg : MapsTo g ↑p ↑p) (c : K)
    (h : IsNilpotent (g.restrict hg - algebraMap K (Module.End K p) c)) :
    trace K p (g.restrict hg) = c * finrank K p := by
  have h₁ := trace_comp_eq_mul_of_commute_of_isNilpotent (f := (LinearMap.id : Module.End K p))
    (g := g.restrict hg) c (Commute.one_left _) h
  rwa [LinearMap.id_comp, trace_id] at h₁

/-- The trace of `q(f)` on the maximal generalized `μ`-eigenspace of `f` is `q(μ)` times the
dimension of that eigenspace. -/
theorem trace_restrict_maxGenEigenspace_aeval (f : V →ₗ[K] V) (q : K[X]) (μ : K)
    (h : MapsTo (aeval f q) ↑(End.maxGenEigenspace f μ) ↑(End.maxGenEigenspace f μ)) :
    trace K _ ((aeval f q).restrict h)
      = q.eval μ * (finrank K (End.maxGenEigenspace f μ) : K) := by
  have hf : MapsTo f ↑(End.maxGenEigenspace f μ) ↑(End.maxGenEigenspace f μ) :=
    End.mapsTo_maxGenEigenspace_of_comm rfl μ
  have hsmul : MapsTo (algebraMap K (Module.End K V) μ)
      ↑(End.maxGenEigenspace f μ) ↑(End.maxGenEigenspace f μ) := fun x hx ↦ by
    simpa [Module.algebraMap_end_apply] using (End.maxGenEigenspace f μ).smul_mem μ hx
  have h₁ : IsNilpotent
      (f.restrict hf - algebraMap K (Module.End K (End.maxGenEigenspace f μ)) μ) := by
    have halg : (algebraMap K (Module.End K V) μ).restrict hsmul
        = algebraMap K (Module.End K (End.maxGenEigenspace f μ)) μ := rfl
    rw [← halg, restrict_sub hf hsmul]
    exact End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ
  refine trace_restrict_of_isNilpotent_sub_algebraMap h _ ?_
  rw [← Module.End.aeval_restrict hf q h]
  exact h₁.aeval_sub_algebraMap_eval q

variable [IsAlgClosed K]

theorem charpoly_eq_prod_roots (f : V →ₗ[K] V) :
    f.charpoly = (f.charpoly.roots.map fun a ↦ X - C a).prod :=
  (IsAlgClosed.splits _).eq_prod_roots_of_monic f.charpoly_monic

theorem charpolyRev_eq_prod_roots (f : V →ₗ[K] V) :
    f.charpolyRev = (f.charpoly.roots.map fun a ↦ 1 - C a * X).prod :=
  charpolyRev_def f ▸ (IsAlgClosed.splits _).reverse_eq_prod_one_sub_C_mul_X f.charpoly_monic

theorem card_roots_charpoly (f : V →ₗ[K] V) : f.charpoly.roots.card = finrank K V := by
  rw [(splits_iff_card_roots).mp (IsAlgClosed.splits _), charpoly_natDegree]

theorem det_eq_prod_roots_charpoly (f : V →ₗ[K] V) : f.det = f.charpoly.roots.prod := by
  classical
  set b := Module.finBasis K V with hb
  rw [← det_toMatrix b, ← charpoly_toMatrix f b, Matrix.det_eq_prod_roots_charpoly]

theorem zero_notMem_roots_charpoly {f : V →ₗ[K] V} (hf : IsUnit f.det) :
    (0 : K) ∉ f.charpoly.roots := fun h ↦ by
  rw [det_eq_prod_roots_charpoly, Multiset.prod_eq_zero h] at hf
  exact not_isUnit_zero hf

/-- Over an algebraically closed field, the trace of `q(f)` for an endomorphism `f` of a
finite-dimensional vector space is the sum of `q(μ)` over the roots `μ` of the characteristic
polynomial of `f`, counted with multiplicity. -/
theorem trace_aeval_eq_sum_eval_roots_charpoly (f : V →ₗ[K] V) (q : K[X]) :
    trace K V (aeval f q) = (f.charpoly.roots.map q.eval).sum := by
  classical
  have hindep : iSupIndep (End.maxGenEigenspace f) := End.independent_maxGenEigenspace f
  have hds : DirectSum.IsInternal (End.maxGenEigenspace f) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep
      (End.iSup_maxGenEigenspace_eq_top f)
  have hfin : {μ : K | End.maxGenEigenspace f μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hindep
  have hcomm : Commute f (aeval f q) := by
    simpa using (Commute.all (X : K[X]) q).map (aeval f)
  have hmaps (μ : K) :
      MapsTo (aeval f q) ↑(End.maxGenEigenspace f μ) ↑(End.maxGenEigenspace f μ) :=
    End.mapsTo_maxGenEigenspace_of_comm hcomm μ
  rw [trace_eq_sum_trace_restrict' hds hfin hmaps, sum_map_roots_charpoly f _ hfin]
  exact Finset.sum_congr rfl fun μ _ ↦ by
    rw [trace_restrict_maxGenEigenspace_aeval, nsmul_eq_mul, mul_comm]

/-- Over an algebraically closed field, the trace of an endomorphism of a finite-dimensional
vector space is the sum of the roots of its characteristic polynomial, counted with
multiplicity. -/
theorem trace_eq_sum_roots_charpoly (f : V →ₗ[K] V) :
    trace K V f = f.charpoly.roots.sum := by
  simpa using f.trace_aeval_eq_sum_eval_roots_charpoly X

/-- Over an algebraically closed field, the trace of the `m`-th power of an endomorphism of a
finite-dimensional vector space is the `m`-th power sum of the roots of its characteristic
polynomial, counted with multiplicity. -/
theorem trace_pow_eq_sum_pow_roots_charpoly (f : V →ₗ[K] V) (m : ℕ) :
    trace K V (f ^ m) = (f.charpoly.roots.map (· ^ m)).sum := by
  simpa using f.trace_aeval_eq_sum_eval_roots_charpoly (X ^ m)

end LinearMap

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If the characteristic polynomial of a matrix splits, its reciprocal characteristic polynomial
`det (1 - t • A)` is the product of `1 - μ t` over the roots `μ` of the characteristic polynomial,
counted with multiplicity. -/
theorem charpolyRev_eq_prod_roots_of_splits {R : Type*} [CommRing R] [IsDomain R]
    (B : Matrix n n R) (hB : B.charpoly.Splits) :
    B.charpolyRev = (B.charpoly.roots.map fun μ ↦ 1 - C μ * X).prod :=
  B.reverse_charpoly ▸ hB.reverse_eq_prod_one_sub_C_mul_X B.charpoly_monic

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, the trace of the `m`-th power of a matrix is the `m`-th
power sum of the roots of its characteristic polynomial, counted with multiplicity. -/
theorem trace_pow_eq_sum_pow_roots_charpoly (A : Matrix n n K) (m : ℕ) :
    (A ^ m).trace = (A.charpoly.roots.map (· ^ m)).sum := by
  rw [← charpoly_toLin' A, ← LinearMap.trace_pow_eq_sum_pow_roots_charpoly A.toLin' m,
    ← toLin'_pow, trace_toLin'_eq]

/-- Over an algebraically closed field, the reciprocal characteristic polynomial
`det (1 - t • A)` of a matrix is the product of `1 - μ t` over the roots `μ` of its
characteristic polynomial, counted with multiplicity. -/
theorem charpolyRev_eq_prod_roots (A : Matrix n n K) :
    A.charpolyRev = (A.charpoly.roots.map fun μ ↦ 1 - C μ * X).prod :=
  A.charpolyRev_eq_prod_roots_of_splits (IsAlgClosed.splits _)

end Matrix
