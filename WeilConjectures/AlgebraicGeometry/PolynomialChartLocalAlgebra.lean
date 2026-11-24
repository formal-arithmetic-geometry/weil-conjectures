/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreDimensions
import WeilConjectures.AlgebraicGeometry.PolynomialChartStalkFlatComparison

/-! # Local algebra comparison for a polynomial chart

## References

* Stacks Project, Tags 00RE, 00R7 and 00RH.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem dimension_le_of_quasiFinite {R S : Type u}
    [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.QuasiFinite) :
    ringKrullDim S ≤ ringKrullDim R := by
  algebraize [φ]
  have : Algebra.QuasiFinite R S := hφ
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap φ)
  intro p q hpq
  refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
  intro heq
  have h := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R)
    p.asIdeal q.asIdeal hpq.le (congrArg PrimeSpectrum.asIdeal heq)
  exact hpq.ne (PrimeSpectrum.ext h)

private theorem fibre_dimension_zero {R S : Type u}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] (hφ : φ.QuasiFinite) :
    ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map φ) = 0 := by
  algebraize [φ]
  have : Algebra.QuasiFinite R S := hφ
  let I := (IsLocalRing.maximalIdeal R).map φ
  have hI : I ≠ ⊤ := (IsLocalRing.map_maximalIdeal_lt_top φ).ne
  let Q := S ⧸ I
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing Q := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hunder (p : Ideal Q) [p.IsPrime] : p.under R = IsLocalRing.maximalIdeal R := by
    symm
    apply (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top' (I := p.under R))
    intro x hx
    change algebraMap R Q x ∈ p
    have hxI : φ x ∈ I := Ideal.mem_map_of_mem φ hx
    have hzero : algebraMap R Q x = 0 := by
      change Ideal.Quotient.mk I (φ x) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hxI
    rw [hzero]
    exact p.zero_mem
  have : Ring.KrullDimLE 0 Q := by
    apply Ring.krullDimLE_zero_iff.mpr
    intro p hp
    have := hp
    have heq : p = IsLocalRing.maximalIdeal Q :=
      Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) p (IsLocalRing.maximalIdeal Q)
        (IsLocalRing.le_maximalIdeal hp.ne_top) ((hunder p).trans (hunder _).symm)
    rw [heq]
    infer_instance
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/-- The geometric part of the polynomial-chart criterion, without a depth assertion
(Stacks, Tags 00RE, 00R7, 00RH and 00P1). -/
theorem polynomial_chart_local_algebra
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e] [LocallyQuasiFinite e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    let S := (f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x))
    ∃ (R : CommRingCat.{u}) (_ : IsRegularLocalRing R)
      (φ : R →+* S) (_ : IsLocalHom φ) (d r t : ℕ),
      IsNoetherianRing S ∧
      ringKrullDim R = (d : WithBot ℕ∞) ∧
      ringKrullDim S = (r : WithBot ℕ∞) ∧
      ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map φ) = 0 ∧
      r ≤ d ∧
      topologicalKrullDimAt (f.asFiber (U.ι x)) = ((r + t : ℕ) : WithBot ℕ∞) ∧
      n = d + t ∧
      ((e.stalkMap x).hom.Flat ↔ φ.Flat) := by
  let S := (f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x))
  let R := PolynomialChart.sourceStalk f U n e he x
  let φ := PolynomialChart.stalkMap f U n e he x
  have hR : IsRegularLocalRing R := PolynomialChart.isRegularLocalRing_sourceStalk f U n e he x
  have hS : IsNoetherianRing S := by
    have : IsLocallyNoetherian (f.fiber (f (U.ι x))) := by
      dsimp [Scheme.Hom.fiber]
      infer_instance
    infer_instance
  have hφ : φ.QuasiFinite := PolynomialChart.quasiFinite_stalkMap f U n e he x
  obtain ⟨d, r, t, hd, hr, htop, hn⟩ := polynomial_chart_fibre_dimensions f U n e he x
  have hle := dimension_le_of_quasiFinite φ hφ
  change ringKrullDim S ≤ ringKrullDim R at hle
  rw [hd, hr] at hle
  have hrd : r ≤ d := by
    exact_mod_cast hle
  exact ⟨R, hR, φ, inferInstance, d, r, t, hS, hd, hr,
    fibre_dimension_zero φ hφ, hrd, htop, hn,
    polynomial_chart_stalk_flat_comparison f U n e he x⟩

end AlgebraicGeometry
