/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.RingTheory.Derivation.PowerSeriesPolynomialNormalization
import WeilConjectures.RingTheory.Derivation.PowerSeriesPolynomialDifferential
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coefficient preparation for detecting derivations

Let `B` be a domain of characteristic `p` of finite type over a Noetherian complete local
ring, with fraction field `M`, and `f ∈ B` detected by a derivation of `M`. Then `f` is
detected by a derivation of `M` that kills a subring `A` of `B` over which `B` is of finite
type.

## Implementation details

The base is replaced by a power series ring `R` over a field `k` (Cohen structure), and Noether
normalization gives a polynomial ring over `R` with fraction field `K`, `M/K` finite. Since
`f` is not a `p`-th power, the coefficient subfields of a `p`-basis of `k` (Tags 07P5, 07P4)
give a subring `A_J` with `f ∉ M^p K_J`, so the differential of `f` over `K_J` is nonzero, and a
linear functional nonzero on it gives the derivation. No denominator clearing is used here.

## References

* [Stacks, Tag 07PH]
* [Stacks, Tag 07P5]
* [Stacks, Tag 07P4]
-/

@[expose] public section
set_option autoImplicit false
universe u v w
namespace Derivation

/-- A detecting derivation can be chosen to kill a coefficient subring over which
`B` is finite type. Given a derivation of the fraction field `M` nonzero on `f`, there are a
subring `A` of `B` with `B` of finite type over `A` and a derivation of `M` that kills `A` and
is nonzero on `f`. -/
theorem exists_finite_coefficient_derivation
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [IsDomain B] [CharP B p]
    (M : Type v) [Field M] [Algebra B M] [IsFractionRing B M]
    (R₀ : Type w) [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀]
    [Algebra R₀ B] [Algebra.FiniteType R₀ B]
    (f : B) (D : Derivation ℤ M M) (hD : D (algebraMap B M f) ≠ 0) :
    ∃ A : Subring B, Algebra.FiniteType A B ∧
      ∃ δ : Derivation ℤ M M,
        (∀ a : A, δ (algebraMap B M a) = 0) ∧ δ (algebraMap B M f) ≠ 0 := by
  classical
  let : CharP M p := charP_of_injective_ringHom (IsFractionRing.injective B M) p
  have hf : ¬ ∃ x : M, x ^ p = algebraMap B M f := by
    rintro ⟨x, hx⟩
    apply hD
    rw [← hx, D.leibniz_pow, ← Nat.cast_smul_eq_nsmul M, CharP.cast_eq_zero]
    simp
  obtain ⟨C, hC, k, hk, n, m, hkp, ⟨e⟩, K, hK, aCK, hfrac, aKM, htower, hdim⟩ :=
    exists_powerSeries_polynomial_normalization p B M R₀
  let := hk
  let := hkp
  let := hK
  let := aCK
  let := hfrac
  let := aKM
  let : Algebra C M := ((algebraMap B M).comp C.subtype).toAlgebra
  let := htower
  let := hdim
  obtain ⟨A, hfinite, hdiff⟩ :=
    KaehlerDifferential.exists_finite_subring_nonzero_differential
      p k n m C e K M (algebraMap B M f) hf
  let : Algebra A M := ((algebraMap C M).comp A.subtype).toAlgebra
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero M hdiff
  let δ : Derivation ℤ M M := (φ.compDer (KaehlerDifferential.D A M)).restrictScalars ℤ
  let A' : Subring B := A.map C.subtype
  let eA : A ≃+* A' := A.equivMapOfInjective C.subtype Subtype.val_injective
  have hAC : A.subtype.FiniteType := by
    let : Module.Finite A C := hfinite
    exact (RingHom.finiteType_algebraMap).mpr inferInstance
  have hCB : C.subtype.FiniteType := (RingHom.finiteType_algebraMap).mpr hC
  have hcomp : (A'.subtype.comp eA.toRingHom).FiniteType := by
    convert hCB.comp hAC using 1
    ext a
    rfl
  have hA' : Algebra.FiniteType A' B :=
    (RingHom.finiteType_algebraMap).mp (RingHom.FiniteType.of_comp_finiteType hcomp)
  refine ⟨A', hA', δ, ?_, hφ⟩
  intro a
  obtain ⟨b, hb⟩ := eA.surjective a
  subst a
  change φ (KaehlerDifferential.D A M (algebraMap A M b)) = 0
  rw [Derivation.map_algebraMap, map_zero]

end Derivation
