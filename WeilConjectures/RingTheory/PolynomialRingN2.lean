/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension
import WeilConjectures.RingTheory.IsN2OfFiniteExtension
import WeilConjectures.RingTheory.PolynomialPurelyInseparableIntegralClosureFinite
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import WeilConjectures.RingTheory.N2CharPPurelyInseparableCriterion

/-!
# Polynomial rings over Noetherian Japanese domains

The polynomial ring in one variable over a Noetherian N-2 domain is N-2.

## Implementation details

Replacing `R` by its finite normalization, `R[x]` is a Noetherian normal domain with fraction
field `K(x)`. In characteristic zero, finite separable extensions are handled by the separable
criterion. In characteristic `p`, it suffices to treat finite purely inseparable extensions
`L / K(x)`; these embed into `L'(t)` with `t^q = x`, where the integral closure is `A[t]` for the
finite integral closure `A` of `R` in `L'`.

## References

* [Stacks, Tag 032O] (second assertion)
-/

@[expose] public section

universe u

set_option autoImplicit false

private theorem finite_polynomial_extension (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] :
    letI : Algebra (Polynomial R) (Polynomial A) := Polynomial.algebra R A
    Module.Finite (Polynomial R) (Polynomial A) := by
  let : Algebra (Polynomial R) (Polynomial A) := Polynomial.algebra R A
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := A)
  let T := Submodule.span (Polynomial R) (Polynomial.C '' (s : Set A))
  have hC (a : A) : Polynomial.C a ∈ T := by
    have ha : a ∈ Submodule.span R (s : Set A) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩
    | zero => simp [T]
    | add a b ha hb ha' hb' => simpa using T.add_mem ha' hb'
    | smul r a ha ha' =>
      simpa [Algebra.smul_def, Polynomial.algebraMap_def] using
        T.smul_mem (Polynomial.C r) ha'
  have hmem (p : Polynomial A) : p ∈ T := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact T.add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_comm]
      convert T.smul_mem (Polynomial.X ^ n) (hC a) using 1
      simp only [Algebra.smul_def, Polynomial.algebraMap_def,
        Polynomial.coe_mapRingHom, Polynomial.map_pow, Polynomial.map_X]
  have hT : T = ⊤ := top_unique (fun p _ ↦ hmem p)
  exact ⟨⟨s.image Polynomial.C, by simpa [T] using hT⟩⟩

private theorem isN2_polynomial_normal (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (hR : IsN2 R (FractionRing R)) :
    IsN2 (Polynomial R) (FractionRing (Polynomial R)) := by
  rcases CharP.exists' (FractionRing (Polynomial R)) with hzero | ⟨p, hp, hchar⟩
  · let := hzero
    intro L _ _ _ _ _
    exact IsIntegralClosure.finite (Polynomial R) (FractionRing (Polynomial R)) L
      (integralClosure (Polynomial R) L)
  · let := hp
    let := hchar
    apply isN2_of_finite_purelyInseparable_integralClosure
      (Polynomial R) (FractionRing (Polynomial R)) p
    intro L _ _ _ _ _ _
    exact finite_polynomial_purelyInseparable_integralClosure R hR p L

/-- The polynomial ring in one variable over a Noetherian N-2 domain is N-2. -/
theorem isN2_polynomial (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : IsN2 R (FractionRing R)) :
    IsN2 (Polynomial R) (FractionRing (Polynomial R)) := by
  let A := integralClosure R (FractionRing R)
  let : Algebra (Polynomial R) (Polynomial A) := Polynomial.algebra R A
  let : Module.Finite R A := hR (FractionRing R)
  let : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  let : IsIntegrallyClosed A :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  have hinj : Function.Injective (algebraMap R A) := by
    intro r s hrs
    apply IsFractionRing.injective R (FractionRing R)
    exact congrArg (fun a : A ↦ (a : FractionRing R)) hrs
  have hA : IsN2 A (FractionRing A) :=
    isN2_of_finite_domain_extension R A (FractionRing R) (FractionRing A) hinj hR
  let : Module.Finite (Polynomial R) (Polynomial A) := finite_polynomial_extension R A
  apply isN2_of_finite_extension (Polynomial R) (Polynomial A)
    (FractionRing (Polynomial R)) (FractionRing (Polynomial A))
  · exact Polynomial.map_injective (algebraMap R A) hinj
  · exact isN2_polynomial_normal A hA
