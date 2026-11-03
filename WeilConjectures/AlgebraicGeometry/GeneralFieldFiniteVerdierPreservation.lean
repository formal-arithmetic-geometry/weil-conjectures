/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing

import WeilConjectures.SixFunctors.Etale.Derived.Stability.HomDevissage

/-!
# Finite-coefficient Verdier duality over an arbitrary field

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-verdier-biduality/sk-thm-pd-verdier-duality/det-pd-biduality-coefficients.proof.md`,
proof (i), the independent preservation input to the internal-Hom comparison at `D_X K`
(blueprint: lem-sf-general-field-finite-verdier-preservation).

For a prime `ell`, a field `k` of characteristic different from `ell` and a finite ring `A`
killed by a positive power of `ell`, the Verdier dual `D_X = RHom_A(-, a^! A)` of a separated
finite-type `a : X ⟶ Spec k` preserves bounded constructible complexes of finite Tor
amplitude. No perfection, finiteness or algebraic closedness of `k` is assumed.

The Verdier dual is the published `AlgebraicGeometry.Etale.verdierDual`, the internal Hom into
`AlgebraicGeometry.Etale.dualizingComplex = R(a)^! A`, the right adjoint of `Ra_!` for the
chosen compactification. Bounded constructibility and finite Tor amplitude are the framework
predicates `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible` and
`AlgebraicGeometry.Etale.DerivedCategory.finiteTorAmplitude` (`D^b_ctf`, as in
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleFiniteTor`); for a finite ring
they agree with the recorded `isBoundedConstructible` and `∃ a b, hasTorAmplitudeIn a b`
(`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

/-- Finite-coefficient Verdier duality preserves bounded constructible complexes of finite
Tor amplitude over an arbitrary field whose characteristic is different from the coefficient
prime. The coefficient ring is explicitly assumed to be killed by a positive power of the
prime, and no perfection or algebraic-closedness hypothesis is imposed on the field.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-verdier-biduality/sk-thm-pd-verdier-duality/det-pd-biduality-coefficients.proof.md`,
proof (i), expanded preservation input
(blueprint: lem-sf-general-field-finite-verdier-preservation).

Proof (node, step by step).
1. Choose `r ≥ 1` with `ell ^ r = 0` in `A`. As `ell` is prime and `ringChar k ≠ ell`, `ell` is
   nonzero, hence a unit, in `k`; so `ell ^ r` is a unit in `Γ(Spec k)`. This gives
   `HasInvertibleExponent A (Spec k)`, and `HasInvertibleExponent.of_hom a` gives it on `X`.
2. The tensor unit over `Spec k` is the degree-zero single complex on the unit sheaf, which is
   constructible and flat (it is dualizable); so it lies in `Dctf(Spec k, A)` with Tor amplitude
   `[0, 0]` (def-weil-pbc-constructible-complexes, def-kun-tor-amplitude).
3. Stability of `Dctf` under `Ra^!` over an arbitrary field
   (`constructibleFiniteTor_dualizingComplex`, sk-prop-sf-rf-shriek-preservation) gives
   `ω_X = Ra^! A ∈ Dctf(X, A)`.
4. Internal Hom preserves `Dctf` over an arbitrary field, by dévissage
   (`constructibleFiniteTor_derivedHom_of_field`, det-rem-sf-matrix-hom-devissage; no
   biduality is used), so `D_X K = RHom(K, ω_X) ∈ Dctf(X, A)`. -/
theorem generalFieldFiniteVerdierPreservation
    (ell : ℕ) [Fact ell.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ (ell ^ r : A) = 0)
    {k : Type u} [Field k] [Fact (ringChar k ≠ ell)]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K ∧
      DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X
        ((verdierDual A a).obj (op K)) ∧
      DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) X
        ((verdierDual A a).obj (op K)) := by
  obtain ⟨r, _, hr⟩ := hA
  have hell : (ell : k) ≠ 0 := by
    intro hz
    exact (Fact.out : ringChar k ≠ ell)
      (CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) hz)
  have : HasInvertibleExponent A (Spec (.of k)) := by
    refine ⟨ell ^ r, pow_pos (Fact.out : ell.Prime).pos r, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hr
    · simpa only [map_pow, map_natCast, Nat.cast_pow] using
        ((isUnit_iff_ne_zero.mpr hell).pow r).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have : HasInvertibleExponent A X := HasInvertibleExponent.of_hom a
  have hunit : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A)
      (Spec (.of k)) (𝟙_ _) :=
    ⟨(DerivedCategory.boundedConstructible _ _).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0), 0, 0,
      (DerivedCategory.torAmplitudeIn _ _ 0 0).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
          (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩
  exact constructibleFiniteTor_derivedHom_of_field A a hK
    (constructibleFiniteTor_dualizingComplex A (𝟙 _) a hunit)

end AlgebraicGeometry.Etale
