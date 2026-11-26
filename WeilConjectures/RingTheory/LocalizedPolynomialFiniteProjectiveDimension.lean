/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.LocalizedPolynomialTorBound
import WeilConjectures.RingTheory.FiniteProjectiveDimensionOfTorBound

/-! # Finite projective dimension over a localized polynomial ring

A finite module over a prime localization of a polynomial ring over a Noetherian ring has finite
projective dimension if it has finite Tor dimension over the base.

## Implementation details

The base map is flat and its nonzero fibres have global dimension at most `n`, so Stacks 068X
makes the module perfect. A syzygy beyond its Tor amplitude is flat and finitely presented,
hence projective, giving a bounded projective resolution and the vanishing of `Ext` above its
length.

## References

* [Stacks, Tag 068X]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A finite module over a prime localization of a polynomial ring is perfect if it
has finite Tor dimension over the base.
-/
theorem localizedPolynomial_finiteProjectiveDimension_of_finiteTor
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) A))
    (M : ModuleCat.{u} (Localization p.asIdeal.primeCompl))
    [Module.Finite (Localization p.asIdeal.primeCompl) M]
    (d : ℕ)
    (hTor : ∀ N : ModuleCat.{u} A, ∀ i : ℕ, d < i →
      IsZero (((Tor' (ModuleCat.{u} A) i).obj
        ((ModuleCat.restrictScalars
          ((algebraMap (MvPolynomial (Fin n) A)
            (Localization p.asIdeal.primeCompl)).comp MvPolynomial.C)).obj M)).obj N)) :
    ∃ k : ℕ, HasProjectiveDimensionLE M k := by
  have hTorS := localizedPolynomial_tor_bound_of_base_tor_bound n p M d hTor
  refine ⟨d + n, ?_⟩
  exact finite_hasProjectiveDimensionLE_of_tor_bound M (d + n) hTorS

end ModuleCat
