/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
import Sheaf.AlgebraicGeometry.PrincipalOpenDenseOfNonZeroDivisor
import WeilConjectures.Blowup.BlowupUniversal

/-!
# Density of a principal nonzerodivisor complement

Source: Stacks Project, Divisors, Lemma 31.14.4 (Tag 07ZU), affine-local calculation
(blueprint: lem-pc-affine-nonzerodivisor-complement-dense).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a nonzerodivisor `a`, the restriction of the structure sheaf of `Spec A` to
the principal open `D(a)` is injective on every open, and `D(a)` is dense.

Source: Stacks Project, Divisors, Lemma 31.14.4 (Tag 07ZU), affine-local calculation
(blueprint: lem-pc-affine-nonzerodivisor-complement-dense).

Proof: On each principal open `D(g)`, restriction to `D(a)` is localization
`A_g → (A_g)_a`. Localization preserves nonzerodivisors
([lem-pc-localization-preserves-nonzerodivisor]), and localization at a nonzerodivisor
is injective ([lem-pc-affine-localization-injective]). Injectivity on this basis gives
injectivity of the restriction sheaf morphism. The principal open is dense by
[lem-pc-principal-open-dense-of-nonzerodivisor]. -/
theorem PrimeSpectrum.basicOpen_app_injective_and_dense_of_nonZeroDivisor
    (A : Type u) [CommRing A] (a : A) (ha : a ∈ nonZeroDivisors A) :
    (∀ V : (Spec (.of A)).Opens,
      Function.Injective
        ((Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen a)).app V)) ∧
    DenseRange (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen a)) := by
  sorry

end AlgebraicGeometry
