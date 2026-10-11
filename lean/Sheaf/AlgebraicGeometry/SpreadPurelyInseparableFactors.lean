/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Spreading purely inseparable factors

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation;
Stacks Project, Tags 00GQ, 0BR5, 01S4 and 04DF
(blueprint: lem-weil-pbc-spread-purely-inseparable-factors).
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A finite domain algebra with a finite purely inseparable extension of fraction fields
becomes surjective and radicial, hence a universal homeomorphism, after a principal localization
of the original base. The tensor-product map is induced by `A' → E` and the identity of `A[1/s]`.
The scalar towers express that the extension of fraction fields is the induced one.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation;
Stacks Project, Tags 00GQ, 0BR5, 01S4 and 04DF
(blueprint: lem-weil-pbc-spread-purely-inseparable-factors).

Proof:
1. Finiteness makes `E` integral over `A'`. The compatible fraction-field maps make
   `A' → E` injective. After localization, lying over
   (`lem-weil-pbc-integral-injective-lying-over`, Tag 00GQ) proves surjectivity on spectra.
2. The finite algebra `A'` is Noetherian. Apply
   `lem-weil-pbc-power-in-base-after-localization` to obtain a nonzero `s' : A'`.
   Choose a monic equation for `s'` over `A` of minimal degree. Its constant term `s`
   is nonzero, since `A'` is a domain, and is divisible by `s'` in `A'`.
   Thus localizing at `s : A` also inverts `s'`, and the power property persists.
   In characteristic zero the localized rings coincide. In characteristic `p > 0`,
   each element has a `p^n`-th power in the base. Two primes over the same base prime
   therefore coincide, and quotients of ring elements in the residue fields also have
   a `p^n`-th power in the base residue field. The residue extensions are purely inseparable.
   Hence the map is radicial, equivalently universally injective
   (`def-weil-radicial-morphism`, Tag 01S4).
3. The localized map is integral, radicial and surjective. Apply
   `lem-pc-integral-radicial-surjective-universal-homeomorphism` (Tag 04DF)
   to obtain the universal-homeomorphism conclusion. -/
theorem exists_spread_purely_inseparable_factors
    (A A' E : Type u) (K : Type v) (K' : Type w) (L : Type z)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing A'] [IsDomain A'] [Algebra A A'] [Module.Finite A A']
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap A A')))]
    [CommRing E] [IsDomain E] [Algebra A' E] [Module.Finite A' E]
    [Algebra A E] [IsScalarTower A A' E]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Field L] [Algebra E L] [IsFractionRing E L]
    [Algebra K' L] [Algebra A' L]
    [IsScalarTower A' E L] [IsScalarTower A' K' L]
    [Module.Finite K' L] [IsPurelyInseparable K' L] :
    ∃ s : A, s ≠ 0 ∧
      Surjective (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
          (AlgHom.id A (Localization.Away s))).toRingHom)) ∧
      UniversallyInjective (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
          (AlgHom.id A (Localization.Away s))).toRingHom)) ∧
      (topologically IsHomeomorph).universally (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
          (AlgHom.id A (Localization.Away s))).toRingHom)) := by
  sorry

end AlgebraicGeometry
