/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Spec

/-!
# DescendModelLocalization

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-descend-model-localization)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open AlgebraicGeometry

/-- Descend a specified nonzero denominator of a finite étale domain model to a
principal open of the original base. The resulting small domain is a localization of
that model at a multiple of the denominator. No finite algebra B or product of fields
occurs in this statement.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9; steps 3--4 of
`lem-weil-pbc-spread-generic-product-embedding`.
(blueprint: lem-weil-pbc-descend-model-localization)

Proof: The nonzero t is integral over S0 because A0 is finite over S0. Among its
monic integral equations choose one of least degree. Its constant coefficient a is
nonzero: otherwise cancel t in the domain and obtain a monic equation of smaller
degree. Evaluating the equation shows that the image of a is divisible by t in A0.
Write a = b/c0^n in S0 with b nonzero in A. Put c = c0*b and s = algebraMap S0 A0 a.
Localizing S0 at a is the same as localizing A at c. Localizing A0 at s is consequently
the base change of A0 along that localization of S0. Hence it remains finite étale
and surjective on spectra. It remains a domain and has fraction field K', since s
is nonzero. It is finite as a module over A[1/c], so it is small in the universe of A.
Transport its ring, algebras, localization and fraction-ring structures to a small
presentation. The algebra maps from A0, A and A[1/c], and the map to K', commute by
construction; they give all the displayed scalar towers. -/
theorem exists_descend_model_localization
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (K' : Type (max u v)) [Field K'] [Algebra A K']
    (c0 : A) (hc0 : c0 ≠ 0) (S0 : Subalgebra A K')
    [IsLocalization.Away c0 S0] (A0 : Subalgebra S0 K')
    [Algebra A A0] [IsScalarTower A S0 A0] [IsScalarTower A A0 K']
    [Module.Finite S0 A0] [Algebra.Etale S0 A0] [IsFractionRing A0 K']
    (hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S0 A0))))
    (t : A0) (ht : t ≠ 0) :
    ∃ (s : A0), t ∣ s ∧ s ≠ 0 ∧
      ∃ (c : A) (A' : Type u) (_ : CommRing A') (_ : Algebra (Localization.Away c) A')
        (_ : Algebra A A') (_ : IsScalarTower A (Localization.Away c) A')
        (_ : IsDomain A') (_ : Algebra A' K') (_ : Algebra A0 A')
        (_ : IsScalarTower A A0 A') (_ : IsScalarTower A0 A' K')
        (_ : IsLocalization.Away s A'),
        c ≠ 0 ∧ Module.Finite (Localization.Away c) A' ∧
          Algebra.Etale (Localization.Away c) A' ∧ IsFractionRing A' K' ∧
          Surjective (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A')))
          := by sorry
