/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.Paper.PurityConventions
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Regular.Flat

/-!
# Regular immersions in smooth schemes over a perfect field

Source: blueprint main-20261015, sec-smooth-purity,
`sk-lem-regular-smooth/_section.md` (blueprint: sk-lem-regular-smooth).

The immersion uses the affine-local pure-codimension convention of
`WeilConjectures.PurityConventions.IsRegularOfPureCodimension`, including codimension zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A regular closed immersion of pure codimension `c`, with smooth ambient scheme over
a perfect field and regular source locally of finite type, has smooth structure morphisms
and lowers the Krull dimension of every local ring by `c`. The source structure morphism
is the composite `i ≫ aX`.

Source: blueprint main-20261015, sec-smooth-purity, sk-lem-regular-smooth
(blueprint: sk-lem-regular-smooth).

Proof:
1. The ambient structure morphism is smooth by hypothesis. The structure morphism of `Z`
   is `i ≫ aX` by the scheme-over-base convention (def-weil-scheme-over-base).
2. The regular-smooth criterion over a perfect field
   (lem-trf-regular-perfect-field-smooth, `smooth_of_isRegular`) applies to `Z` and this
   locally finite-type composite, so the source structure morphism is smooth.
3. For `z : Z`, the purity convention gives an affine neighbourhood `Spec A` of `i z`
   whose defining ideal `J` has an `A`-regular sequence of length `c` as generators.
   The affine description of a closed immersion identifies the inverse image with `Spec (A/J)`
   (def-weil-closed-immersion). The affine stalk-localization theorem and localization of a
   quotient identify the local rings with `A_p` and `A_p / J A_p`
   (lem-weil-pbc-affine-open-stalk-localization,
   lem-weil-pbc-localization-at-prime-of-quotient).
4. Smoothness makes the ambient local ring regular and hence Noetherian
   (lem-weil-pbc-smooth-scheme-over-field-regular). The generators lie in `p`; their
   localized images are a regular sequence in `A_p`
   (lem-weil-pbc-weakly-regular-sequence-localization-prime).
5. The regular-sequence dimension formula (lem-trf-regular-sequence-dimension-formula)
   gives the quotient dimension plus `c` equal to the dimension of `A_p`. The localized
   generators generate `J A_p`, and ring isomorphisms preserve chains of primes, so this
   is the asserted stalkwise equality. The empty sequence covers `c = 0`; for empty `Z`
   the dimension assertion is vacuous. -/
theorem regularImmersion_smooth_structure_and_stalk_dimension
    {k : Type u} [Field k] [PerfectField k] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
    (hi : WeilConjectures.PurityConventions.IsRegularOfPureCodimension i c)
    (aX : X ⟶ Spec (.of k)) [Smooth aX] [LocallyOfFiniteType (i ≫ aX)]
    (hZ : IsRegularScheme Z) :
    Smooth aX ∧ Smooth (i ≫ aX) ∧
      ∀ z : Z, ringKrullDim (X.presheaf.stalk (i z)) =
        ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
