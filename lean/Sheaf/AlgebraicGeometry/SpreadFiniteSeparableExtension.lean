/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Spreading a finite separable extension

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`
(blueprint: lem-weil-pbc-spread-finite-separable-extension).
-/

set_option autoImplicit false

universe u v w

namespace AlgebraicGeometry

/-- A finite separable extension of the fraction field of a Noetherian domain spreads to
 a finite etale domain over a principal localization, with the given extension as fraction
 field. Both rings are represented inside the extension field, with their induced algebra
 structures; `IsLocalization.Away c S` identifies `S` with `A[c⁻¹]`. That `B` is a domain
 is automatic (`B` is a subring of the field `L`), so it is not a separate conjunct.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`
(blueprint: lem-weil-pbc-spread-finite-separable-extension).

Proof:
1. Choose a primitive element alpha by `lem-weil-pbc-finite-separable-primitive-element`.
Its monic minimal polynomial f is irreducible and separable, and
`lem-weil-pbc-minimal-polynomial-quotient-field-iso` identifies K[T]/(f) with K'.
2. Clear the coefficients' denominators and invert the nonzero discriminant, giving a
nonzero c and S = A[c⁻¹]. Then f is monic over S and f' is a unit modulo f. The algebra
B = S[T]/(f) is finite free, embeds in K' via T mapping to alpha, and has fraction field K'.
3. Since f' is invertible modulo f, `lem-weil-pbc-standard-etale-monic-derivative` makes
B etale over S. Its finite free presentation gives finiteness. The inclusion S into B is
injective and integral; `pqf-lem-lying-over` gives surjectivity on spectra.
-/
theorem exists_spread_finite_separable_extension
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ c : A, c ≠ 0 ∧ ∃ S : Subalgebra A L,
      IsLocalization.Away c S ∧ ∃ B : Subalgebra S L,
        Module.Finite S B ∧ Algebra.Etale S B ∧ IsFractionRing B L ∧
        IsFinite (Spec.map (CommRingCat.ofHom (algebraMap S B))) ∧
        Etale (Spec.map (CommRingCat.ofHom (algebraMap S B))) ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap S B))) := by
  sorry

end AlgebraicGeometry
