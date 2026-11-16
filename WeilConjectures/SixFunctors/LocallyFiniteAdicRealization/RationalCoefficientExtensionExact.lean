/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.NativeIntegralCoefficientFlat
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplete

/-! # Exactness of rational scalar extension along an arbitrary coefficient map

This is the coefficient-ring input to the realization scalar functor of the proper base
change chapter. The normalized case is `integralRationalCoefficient_flat`.

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-flat)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Ordinary scalar extension along an **arbitrary** ring-sheaf map `φ` from the completed
integral coefficients to the rational coefficients preserves finite limits.

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
(blueprint: lem-sf-native-integral-coefficient-flat).

Missing input from the coefficient-ring chapter (cross-section rule). The normalized
inclusion is proved sectionwise flat in `integralRationalCoefficient_flat`. Sections of the
rational coefficient sheaf are continuous `E`-valued functions. Along the inclusion they are a
localization, hence flat, over the continuous integral-valued functions, and
`pbcExtend_preservesFiniteLimits_of_flat` then gives exactness.

Precise obstacle for an arbitrary `φ`: one needs the classification of ring-sheaf maps
`φ`. Every such map should be, locally on the pro-étale site, the normalized inclusion
followed by an automorphism of `E` over `ℚ_ℓ`, and hence flat. This requires three facts
that are not yet formalized:
* every ring homomorphism from `ℚ_ℓ` into a finite extension `E` is continuous, by the
  Hensel characterization of `ℤ_ℓ`;
* every `ℚ_ℓ`-embedding of `E` into itself is an automorphism;
* naturality on the pro-étale site forces `φ` to be pointwise of this form. -/
theorem pbcExtend_rationalCoefficient_preservesFiniteLimits (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (φ : pbcAdicCompletion T (pbcIntegralDatum l E) ⟶ rationalCoefficientSheaf l T E) :
    PreservesFiniteLimits (pbcExtend φ) := by
  sorry

end AlgebraicGeometry.Scheme
