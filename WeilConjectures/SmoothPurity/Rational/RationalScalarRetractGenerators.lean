/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import Mathlib.CategoryTheory.Retract

import WeilConjectures.SmoothPurity.Rational.RationalScalarIntegralDenominatorSplit
import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionConstructible
import WeilConjectures.SmoothPurity.Rational.RationalScalarLocalizationRetract

/-! # Scalar-extended retract generators of the raw rational category

Every raw rational `F`-object is a retract of an object extended from `E`, by finite
separability applied to the coefficient-restriction construction.

## Implementation details

Restricting the completed coefficient action of `K` from `𝒪_F` to `𝒪_E` gives an object `M` of
the raw rational `E`-category. With a separability element `∑ i, a_i ⊗ b_i` of `F ⊗_E F`,
multiplication gives `T(M) ⟶ K` and `x ↦ ∑ i, a_i ⊗ b_i x` gives `K ⟶ T(M)`; one common
`𝒪_E` denominator turns these into morphisms of the raw localized Hom groups.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 6.8.14(2), Remark 6.8.15.
* Stacks Project, Tags 090W and 02FL (the separability diagonal).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Every raw rational F-object is a retract of an object extended from E. -/
theorem rationalScalar_retract_generators
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (K : sfRationalConstructibleCategory l F W) :
    ∃ M : sfRationalConstructibleCategory l E W,
      Nonempty (Retract K ((sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M)) := by
  let M : sfRationalConstructibleCategory l E W :=
    ⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
      rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩
  refine ⟨M, ?_⟩
  apply rationalScalar_constructible_trace_retract l E F ι W K
  exact rationalScalar_ambient_trace_retract l E F ι W K

end WeilConjectures
