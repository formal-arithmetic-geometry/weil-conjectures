/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients

/-! # Triangulated closure of the integral scalar-extension image

Source: Bhatt--Scholze, Lemma 6.8.12 and the full-faithfulness argument after localization
in Proposition 6.8.14(2). No full faithfulness of the integral functor is asserted.
(blueprint: lem-weil-pbc-continuous-constructible-integral-image)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- The essential image of integral constructible scalar extension is triangulated.
Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-continuous-constructible-integral-image)

Proof in words. Integral constructible modules form a weak Serre class by Proposition
6.8.11, so their bounded derived subcategory is closed under shifts and cones. Derived
coefficient extension is triangulated and sends zero to zero, giving zero and shift
closure of its essential image. For cone closure, take a morphism between scalar
extensions of two integral bounded constructible complexes. The localization telescope
and the bounded-below coproduct compactness of Lemma 6.8.12 identify the rational derived
Hom group with integral Hom after inverting ℓ. Thus a power of ℓ times the given morphism
is the scalar extension of an integral morphism. Complete that integral morphism to a
triangle; its cone is bounded integral constructible. Scalar extension gives a cone for
the multiplied morphism. Multiplication by that power of ℓ on the rational source is an
isomorphism, so the original morphism has an isomorphic cone. This proves cone closure,
and rotation gives the two-out-of-three formulation of triangulated closure. Transport
along the chosen endpoint isomorphisms handles every triangle whose endpoints lie in
the essential image. The coefficient telescope is the actual integralScalarExtension:
on compact profinite tests every continuous function has a single bounded denominator,
and exact pullback from the profinite point preserves that localization calculation.
This proves closure only; it does not assert that every rational object is in the image.
-/
theorem continuousConstructible_integral_image_triangulated (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    (((ProEtale.boundedConstructible (condensedRingObj (integralCoeff ℓ E) X)).ι ⋙
      integralScalarExtension ℓ E X).essImage).IsTriangulated := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
