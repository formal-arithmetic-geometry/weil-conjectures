/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.IntrinsicCoefficientTwists
import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted

/-! # Rationalization of inverse integral twists

Source: `literature/blueprint/master/blueprint/sec-smooth-purity/`
`sk-prop-sf-existence/prop-weil-twist-preserves.md`, final sentence
(blueprint: lem-weil-twist-rationalization).

The intrinsic constructible categories are the recorded integral and rational
categories. The scalar-localization map extends an additive linear integral
functor to the raw rational category, and the theorem records the inverse-pair
and exactness clauses for that extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe d u

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (S : Scheme.{u})
  [∀ x : S, Invertible (l : S.residueField x)]

/-- The canonical extension of an additive linear integral functor to the raw
scalar localization. Source: the raw localization in
`def-weil-rationalization-karoubi`, used in the final sentence of
`prop-weil-twist-preserves.md` (blueprint: lem-weil-twist-rationalization). -/
noncomputable def localizedIntegralFunctor
    (F : sfIntegralConstructibleCategory l E S ⥤
      sfIntegralConstructibleCategory l E S)
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E)] :
    sfRationalConstructibleCategory l E S ⥤
      sfRationalConstructibleCategory l E S :=
  ScalarLocalization.map (Padic.coefficientExtensionIntegers l E)
    (sfIntegralConstructibleCategory l E S)
    (Padic.coefficientExtensionUniformizer l E) F

/-- An exact linear inverse pair on the intrinsic integral category descends to
an exact inverse pair on its intrinsic raw rationalization.
Source: `prop-weil-twist-preserves.md`, proof, final sentence
(blueprint: lem-weil-twist-rationalization).

Proof: extend the Hom maps by scalar localization, sending a pure tensor a ⊗ f
to a ⊗ U(f), respectively a ⊗ V(f). The tensor relations and integral linearity
make these maps well defined. Identity and composition hold on pure tensors and
then on their sums. The induced shift comparisons localize the given comparisons;
distinguished triangles are images of integral distinguished triangles up to
isomorphism, so exactness of U and V gives exactness of both extensions. Localize
the components of η and ε. Integral naturality extends by bilinearity, and the
inverse equations extend by functoriality of localization. The extended composite
and identity functors agree with the corresponding composites and identities on
objects and all pure tensors, hence on every arrow. Thus the localized natural
isomorphisms have the asserted endpoints and the functors are inverse equivalences.
For the final clause, the displayed equalities after full-subcategory inclusion
identify U and V, including their arrow maps, with tensor by the completed signed
root lines of exponents m and -m. Applying the preceding conclusions gives exactly
the induced rational twists, on the same integral representatives. -/
theorem integral_twist_rationalization
    (U V : sfIntegralConstructibleCategory l E S ⥤
      sfIntegralConstructibleCategory l E S)
    [U.Additive] [V.Additive]
    [U.Linear (Padic.coefficientExtensionIntegers l E)]
    [V.Linear (Padic.coefficientExtensionIntegers l E)]
    [U.CommShift ℤ] [V.CommShift ℤ]
    [U.IsTriangulated] [V.IsTriangulated]
    (η : U ⋙ V ≅ 𝟭 (sfIntegralConstructibleCategory l E S))
    (ε : V ⋙ U ≅ 𝟭 (sfIntegralConstructibleCategory l E S)) :
    (∀ (K L : sfIntegralConstructibleCategory l E S)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
      (f : K ⟶ L),
      HEq
        ((localizedIntegralFunctor l E S U).map
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
            ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
              (p := Padic.coefficientExtensionUniformizer l E) K ⟶
            ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
              (p := Padic.coefficientExtensionUniformizer l E) L))
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] U.map f :
          ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
              (p := Padic.coefficientExtensionUniformizer l E) (U.obj K) ⟶
            ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
              (p := Padic.coefficientExtensionUniformizer l E) (U.obj L))) ∧
    (∀ (K L : sfIntegralConstructibleCategory l E S)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
      (f : K ⟶ L),
      HEq
        ((localizedIntegralFunctor l E S V).map
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
            ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
              (p := Padic.coefficientExtensionUniformizer l E) K ⟶
            ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
              (p := Padic.coefficientExtensionUniformizer l E) L))
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] V.map f :
          ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
              (p := Padic.coefficientExtensionUniformizer l E) (V.obj K) ⟶
            ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
              (p := Padic.coefficientExtensionUniformizer l E) (V.obj L))) ∧
    (∃ cU : (localizedIntegralFunctor l E S U).CommShift ℤ,
      (fun [commInst : (localizedIntegralFunctor l E S U).CommShift ℤ] ↦
        (localizedIntegralFunctor l E S U).IsTriangulated) (commInst := cU)) ∧
    (∃ cV : (localizedIntegralFunctor l E S V).CommShift ℤ,
      (fun [commInst : (localizedIntegralFunctor l E S V).CommShift ℤ] ↦
        (localizedIntegralFunctor l E S V).IsTriangulated) (commInst := cV)) ∧
    Nonempty (localizedIntegralFunctor l E S U ⋙
      localizedIntegralFunctor l E S V ≅
      𝟭 (sfRationalConstructibleCategory l E S)) ∧
    Nonempty (localizedIntegralFunctor l E S V ⋙
      localizedIntegralFunctor l E S U ≅
      𝟭 (sfRationalConstructibleCategory l E S)) ∧
    (∀ (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (m : ℤ),
      U ⋙ (sfIntegralConstructible l E S).ι =
        (sfIntegralConstructible l E S).ι ⋙ integralComplexTwist D l hl E S m →
      V ⋙ (sfIntegralConstructible l E S).ι =
        (sfIntegralConstructible l E S).ι ⋙ integralComplexTwist D l hl E S (-m) →
      Nonempty (localizedIntegralFunctor l E S U ⋙
        localizedIntegralFunctor l E S V ≅
        𝟭 (sfRationalConstructibleCategory l E S)) ∧
      Nonempty (localizedIntegralFunctor l E S V ⋙
        localizedIntegralFunctor l E S U ≅
        𝟭 (sfRationalConstructibleCategory l E S))) := by
  sorry

end WeilConjectures
