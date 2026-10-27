/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.Paper.RationalModuleRealizationFunctor
public import Sheaf.Paper.RationalContinuousCoefficientDerivedLocalization

/-! # Normalized localization of the completed coefficient ring

Source: Bhatt--Scholze, Lemma 6.8.2, pp. 58--59, and Proposition 6.8.14(2), p. 62.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] pbcIntegralDatum pbcRationalCoefficientEquiv
  ringedLocalizationRingOfUniverses ringedLocalizationRingUnitOfUniverses

/-- The completed ring localizes to the rational continuous coefficient ring,
with its specified unit and constant sections.
Source: Bhatt--Scholze, Lemma 6.8.2, pp. 58--59, and Proposition 6.8.14(2), p. 62.
(blueprint: lem-per-rational-realization-coefficient-localization).

Proof: apply every finite quotient projection to the image under R.integralIso
of a completed constant section. R.finite_normalization and
R.integral_normalization identify the result with the reduction of that constant.
The intersection of all powers of the uniformizer ideal in the valuation ring
is zero, so equality of these reductions proves equality of continuous integral
functions, point by point. In particular the uniformizer section is preserved.
Localize R.integralIso sectionwise at these matching sections. The localization
universal property gives inverse ring maps, and its uniqueness makes them
natural. Sheafify this presheaf isomorphism and compose with R.localizationIso.
On integral numerators its unit is R.integralIso.hom followed by R.inclusion:
R.localization_normalization and R.inclusion_normalization give the same
pointwise value. On constant integral sections the comparison is the lifted
field inclusion. The ring maps on A[1/t] therefore agree by uniqueness of
localization, using the canonical coefficient equivalence A[1/t] = E. Apply
the inverse coefficient isomorphism to get the displayed inverse formula.
Sheafification permits denominators to vary locally; no quasi-compactness or
nonemptiness of a test object, and no nonzero module, is required. -/
theorem rationalRealizationCoefficientLocalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (R : RationalModuleRealization l E X) :
    let B := pbcAdicCompletion X (pbcIntegralDatum l E)
    let a := pbcCompletedScalarSections X (pbcIntegralDatum l E)
    let t := pbcUniformizer l E
    let S := ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t)
    ∃ c : S ≅ rationalCoefficientSheaf l X E,
      ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} B (a t) ≫ c.hom =
        R.integralIso.hom ≫ R.inclusion ∧
      ∀ (r : Localization.Away t) (U : X.ProEtᵒᵖ),
        c.inv.hom.app U
          ((rationalModuleConstantMap l E X).hom.app U
            ((toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
                (ULift.up (pbcRationalCoefficientEquiv l E r)))) =
          (scalarLocalizationCoefficientMapOfUniverses (PbcIntegralRing l E)
            B a t r).val U := by sorry

end AlgebraicGeometry.Scheme
