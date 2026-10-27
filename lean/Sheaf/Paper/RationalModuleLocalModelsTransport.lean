/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion

/-! # Ordinary rational module models under coefficient transport

The completed presentation is compared with the continuous coefficient presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary localization of the completed finitely presented local models.
Source: Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.10 and Proposition 6.8.14(2)
(blueprint: lem-per-rational-module-local-models-transport).

Proof: first use completedConstantModelTransport to compare the completed constant
model with its ordinary quotient-tower realization. The scalar square identifies the
completed constant realization after extension along i with the ordinary continuous
integral model. Prove this identification by
uniqueness of left adjoints to scalar restriction, retaining the constant module unit.
The scalar tower comparison followed by RationalStratum.scalarModels identifies its
localization with the rational constant realization of E tensor_A N. This argument is
ordinary tensor reassociation and holds for every finitely presented N, including torsion.
For a sheaf M with the given stratified integral presentations, transport each covering
sieve and each local model across i and the normalized immersion coefficient comparison.
Inverse image and slice restriction commute with localization. Apply
RationalStratum.chosenLocalModel on these same covers: a finite basis of E tensor_A N
identifies each localized model with a finite power of the rational ring sheaf. Transport
finite local freeness back along the immersion coefficient isomorphism. This is valid
also for rank zero and the empty stratification. It yields the claimed finite locally
free inverse-image sheaves on the original strata. -/
theorem rationalModuleLocalModelsTransport (X : Scheme.{u}) [IsNoetherian X]
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (_hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E))) :
    (∀ M : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)),
      IsIntegralStratifiedFinitelyPresented X (pbcIntegralDatum l E) M →
        ∃ s : FiniteLocallyClosedStratification X, ∀ k : Fin s.n,
          ((proEtaleModuleInverseImage (s.immersion k)
            (rationalCoefficientSheaf l X E)).obj
              ((pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)).obj M)
            ).IsFiniteLocallyFree) ∧
    (∀ (N : ModuleCat.{u + 1} (PbcIntegralRing l E)),
      Module.FinitePresentation (PbcIntegralRing l E) N →
        Nonempty ((pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)).obj
          ((integralConstantModule X (pbcIntegralDatum l E)).obj N) ≅
            (adicLisseConstantModules X (ULift.{u + 1} E) ⋙
              pbcExtend (letI := coefficientExtensionNormedField l E
                continuousCoefficientConstantComparison X (ULift.{u + 1} E))).obj
                ((ModuleCat.extendScalars
                  (RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype)).obj N))) :=
  by sorry

end AlgebraicGeometry.Scheme
