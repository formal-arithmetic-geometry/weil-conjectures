/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.Paper.FiniteFreeHomLocalCalculation

/-! # Restriction of coefficient-Hom comparisons

Source: thm-coef-finite-hom, proof paragraphs 2–3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
attribute [local implicit_reducible] finiteHomEtaleCategory
attribute [local instance] lisseHomModuleDerivedCategory
attribute [local irreducible] _root_.DerivedCategory instCategoryDerivedCategory
attribute [local irreducible] Functor.rightAdjoint Functor.leftAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Etale.upperStar Etale.lowerStar _root_.DerivedCategory.monoidalClosed
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor
  Padic.coefficientExtensionAbsoluteValue Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionIdeal
  coefficientBaseChangeHom finiteHomEtaleData finiteHomEtaleClosed finiteHomEtaleTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- Etale restriction commutes with the canonical coefficient-Hom comparison for
perfect first inputs.
Source: thm-coef-finite-hom, restriction compatibility in paragraphs 2–3
(blueprint: lem-coef-etale-perfect-hom-restriction).

Proof: etale derived pullback is monoidal. Its internal-Hom comparison is invertible
on a dualizable first input. Scalar extension is monoidal and preserves dualizability,
so the comparison over the target coefficient ring is also invertible. Transpose
the desired square through the target tensor-Hom adjunction. Naturality of evaluation
and the tensor and unit compatibility of the canonical scalar/pullback isomorphism
identify both sides with the restriction of reduced evaluation. Injectivity of
transposition proves the square. -/
theorem etalePerfectHomRestriction (T U : Scheme.{u}) (f : U ⟶ T) [Etale f]
    {n m : ℕ} (h : m ≤ n) (K N : finiteHomEtale l E T n)
    (hK : IsDualizable K) :
    ∃ (vT : LisseHomComparisonType
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))
        (finiteHomQuotient l E h) T K N)
      (vU : LisseHomComparisonType
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))
        (finiteHomQuotient l E h) U
        (L(Etale.upperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) f).obj K)
        (L(Etale.upperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) f).obj N)),
      HEq vT (etaleFiniteHomCanonical l E T h K N) ∧
      HEq vU (etaleFiniteHomCanonical l E U h
        (L(Etale.upperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) f).obj K)
        (L(Etale.upperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) f).obj N)) ∧
      LisseHomRestrictionCompatibilityRing _ _ (finiteHomQuotient l E h) T U f
        K N vT vU := by
  sorry

end WeilConjectures
