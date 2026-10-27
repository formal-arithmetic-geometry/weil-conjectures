/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.FiniteDualizingData

/-! Unit and successive-quotient normalization for finite dualizing coefficients. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/--
The regular scalar unit and the two successive-quotient equations for finite
 dualizing coefficients.  The scalar unit is identified with the normalized
origin unit at the base.  The two remaining equations are the mate-pasting
identities for compact support and for the regular coefficient unit.  Expanding
the proper/open factorization, applying the coefficient comparison cocycle,
and cancelling the invertible scalar mates proves all three equations.  The
argument is valid for equal levels and for arbitrary (possibly non-flat)
quotient maps.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md`, paragraphs 1--3 and
final sentence.
(blueprint: lem-coef-dualizing-compact-normalization)
-/
theorem finiteDualizing_quotient_normalization :
    (∀ n : ℕ, (Etale.ExceptionalCoefficients.unitIso
        (finiteDualizingQuotient l E (le_refl n)) (Spec (.of D.k))).hom =
      (ProEtale.normalizedOriginScalarUnit (Spec (.of D.k)).smallEtaleTopology _
        (finiteDualizingQuotient_id l E n)).hom.app
          (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m)
      (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E r) X),
      (Etale.scalarExtension (finiteDualizingQuotient l E hmn) (Spec (.of D.k))).map
          (Etale.ExceptionalCoefficients.compactSupportMap
            (finiteDualizingQuotient l E hrm) (finiteDualizingCompactification D X) K) ≫
        Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E hmn)
          (finiteDualizingCompactification D X)
          ((Etale.scalarExtension (finiteDualizingQuotient l E hrm) X).obj K) ≫
        (finiteDualizingEtaleSupport l E D X n).map
          ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology _ _ _
            (finiteDualizingQuotient_comp l E hrm hmn)).hom.app K) =
      (ProEtale.pbcFixedScalarExtensionComp (Spec (.of D.k)).smallEtaleTopology _ _ _
        (finiteDualizingQuotient_comp l E hrm hmn)).hom.app
          ((finiteDualizingEtaleSupport l E D X r).obj K) ≫
        Etale.ExceptionalCoefficients.compactSupportMap
          (finiteDualizingQuotient l E (hmn.trans hrm))
          (finiteDualizingCompactification D X) K) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      (Etale.scalarExtension (finiteDualizingQuotient l E hmn) (Spec (.of D.k))).map
          (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E hrm)
            (Spec (.of D.k))).hom ≫
        (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E hmn)
          (Spec (.of D.k))).hom =
      (ProEtale.pbcFixedScalarExtensionComp (Spec (.of D.k)).smallEtaleTopology _ _ _
        (finiteDualizingQuotient_comp l E hrm hmn)).hom.app
          (Etale.constantComplex (finiteDualizingCoeff l E r) (Spec (.of D.k))) ≫
        (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E
          (hmn.trans hrm)) (Spec (.of D.k))).hom) := by
  sorry

end WeilConjectures
