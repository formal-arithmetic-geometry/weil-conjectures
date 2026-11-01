/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingCompactSupportIdentity
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingQuotientNormalization

/-! # Coefficient normalization before taking exceptional mates -/

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

/-- The proper/open comparison and regular scalar unit respect identity and
successive quotients, before transposition through an exceptional adjunction.
Source: current blueprint lem-coef-finite-dualizing.proof.md, paragraph 3,
"The same adjoint calculation proves the quotient cocycle"
(blueprint: lem-coef-dualizing-compact-normalization).

Proof: write the compact-support comparison as the proper coefficient mate followed
by proper direct image of the open balancing comparison. For an identity quotient,
the ordinary restriction identification is identity on sections. Conjugating it
under the scalar adjunction gives normalizedOriginScalarUnit. The defining proper
counit transpose and open-unit transpose identify their compact-support composite
with scalar unit at F(K) followed by F of the inverse scalar unit at K.
For two quotients, paste the two proper counit-mate squares. Paste the two open
balancing squares; on sections both send (x tensor b) tensor c to x tensor bc.
Functoriality of proper direct image and the interchange law identify the resulting
outer boundary with the composite quotient comparison and the published scalar
associators. This proves the equation for every K. The regular unit comparison is
uniquely normalized by multiplication B tensor_A A to B. Its identity equation
and successive-quotient equation follow on 1 and pure tensors by the same formulas;
sheafification and K-flat localization preserve those equalities. No exceptional
adjoint or dualizing comparison is used. Identity and nonflat quotients obey the
same balancing equations. -/
theorem finiteDualizing_compact_normalization :
    (∀ (n : ℕ) (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X),
      Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E
          (le_refl n)) (finiteDualizingCompactification D X) K =
        (ProEtale.normalizedOriginScalarUnit (Spec (.of D.k)).smallEtaleTopology _
          (finiteDualizingQuotient_id l E n)).hom.app
            ((finiteDualizingEtaleSupport l E D X n).obj K) ≫
        (finiteDualizingEtaleSupport l E D X n).map
          ((ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology _
            (finiteDualizingQuotient_id l E n)).inv.app K)) ∧
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
  obtain ⟨h1, h2, h3⟩ := finiteDualizing_quotient_normalization l E D X
  exact ⟨finiteDualizing_compact_support_identity l E D X, h1, h2, h3⟩

end WeilConjectures
