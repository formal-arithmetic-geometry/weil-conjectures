/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTraceSectionNormalization
public import WeilConjectures.SixFunctors.DualizingSupportEvaluation

/-! Finite support and point sections in the two coefficient presentations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Finite support of the pro-etale dualizing object has its canonical etale
presentation, compatibly with the specified scalar-adjunction transitions.
Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, finite origins.
Proof: apply the finite dualizing origin isomorphism under compact support and
point sections. The finite-Tor site comparison identifies pro-etale support with
etale support; the point comparison and exact constant scalar restriction give
an isomorphism for each level. For a pair of levels apply the specialized formula
in evaluatedSupport to the given input transition. The proper scalar-mate/site
square and open scalar normalization identify its comparison with
finiteDualizingCompactComparison. The origin identifies its adjunct with
finiteDualizingEtaleComparison. Naturality in the two level isomorphisms gives
the displayed equation. This statement concerns only finite support values;
it constructs no whole-tower comparison or evaluation isomorphism.
(blueprint: new-lem-coef-trace-finite-support-transport) -/
theorem coefTraceFiniteSupportTransport (hl : l ≠ D.p) :
    ∃ i : ∀ n : ℕ,
      (coefTraceSmallSections l E).obj
        ((DualizingSupportEvaluation.sections D l E n).obj
        ((sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
          (Padic.coefficientExtensionRing l E (n + 1))).obj
            (integralDualizingFiniteTerm l E D X n))) ≅ coefTraceFiniteValue l E D X n,
      ∀ (Q : coefficientSequenceDerived.{u, u} l E X)
        (eQ : ∀ n : ℕ, (coefficientSequenceDerivedEvaluation l E X n).obj Q ≅
          integralDualizingFiniteTerm l E D X n)
        (hQ : ∀ {m n : ℕ} (h : n ≤ m),
          (coefficientSequenceDerivedTransition l E X h).app Q ≫
              (normalizedDVRRes l E X h).map (eQ n).hom =
            (eQ m).hom ≫ integralDualizingExceptionalTransition l E D X hl h)
        {m n : ℕ} (h : n ≤ m),
        (coefTraceSmallSections l E).map
            (DualizingSupportEvaluation.sectionTransition D l E
              (finiteDualizingCompactification D X) h Q) ≫
          (coefTraceSmallSections l E).map
            ((DualizingSupportEvaluation.sections D l E n).map
              ((sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
                (Padic.coefficientExtensionRing l E (n + 1))).map (eQ n).hom)) ≫
                  (i n).hom =
        (coefTraceSmallSections l E).map
            ((DualizingSupportEvaluation.sections D l E m).map
              ((sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
                (Padic.coefficientExtensionRing l E (m + 1))).map (eQ m).hom)) ≫
            (i m).hom ≫ coefTraceFiniteTransition l E D X h := by
  sorry

end WeilConjectures
