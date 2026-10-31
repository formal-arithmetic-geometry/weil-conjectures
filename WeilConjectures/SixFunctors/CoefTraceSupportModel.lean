/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTraceSectionNormalization
public import WeilConjectures.SixFunctors.DualizingSupportEvaluation

/-! Comparison of the two whole-tower compact-support presentations. -/

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

/-- Evaluated constant-scalar support is the normalized finite ringed support functor,
for every derived input and every horizontal arrow, before choosing dualizing objects.
Source: blueprint prop-coef-integral-dualizing, proof paragraph 2; Stacks 0941.
Proof: at the ordinary level constant scalar restriction commutes with open
extension, proper image and final-object sections: all three composites retain
exactly the underlying sheaves and their horizontal arrows. Exact restriction
commutes with open extension before deriving. The canonical right-derived
composition comparisons identify the separate proper image and point sections
with DualizingSupportEvaluation.B. Apply theta from evaluatedSupport. Change the
chosen section localization by the identity exact functor; localization
uniqueness identifies the transported horizontal map with coefTraceTransition.
This step is independent of finite dualizing origins and finite counits.
(blueprint: new-lem-coef-trace-support-model) -/
theorem coefTraceSupportModel (hl : l ≠ D.p) :
    ∃ θ : ∀ n : ℕ,
      coefTraceCompactSections l E (finiteDualizingCompactification D X) ⋙
          coefTraceEvaluation l E n ≅
        DualizingSupportEvaluation.target D l E (finiteDualizingCompactification D X) n ⋙
          coefTraceSmallSections l E,
      ∀ (Q : coefficientSequenceDerived.{u, u} l E X) {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app
            ((coefTraceCompactSections l E (finiteDualizingCompactification D X)).obj Q) ≫
          (θ n).hom.app Q =
        (θ m).hom.app Q ≫ (coefTraceSmallSections l E).map
          (DualizingSupportEvaluation.sectionTransition D l E
            (finiteDualizingCompactification D X) h Q) := by
  sorry

end WeilConjectures
