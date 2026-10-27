/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.Paper.FieldExceptionalSystemLaws

/-! # Finite evaluations of the exceptional coefficient transpose

Only the finite comparison and mixed quotient step are asserted here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExceptionalSystem

open FieldShriekSystem
variable (P : PurityFiniteSetting.{u})

/-- Evaluation of the actual exceptional transpose is the finite coefficient mate;
that finite mate is invertible and its two mixed quotient composites agree.
This makes no assertion about unit, counit, naturality, composition or identity of
whole-system comparisons, or invertibility of a whole-system arrow.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
finite evaluations and the square of quotient and field coefficient maps.
(blueprint: lem-sp-field-exceptional-finite-compatibility).

Proof: Apply evaluation at n to the defining counit equation of component. The
AdjunctionEvaluationNormalized equation of A identifies the tower counit with the
finite counit, while b.scalarEvaluation and b.evaluation identify scalar extension
and the compact-support comparison. A.leftNormalized fixes the same left evaluation
coordinate. Thus the evaluated arrow, conjugated by sourceEvaluation and
targetEvaluation, has the counit transpose defining finiteComponent. Injectivity of
the finite adjunction Hom bijection proves evaluationLaw. The finite adjoints retain
their ordinary-etale counit realizations; uniqueness of such adjoints transports
reductionExceptional_isIso to them. Counit transposition then identifies its
invertible finite comparison with finiteComponent, proving the last assertion.
For mixedLaw apply reductionCompatibilities_composition to the field map followed
by the quotient map and to the quotient map followed by the field map. The
finiteComponent counit equations discharge the comparison hypotheses. Both composites
are the direct comparison by injectivity of transposition. The residue-class formula
in D.coefficients proves equality of the two ring maps; transport along that equality
gives the second HEq. The scalar associators are exactly those in finiteComposite.
Equal levels and identity field extensions use the same associators and unitors;
quotient maps need not be flat. All these equalities are in finite derived categories. -/
theorem field_exceptional_finite_compatibility
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f)
    (D : Models P) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) :
    evaluationLaw P D c b a A ∧ mixedLaw P D c b a A ∧
      ∀ (E F : Index P) (h : E ≤ F) (n : ℕ)
        (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)),
        IsIso (finiteComponent P D c b a A ((D.coefficients E F h).quotient n) K) := by
  sorry

end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
