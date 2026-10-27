/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FieldShriekSystemMixed

/-! # Mixed quotient and field-extension compatibility of compact support

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
proof step 8 of lem-sp-field-shriek-system-comparison.
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
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

/-- The given finite evaluation law extends to mixed quotient compatibility for the
actual system comparison. This does not assert invertibility or the whole-system
coefficient-extension cocycle, and retains the given evaluation coordinates exactly.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
lem-sp-field-shriek-system-comparison, step 8
(blueprint: lem-sp-field-shriek-system-mixed-compatibility).

Proof: identify quotient restriction with constant-ring restriction by the identity
on sections. The residue-class formula in Coefficients proves the coefficient square:
both quotient paths send an integer x to its image modulo ell^(m+1). Transpose the
naturality square of derivedTransition under the finite scalar adjunction; this is
ComparisonTransitionSquare for every system morphism, hence for comparison.app M.
The semilinear direct-image transition formula, followed by termwise open evaluation,
identifies the compact-support transition with finite coefficient comparison followed
by compact support of the input reduction. Substitute this formula and the given
EvaluationLaw in quotientAfterComparison and comparisonAfterQuotient. The finite
coefficient cocycle identifies the two coefficient words with the comparison for the
common map R_n to S_m, under the specified scalar associators. Naturality of the
finite comparison moves the input reduction past the second comparison, leaving
exactly commonTransitionComparison. The coefficient square transports the two source
scalar actions; their targets are already identical, so these are the required HEq
statements. Equal indices reduce to the scalar unitors. The quotient maps may be
nonflat throughout: all reductions are the actual derived adjunction transposes. -/
theorem field_shriek_system_mixed (P : PurityFiniteSetting.{u}) (D : Models P)
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (c : Compactification f)
    (e : EvaluationLaw P D c) :
    ∃ l : MixedLaw P D c, l.toEvaluationLaw = e := by sorry

end AlgebraicGeometry.ProEtale.FieldShriekSystem
