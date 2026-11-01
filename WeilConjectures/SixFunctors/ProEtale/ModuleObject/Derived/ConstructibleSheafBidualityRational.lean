/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Rational.RationalVerdier

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Rational coefficient-stage Verdier biduality and scalar coherence.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`, the
integral-to-rational sentence.  It is the current rational-stage theorem and
has no finite-stage biduality hypothesis.
(blueprint: lem-pd-constructible-sheaf-biduality-rational) -/
theorem rational_stage_biduality
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] :
    WeilConjectures.RationalVerdier.Conclusion D l hl X := by
  exact WeilConjectures.coef_rational_verdier D l hl X

end AlgebraicGeometry.ProEtale.CondensedRing
