/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.IntegralCompositeNormalizedCompositionTrace

/-! # Refinement from generated to arbitrary integral composites

The refinement comparison and the coherent compositor transport the equation
from a generated composite compactification to an arbitrary `ch` and `H`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.PurityTransport

/--
Source: current blueprint `sk-prop-sp-composition-comparisons.proof.md`
(det-sp-composition-comparisons, (2): compactifications chosen compatibly), the
compactification independence used in `sk-prop-sp-composition.proof.md`
(blueprint: lem-pur-integral-normalized-trace-refinement).

Proof in words.  For each prescribed composite compactification and coherent
support datum, choose the generated composite supplied by the comparison system.
Use the comparison cocycle and independence laws to transport its normalized
equation across the refinement square.  Naturality of the normalized counits and
the source comparison carries the equation through the coherent support
compositor, while uniqueness of line-pull coordinates identifies the transported
source coordinate with the one in `NormalizedCompositionTrace`. -/
theorem normalizedCompositionTrace_of_composite
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (c : Coefficient ell)
    (hcomp : CompositeNormalizedCompositionTrace ell D hEll c) :
    NormalizedCompositionTrace ell D hEll c := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
