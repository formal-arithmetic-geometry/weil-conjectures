/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransportData
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence

/-! # Smooth purity for all admissible condensed coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/
_section.md, theorem (10.1), and sk-thm-purity-transport.proof.md,
Steps 1--4 and the final compatibility paragraph.
(blueprint: sk-thm-purity-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- The canonical natural smooth-purity isomorphism (10.1), compatible with
coefficient change, base change and composition, and normalized by affine-line trace.
Its canonical family is rendered using the explicit adjunctions and counit-preserving
Brown comparison constructed in proof Step 3.
Source: current nested blueprint sk-thm-purity-transport/_section.md, theorem (10.1),
and its proof Steps 1--4; the finite-or-algebraically-closed base convention is that
of sk-prop-sf-existence, in the positive-characteristic sk-def-sfb-dc-setting.
(blueprint: sk-thm-purity-transport).
Proof in words. For every finite ring, including nonregular and zero rings, use
the finite normalized counit system and its section-action realization. Reconstruct
the integral adjunction from the normalized positive tower and its transition
counits. Localize the Hom bijections and counits to obtain rational coefficients.
Descend objects and arrows for the algebraic closure to one finite subextension.
The resulting adjunctions have the displayed coefficient, base-change and
composition equations and the affine integration normalization. Restrict the
specified Brown adjunction to finite Tor objects. Uniqueness of right adjoints
with a fixed counit gives the natural gamma, uniquely satisfying its counit
identity. The transported finite and reconstructed comparisons satisfy that
identity and therefore are this same gamma. -/
theorem smooth_purity_transport (k : Type u) [Field k]
    [Fact (ringChar k).Prime] (_hk : Finite k ∨ IsAlgClosed k)
    (hEll : IsUnit (ell : k)) :
    ∃ a : AdjunctionFamily ell k,
      BrownComparison ell k a ∧
      ScalarCompatible ell k a ∧
      BaseChangeCompatible ell k a ∧
      CompositionCompatible ell k hEll a ∧
      AffineNormalized ell k a := by
  sorry

end AlgebraicGeometry.ProEtale.GeneralPurityTransport
