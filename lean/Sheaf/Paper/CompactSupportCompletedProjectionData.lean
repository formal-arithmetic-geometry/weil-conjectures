/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Paper.SfProEtaleProjectionFormula

/-! # The completed compact-support projection construction

Source: Stacks 0B56, 0E8I, 099N; the integral projection construction underlying
blueprint sk-thm-sf-pf-proetale and the scalar/projection identification, Steps 5--6
(blueprint: def-pur-compact-support-completed-projection-data).

These abbreviations re-export the actual tensor model, endpoints, typing lemma
and completed projection. They assert no projection-formula invertibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace WeilConjectures.PurProjectionData

/-- The signed K-flat ordinary derived tensor model over the completed ring sheaf.
Source: Stacks 07A4; integral projection construction
(blueprint: def-pur-compact-support-completed-projection-data). -/
abbrev TensorModel := @SfProEtaleProjection.TensorModel.{u}

/-- The ordinary tensor Rp_* j_! M tensor K, before its completion unit.
Source: Stacks 0B56, 0E8I; integral projection construction
(blueprint: def-pur-compact-support-completed-projection-data). -/
abbrev ordinarySource := @SfProEtaleProjection.ordinarySource.{u}

/-- The ordinary inner tensor M tensor f-star K, before its completion unit.
Source: Stacks 0B56, 099N; integral projection construction
(blueprint: def-pur-compact-support-completed-projection-data). -/
abbrev ordinaryInner := @SfProEtaleProjection.ordinaryInner.{u}

/-- Completion of the ordinary source tensor with its specified Roos unit.
Source: Stacks 099N; integral projection construction
(blueprint: def-pur-compact-support-completed-projection-data). -/
abbrev completedSource := @SfProEtaleProjection.completedSource.{u}

/-- Actual proper/open image of the completed inner tensor.
Source: Stacks 0B56, 0E8I, 099N; integral projection construction
(blueprint: def-pur-compact-support-completed-projection-data). -/
abbrev completedTarget := @SfProEtaleProjection.completedTarget.{u}

/-- The existing typing theorem: the ordinary source completion unit is invertible
and the completed source and target are integral constructible, for every supplied
compactification and integral constructible inputs over the finite-field datum.
Source: Bhatt--Scholze Sections 6.5, 6.7; integral projection construction
(blueprint: def-pur-compact-support-completed-projection-data).
Proof: re-export the existing theorem, preserving its full type. Finite quotient
constructibility and common Tor bounds, open extension and proper image, and the
normalized Roos reconstruction give these typing facts. This helper proves no
invertibility of the projection map itself. -/
abbrev integralDomains := @SfProEtaleProjection.integralDomains.{u}

/-- The actual integral projection: inverse source completion unit, followed by
the ordinary proper-counit/open projection, then compact support of the inner unit.
Its endpoints use exactly the preceding typing theorem, with no new witness.
Source: Stacks 0B56, 0E8I, 099N; integral projection construction
(blueprint: def-pur-compact-support-completed-projection-data). -/
abbrev integralMap := @SfProEtaleProjection.integralMap.{u}

end WeilConjectures.PurProjectionData
