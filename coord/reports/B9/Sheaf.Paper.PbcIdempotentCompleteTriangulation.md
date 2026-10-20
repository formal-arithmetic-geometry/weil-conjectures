## What changed

Completed `AlgebraicGeometry.Scheme.pbcIdempotentCompleteTriangulation` without changing its statement, definitions, visibility, or public imports. The proof uses `qbarScalarRep_rel`, `qbarScalarHom_mkHom`, and `pbcQbarLinear` from the existing Qbar-category interface, projects the Verdier and canonical Karoubi assertions from their existing theorems, and proves the final finite-stage scalar equation by semilinearity and `tr_map`. The private generic helper and explicit object arguments avoid expensive inference of representative stages in the concrete coefficient category. Updated the existing node's proof route and dependencies. Added one fully proved private helper, `scalarHom_inclusion`, for the generic same-stage scalar calculation. No new public declarations, definitions, or nodes.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Scheme.pbcIdempotentCompleteTriangulation` (node `thm-weil-pbc-idempotent-complete-triangulation`). Added 0 holes; 0 holes remain in the delivered module. This is a proof from existing stated dependencies, not a decomposition. Existing upstream holes, including those of the Qbar-category interface, remain assigned to their existing nodes and are not moved or duplicated here.

## No longer needed

Removed these direct proof imports:

- `Mathlib.LinearAlgebra.TensorProduct.Basic`
- `Mathlib.RingTheory.Localization.Away.Basic`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.CategoryTheory.ScalarLocalization`
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`
- `Sheaf.Paper.CommonStageCalculus`
- `Sheaf.Paper.FiniteStagePairCategory`
- `Sheaf.Paper.IntrinsicQbarCategory`
- `Sheaf.Paper.PbcRationalCategory`
- `Sheaf.Paper.PbcScalarExtension`

Removed direct proof dependencies `def-weil-linear-scalar-localization`, `def-weil-pbc-rational-category`, `lem-pur-derived-change-of-rings`, and `prop-weil-pbc-scalar-extension`. The specialized semilinearity and quotient-scalar APIs already state exactly what this proof needs, so this module need not repeat the integral tensor or rationalization argument. Removed the obsolete top-level tool approvals for `lem-pur-derived-change-of-rings` and `prop-weil-pbc-scalar-extension`. Retained the common-stage tool and both Verdier and Karoubi theorem dependencies. The removed imports may remain transitively reachable through those retained dependencies; this report does not claim their global withdrawal.

## Where the brief, the DAG or earlier work was wrong

The six-step DAG plan expands scalar-transport and scalar-law implementation already packaged by the Qbar-category interface. Reuse that interface rather than restating or reproving its obligations here. The current blueprint proof also calls j_E Qbar-linear, although its source has only E-linear Homs; the already-published assigned statement correctly asks for additivity and E-homogeneity. Its statement is unchanged. The unit record has no realized statement or steps to bypass; the common-stage, Verdier, and Karoubi route is retained.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
