## What changed

Proved `AlgebraicGeometry.WeilComplex.native_pullback_star_preservation` without changing its
signature. The native library already constructs `WeilComplex.upperStar` with a preservation
witness and proves `WeilComplex.objectProperty_rightDerivedLowerStar`. Extracting the first
witness and applying the second theorem proves the two preservation clauses. The inclusion
identities are both `rfl`, hence identify morphisms as well as objects. No source-library file,
definition, public import, or target was changed.

Updated the declaration's proof description and its existing DAG node to record this shorter
native route. The unit `sk-prop-sf-biduality-general` has no realized steps to bypass; the
biduality argument still receives exactly its required native preservation statement.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.WeilComplex.native_pullback_star_preservation`
(node `lem-sf-native-weil-pullback-star-preservation`). Added 0 holes; split off 0 statements.
There are no remaining `sorry` declarations in the delivered Lean file. This counts the local
hole closed, not a claim that every transitive dependency of the native preservation theorem
is sorry-free.

Validation: `lcompile.py` compiled the proof with only the unchanged public import of
`WeilConjectures.WeilSheaf.LowerShriek` in 5.2 seconds, exit code 0, no warnings. The delivery
tool performs the final compile and preflight. The proof also covers the zero complex and the
empty scheme: no nonzero or nonempty witness, finite rank choice, or additional hypothesis is
used.

## No longer needed

Removed all private imports from this module:

- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.Paper.LocallyFiniteCoefficientRingRealization`
- `Sheaf.Paper.NativeEncodingDerivedOperations`
- `Sheaf.Paper.NativeForgetConstructibleCriterion`
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`
- `Sheaf.SixFunctors.CtfStabilityDirectImages`

The following former direct proof dependencies are unnecessary for this native assembly:

- `lem-pod-separated-finite-type-base-change`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-qcqs-over-affine`
- `lem-sf-locally-finite-coefficient-ring-realization`
- `lem-sf-native-encoding-derived-operations`
- `lem-sf-native-forget-constructible-criterion`
- `sk-def-sfb-qlbar-condensed`
- `det-thm-sf-ctf-stability-direct-images`

The old geometry checks served the coefficient-realization route. The existing native
preservation theorem already checks its own geometric hypotheses; the pullback witness is
already present in the restricted construction. Neither coefficient realization, operation
comparison, predicate reflection nor the general coefficient stability theorem is used here.
Only `def-sf-native-weil-derived-framework` remains as the direct DAG dependency.

Withdrew all 13 obsolete top-level `tool_uses` approvals in their original order:
`lem-pod-separated-finite-type-base-change`,
`lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-qcqs-over-affine`,
`lem-sfb-totally-disconnected-coefficient-realization`, `sk-prop-sfb-qlbar-colimit-x`,
`lem-pd-module-ringed-topos-derived-comparison`, `sk-prop-sfb-cartesian-coefficients`,
`sk-lem-coefficient-heart`, `det-def-localizing-closure-ctf-equals-bc`,
`lem-weil-pbc-ring-sheaves-grothendieck`, `lem-sf-fixed-pair-derived-forget-comparison`,
`det-thm-sf-ctf-stability-direct-images`, and
`lem-sf-locally-finite-coefficient-ring-realization`.

These are removals from this module's direct route, not withdrawals of their modules or a
claim that other consumers, including native source proofs, no longer need them. No Lean
module or declaration is deleted.

## Where the brief, the DAG or earlier work was wrong

The planned coefficient-realization argument duplicates preservation already encoded in the
existing native full-subcategory functors and in the native direct-image preservation theorem.
The source references of the node itself identify these constructions. The requested statement
is unchanged, and no mathematical error in the longer route is asserted.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
