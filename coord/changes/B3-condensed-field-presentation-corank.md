# B3: scalar evaluation interface and private corank proof helpers

Item: `Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank`.

## Reason

Reduce the common-fibre corank theorem to its geometric scalar evaluation step.
The original proof plan has no usable internal-module evaluation/matrix interface.
The new interface isolates that geometric construction while the parent proves
all finite-free coordinates, matrix equations, cokernel transport and rank-nullity.

## Old

The original module publicly imports only CondensedFieldPresentationMatrix and
contains the public theorem `condensedField_presentation_corank_eq` with one sorry.
It has no private coordinate helpers and no generic helper variable section.
The existing target definitions and theorem signatures are the old versions
unchanged; no signature or existing definition is being replaced.

## New

The existing theorem signature and original public import are unchanged. Its proof
now uses the new scalar evaluation interface and proved private helpers. Additional
universe names and `variable` commands are inside `section FiniteFreeCoordinates`,
which ends before the original theorem. All added declarations in the original
module are private. The `irreducible` attribute applies only to the new private
coordinate construction; its projection and single-coordinate API is proved.
These commands trigger the conservative interface scanner but add no public
declaration to the existing module and do not change existing target definitions.

The new module `Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation` states
one public theorem about compatible additive finite-colimit-preserving evaluation
functors, their regular-module coordinates and endomorphism scalar formulas. Its
one sorry is strictly a part of the corank argument. It has its own new DAG node,
source and proof in words. The parent proves the remaining argument from it.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | unchanged; no adaptation | Existing public signature and public import closure unchanged. |

This is the sole current direct importer and needs no adaptation.
All further importers likewise receive the same existing public declarations;
proof-only imports and private helpers do not enter their interfaces. The new
evaluation module is privately imported by the parent. Its pending proof imports
SitePullbackAbelianExact and GeometricFieldProEtaleEvaluation privately; the latter
publicly supplies ProfinitePointPullback. The continuous realization is already
public through PresentationMatrix. No other existing module,
claimed or unclaimed, is changed, and no target-definition review is reopened.

## Status

landed 20261016T025203-L-1450439 2026-10-16 (merge of deliver/B3/Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank)

This is a decomposition: one original hole closed and one strictly smaller
geometric-evaluation hole added. The implementation has passed the independent B3 second
reading recorded in report.md. Both modules compile without warnings through
lcompile --all after rebuilding the sandbox outputs against the published library. The original theorem signature and public imports
were compared byte for byte, and the parent node changes only proof, proof_deps
and proof_origin. No compilation limit was raised.
