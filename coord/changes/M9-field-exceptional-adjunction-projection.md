# AlgebraicGeometry.ProEtale.FieldExceptionalSystem.Adjoints projections (withdrawn)

## Reason

The delivery proposed turning the four `abbrev` projections Adjoints.right, adj, finite and
evaluation of the unclaimed module Sheaf.Paper.FieldExceptionalSystemAdjoints into typed
`def`s, to shorten compile time. The independent reader (2026-10-26) withdrew this change
and restored the published module verbatim. The change was not needed. In a sandbox rebuild
against the published `abbrev` projections, the delivered Domains, the delivered new modules
and the delivered item compiled. The item took 45.1 s, Arrows 32.6 s and the published
FieldPurityTransposeLevelWords 35.4 s, all under the 60 s gate. The change also made the four
projections non-reducible in an interface with thirteen downstream users. Its users table
left out M3's FieldExtensionTowers, N1's FieldOrientationSystemComparison, and the unclaimed
FieldOrientationSystemCoordinates, FiniteOrientation and Normalizations.

## Old

The published Sheaf.Paper.FieldExceptionalSystemAdjoints (four `abbrev` projections).

## New

Identical to Old: this delivery does not change the module.

## Users

None affected: no signature, body or attribute changes.

## Status

landed 20261026T070331-L-3547379 2026-10-26 (merge of deliver/M9/Sheaf.Paper.FieldExceptionalSystemComparison)
