# Reuse upstream local perfect-model transport

## Reason

The assigned module is quarantined after the upstream sync. Its rework row records
an unsolved universe constraint at line 171, from an implicit module-sheaf universe.
The adopted upstream twin already contains the complete proof with the required
explicit `SheafOfModules.overFunctor.{u}` annotations. Reuse it rather than restoring
a second declaration with the same name.

## Old

`quarantine/Sheaf/AlgebraicGeometry/SchemeIsoPerfectLocalTransport.lean` declares
`AlgebraicGeometry.Scheme.scheme_iso_local_perfect_transport` and the private
`localRestrictionSquare`, importing PerfectComplex publicly and DerivedPullbackPerfect
and SchemeIsoDerivedRestrictionSquare privately. The public theorem's local model
uses `SheafOfModules.overFunctor` without an explicit universe.

## New

Restore `lean/Sheaf/AlgebraicGeometry/SchemeIsoPerfectLocalTransport.lean` as a public
re-export of `WeilConjectures.AlgebraicGeometry.SchemeIsoPerfectLocalTransport`.
The same theorem name is available from its official defining module. The DAG node
`lem-pc-scheme-iso-perfect-local-transport` points to that module and records its
verbatim signature, including the explicit module-sheaf universe. The mathematical
hypotheses and conclusion and the three-step proof route are unchanged. No upstream
file is edited and no public declaration is duplicated.

## Users

Source scanning finds no current library or quarantine importer of the Sheaf module.
`WeilConjectures.AlgebraicGeometry.SchemeIsoPerfectTransport` already imports the
upstream theorem directly. Its proof was checked in a separate sandbox example with
that import replaced by the restored Sheaf re-export; it compiles unchanged.
No consumer requires an adaptation and no target statement or definition changes.

## Status

landed 20261020T154052-L-3040495 2026-10-20 (merge of deliver/R7/Sheaf.AlgebraicGeometry.SchemeIsoPerfectLocalTransport)
