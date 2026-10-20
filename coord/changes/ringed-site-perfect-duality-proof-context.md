# Ringed-site perfect-duality proof context

## Reason

The completed proof of `CategoryTheory.ringedSitePerfectDuality` needs private
categorical helpers, separate slice derived-category universes, and controlled
elaboration of normalized coefficient presentations. Preflight classifies the
added section variables and local notations as a command-context change.

## Old

`Sheaf.CategoryTheory.RingedSitePerfectDuality` had universes `c v r w`, no
private proof helpers, and both backward definitional-equality transparency
options set to false. Its public theorem had one hole.

## New

The public theorem signature, universes, visibility and public imports stay
verbatim. Both backward transparency options are true. The proof uses an extra
private universe `w'`, local section notations `S`, `A`, `AU`, section variables,
private proved helpers, two explicitly constructed private natural isomorphisms,
a private comparison-data structure, and a private product-isomorphism instance
of priority 10. The final theorem has a scoped smaller heartbeat budget of
60000 to bound normalization-instance searches; the 60-second compile limit is
unchanged. The ordinary bounded-complex calculation is a new public theorem in
`Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom`, recorded by its new node.
Removed private imports are listed in the report. No existing mathematical
definition or public declaration signature changes.

Repair of returned head `9f5a5a6b895`: the optional `warn.sorry` command was
removed because the hole ledger interpreted its option name as an unattributed
hole at line 41. The proof and its theorem statements are unchanged by the repair.

## Users

The item `Sheaf.CategoryTheory.RingedSitePerfectDuality` is held by U6.
`tools/downstream.py Sheaf.CategoryTheory.RingedSitePerfectDuality --uses
ringedSitePerfectDuality` finds 338 downstream modules and no occurrence of the
theorem name outside its own module. The direct importers are:

- `Sheaf.Paper.FiniteTorStability`
- `Sheaf.Paper.SmoothPurityTowerP1Adjunction`
- `Sheaf.SixFunctors.InternalHomPullback`
- `Sheaf.Paper.SixFunctorDatum`
- `Sheaf.Paper.InternalHomPullback`
- `Sheaf.Paper.BasicOperationsCoefficientReduction`

They retain the same public theorem and public imports. The new section
notations are local and the additional declarations are private proof support.
No consumer adaptation is required or included. No source-library module is
changed. No target meaning is changed or reopened by this proof-context change.

## Status

landed 20261020T221355-L-4179459 2026-10-20 (merge of deliver/U6/Sheaf.CategoryTheory.RingedSitePerfectDuality)
