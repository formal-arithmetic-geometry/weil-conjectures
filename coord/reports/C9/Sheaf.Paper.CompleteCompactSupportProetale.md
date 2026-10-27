## What changed

Filled the section-normalized restriction unit, its inverse-image comparison, and the
Cartesian inverse open comparison in `Sheaf.Paper.CompleteCompactSupportProetale`.
A private coefficient-counit calculation reduces completed scalar compatibility to the
finite projections and constant sheafification. The site adjunction then supplies the
restriction/direct-image adjunction. Uniqueness of left adjoints identifies its unit
transpose with the published comparison. The inverse open comparison uses the invertible
open unit and the ordinary Cartesian open exchange to identify its target in the
essential image of fully faithful open extension.

Added the proof-only import `Sheaf.Paper.CompletedFiniteExchangeCoordinates` with
`import all` for its existing private finite projection and normalization lemmas.
Moved the already proved open-unit theorem before the inverse-comparison theorem so the
latter can use it. Public signatures and all definition bodies are unchanged.
The theorem node records these arguments and their finite-coordinate dependency.

Validation: `lcompile.py` compiled the delivered module successfully in 29.7 seconds
with no compiler diagnostics. The first delivery attempt with this revision returned
`DELIVERY BUSY` before checking or pushing the packet; it is being retried unchanged.

## Proved and sorry left

The packet replaces 3 of the 11 original holes with proofs:
`cbcRestrictionUnit_existsUnique`, `cbcPullToRestriction_isIso`, `cbcBetaInv_isIso`.
No holes added or split off.

The remaining eight holes, all attached to `thm-cbc-complete-proetale`, are:

- `cbcOpenToPush_isIso`
- `completeCompactSupportProetale_identity`
- `completeCompactSupportProetale_horizontal`
- `cbcRefinementMap_isIso`
- `completeCompactSupportProetale_compactifications`
- `completeCompactSupportProetale_refinement`
- `completeCompactSupportProetale_vertical`
- `completeCompactSupportProetale_composition_refinement`

## No longer needed

None. No original imports, declarations, nodes, or modules are withdrawn. The finite
coefficient argument reuses the existing coordinate lemmas. The remaining strict-tower
coherence dependencies remain needed by the retained obligations.

## Where the brief, the DAG or earlier work was wrong

The item has 11 holes in the current source. The strict-tower realization module
`Sheaf.Paper.CompleteProetaleStrictTowerRealization` imports this item to use its open
adjunction comparison. `Sheaf.Paper.CompletedOpenStrictMateIdentification` imports that
realization module. Consequently the DAG plan's imports of these two modules back into
this item would create Lean import cycles. No such import was added. The current
blueprint also records a condensed integral-coefficient reformulation in
`blueprint_update`; this packet preserves every published target and helper signature.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
