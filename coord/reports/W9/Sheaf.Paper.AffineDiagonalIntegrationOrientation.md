## What changed

Repair of returned delivery `6aa69f4d869` (reviewer `C-6aa69`). The reviewer passed
the mathematics; landing failed because `--apply-fixes` named the bare report filename
`Sheaf.Paper.AffineDiagonalIntegrationOrientation.md`, which is not a delivery path.
The report belongs at
`coord/reports/W9/Sheaf.Paper.AffineDiagonalIntegrationOrientation.md`;
`deliver3.py` installs this sandbox's `report.md` there automatically. The retry uses
that standard packet layout and the delivery tool's freshly fetched `sheaf-dag` base.
There is no Lean build error in `coord/build-errors/` for this item. The retained
Lean changes were compared with current shared source; the four proof replacements
and eight private-import removals are still outstanding. No competing item edit
needs to be merged. No mathematical correction was requested.

The fresh repair compile exceeded 60 seconds. Profiling located deep expansion in
canonical comparison definitions used by the retained derived-map statements; the new
coordinate proofs each elaborate in under two seconds. Three imported comparisons are
therefore locally irreducible in this module after the product-chart proof:
`Etale.affineLinearCompactComparison`, `Etale.affineLinearCoefficientDescent`, and
`Etale.vectorIntegrationBaseCoefficientPullback`. These local attributes change no
public signature, construction, or exported reducibility setting. Development profiler
options were removed before validation.

Filled four existing theorem proofs in
`lean/Sheaf/Paper/AffineDiagonalIntegrationOrientation.lean`.
The diagonal differences lift uniquely through the actual ideal inclusion.
The product-coordinate map has an explicit inverse from the pullback universal property.
The recursive translation preserves the base and subtracts the given vector on every
coordinate; this proves the difference-coordinate isomorphism, its projection equation,
and its restriction to the zero section. Smoothness follows from the existing ordered-tower
isomorphism with affine space and invariance under isomorphisms.

All existing signatures, definitions, docstrings and public imports are preserved.
Private helpers prove the tower-coordinate and translation calculations. In particular,
the translation calculation proves its own projection equation rather than using the
unfinished `ambientAffineTranslation_lineSquare` theorem. No source-library module changes.
The arguments cover rank zero and arbitrary bases, including the empty scheme.

## Proved and sorry left

Closed 4 of the original 9 holes, all in namespace
`WeilConjectures.PurityFiniteSetting`:

- `affineDiagonalDifference_lift`
- `affineDiagonalProductCoordinates_spec`
- `affineDiagonalTranslatedCoordinates_spec`
- `affineDiagonalProjection_smooth`

The following 5 original holes remain unchanged, with node
`lem-pur-affine-diagonal-integration-orientation`:

- `affineDiagonalNormalCoordinates_spec`
- `affineDiagonalIntegration_translation`
- `affineDiagonalIntegration_exponent`
- `affineDiagonalIntegration_zero`
- `affineDiagonalIntegrationOrientation`

Added holes: zero. Split-off statements: zero. This is a partial proof delivery of a
module with multiple original holes, not a proof of the final orientation theorem.

## No longer needed

Removed the following private imports, which none of the completed proofs uses:

- `Sheaf.Paper.ProjectionFormulaCoefficientCoherence`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`
- `Sheaf.Paper.TraceTransposeBaseChange`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.PurityDncComparisons`
- `Sheaf.Paper.AffineTranslationTrace`
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`

These are import removals only. No node or module is withdrawn: the five remaining
obligations still follow the recorded integration, normal-coordinate and normalized-DNC
route. Its proof dependencies are retained in the DAG. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned packet exposed a landing-path error, not a rejected proof: the reviewer
fix named a bare report filename rather than its canonical delivery path above.
This retry documents the correct path and rebuilds the packet on current `sheaf-dag`.
The launcher and maintainer tools are unchanged.

No false mathematical statement found. The four geometric obligations admit direct
proofs from the existing affine-space, ideal-sheaf and fibre-product APIs. They require
no new intermediate statements and no change to the recorded mathematical route.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
