## What changed

Filled five existing proofs in `Sheaf.Paper.FiniteReductionComparisons`.
The pullback presentation uses its native isomorphism and uniqueness by HEq.
The coefficient square uses constant inverse-image naturality.
The ordinary coefficient-unit map is constructed sectionwise as a linear natural map.
The compact-support comparison uses the existing normalized
`finiteCompactSupportScalarComparison`, with original and reduced constructibility.
The exceptional comparison is constructed uniquely by the published counit Hom
bijection, transported through the intrinsic realization equivalences.

Added one proof-only import, `Sheaf.Paper.FiniteCompactSupportScalarComparison`, and
two proved private helpers. Updated the existing node's proof and proof dependencies.
All public signatures, definitions and public imports are unchanged.
The complete file compiles cleanly through `lcompile.py` in 35.7 seconds.

## Proved and sorry left

Closed five holes: `finiteReductionPullbackPresentation`,
`finiteReductionCoefficientSquare`, `existsUnique_finiteReductionUnitSectionMap`,
`finiteReductionCompactSupportComparison_isIso`, and
`existsUnique_finiteReductionExceptionalComparison`.

Added zero holes. Three existing holes remain:
`existsUnique_finiteReductionSourceComparison`,
`finiteReductionUnitComparison_isIso`, and
`finiteReductionExceptionalComparison_isIso`.
All belong to `def-pur-finite-reduction-comparisons`.
This is five proofs from existing declarations, not a decomposition into new holes.

## No longer needed

None. No imports, nodes or modules were removed. The original dependency list was
statement dependencies with an empty proof field; these remain needed by the definitions
and retained obligations. The normalized compact-support scalar comparison already has
the exact defining adjunct formula, so no new scalar-transport intermediate was needed.

## Where the brief, the DAG or earlier work was wrong

The existing node had no numbered proof plan. The coefficient-square argument is
immediately the existing constant inverse-image naturality theorem. The compact-support
hole can reuse the stronger existing normalized comparison requiring only bounded
constructibility of the input and actual reduction, supplied by the finite-Tor hypotheses.
The exceptional existence/uniqueness proof requires the class-restricted counit Hom
bijection, not an unrestricted ambient adjunction; the proof uses that restricted
bijection and `compositionInput_bounded` explicitly.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
