## What changed

Filled all six theorem proofs in `Sheaf.Paper.FiniteSiteTowerPaste`. The proof
restricts the proper/open word along the fully faithful D+ inclusion and identifies
the resulting unbounded word with the compositor for the supplied compactification
triangle. It pastes the specified site square and the proper/open compositor
squares, derives the inverse formula, and proves all three naturality statements.

Added the proof import `Sheaf.Paper.FiniteSiteWordRefinement`, and private access
imports for the existing proved APIs in `ProperOpenCoefficientMate` and
`UnboundedEtaleCompactSupportComparisons`. Every original public import, definition,
and theorem statement is preserved. Updated the existing node's proof and proof
origin to record the implemented calculations. Validation: the full module compiled cleanly through `lcompile.py` in 37.2 seconds,
with no warnings and no `sorry` in the item. No other module is changed. The private unbounded formalism instances are
registered locally; no instance is exported.

## Proved and sorry left

Closed all six original holes, with namespace prefix
`AlgebraicGeometry.ProEtale.FiniteSiteTower`:

- `etale_normalization`
- `etale_compositor_normalization`
- `paste`
- `paste_naturality`
- `word_naturality`
- `comparison_naturality`

Item holes: 6 before, 0 after. Holes added: 0. Split-off statements: 0.
All private helpers are proved. The proof uses the existing stated
`finiteSiteWordRefinement` theorem; this delivery does not claim to close its hole.

## No longer needed

No original import, module, or dependency node is pruned. All four declared proof
dependencies remain needed. The word equation cancels the explicit transport
isomorphism and its inverse, so a separate naturality result for the pro-etale
interchange is unnecessary. Naturality of AP follows by cancellation of D from the
named-map equation, avoiding a separate adjunct-naturality calculation.

## Where the brief, the DAG or earlier work was wrong

No statement correction is required. For invertibility alone, AE is already a
composite of the specified interchange isomorphism and two compositor
isomorphisms. Thus the final invertibility argument need not invoke unbounded
normalization. The required unbounded normalization is nevertheless proved in full
for the supplied compactifications, preserving the unit route.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
