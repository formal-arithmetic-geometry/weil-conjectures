## What changed

In `Sheaf.Paper.RationalRestrictionComparisonCoherence`, prove
`tensorComparison_existsUnique` by the existing generic bilinear localization
isomorphism theorem in `DerivedPullbackTensorHom`. Its two hypotheses on arrow
actions follow by postcomposing or precomposing the recorded tensor bilinear map
with additive rational pullback. The inverse formula follows from the hom formula
and the integral mapIso inverse.

Move existing private pullback and tensor helpers earlier in the same file for
use by this proof. All declaration signatures, definitions and imports stay
unchanged. A proved private generic helper assembles the bilinear-map hypotheses
before specializing them to the large coefficient categories.
Update step 5 and proof_origin of the existing node to record the proof.

## Proved and sorry left

Of the four original direct holes, close one (no holes added):

- `WeilConjectures.RationalRestrictionComparison.tensorComparison_existsUnique`.

Three existing holes remain, all attached to
`lem-pur-rational-restriction-comparison-coherence`:

- `WeilConjectures.RationalRestrictionComparison.mixedSquares`.
- `WeilConjectures.RationalRestrictionComparison.identityCoherence`.
- `WeilConjectures.RationalRestrictionComparison.towerCoherence`.

Their existing source/proof docstrings and DAG steps 6–7 are retained. This is a
partial proof delivery, with no decomposition and no new sorry statements.

## No longer needed

None. No imports or dependency nodes are removed. The generic bilinear extension
argument is already proved in an existing imported module, so its naturality proof is reused; the private helper only composes the given
bilinear actions with the given additive pullback action. The
planned integral conjugation route for identity and tower coherence remains.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The generic private bilinear
localization theorem already available through the existing `import all` gives
a shorter implementation of the tensor-comparison construction. The current
blueprint has moved the operation definition to
`sec-proetale-coefficients/sk-prop-sf-open-closed-triangle`; it now describes the
condensed-coefficient interface, while this item's existing recorded statement
and raw-localization subargument concern the integral-model interface. This
delivery preserves that recorded interface and all hypotheses.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
