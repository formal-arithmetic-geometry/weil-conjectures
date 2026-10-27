## What changed

Filled `AlgebraicGeometry.ProEtale.properOpenRefinementAlpha_plus_inclusion`
without changing its statement or public imports. The proof first compares exact
localized squares across the bounded-below inclusion, then identifies the sheaf
alpha with the existing `AmbientClopen.alpha` and applies
`AmbientClopen.ordinary_alpha_localized`. Private helpers prove all comparison
and cancellation steps. Updated the item node to record this route.

Added proof imports of `FiniteClopenAlphaSiteTransport`,
`EtaleClopenMateNormalization`, `AmbientOrdinaryClopenLocalization`, and
`AmbientAdjunctionCompositorNormalization`. Their proved private normalization
helpers are accessed with `import all`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.properOpenRefinementAlpha_plus_inclusion`:
1 of 1 original holes closed. No holes added or split off; no `sorry` remains in
the delivered module. All private helpers have complete proofs.

Validation: `lcompile.py` compiled the complete delivered module cleanly in 8.5 s
(no errors or warnings), with profiling options removed.

## No longer needed

No existing public imports or modules are removed. No new geometric localization
lemma is needed: the already proved `ordinary_alpha_localized` supplies the full
clopen projector and compositor calculation. No original declared dependency is
withdrawn; its constructions or normalization results remain used.

## Where the brief, the DAG or earlier work was wrong

The planned factorwise clopen calculation already exists in
`Sheaf.SixFunctors.AmbientOrdinaryClopenLocalization`. Reusing it avoids repeating
that argument or splitting this obligation a third time. The remaining gap was
identifying the two sheaf words and proving that exact localized squares commute
with the bounded-below inclusion. No statement, definition, or unit route changed.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
