## What changed

Proved `AlgebraicGeometry.Etale.sfGraphMiddleIso_projection` by the prescribed
graph-intersection argument. The two inner proper/open squares, open projection
composition, and pullback-composition coherence give the intersection square.
Naturality pastes the common outer proper projection. Private lemmas handle
inverse, composition, associators, whiskering, and the exact graph-word coefficients.

Added `Sheaf.AlgebraicGeometry.ProperOpenFactorProjection`, with a complete proof of
`AlgebraicGeometry.Etale.properOpenFactor_projection`. This is the identity-top
specialization of the proper/open tensor square. It reuses the proved private
`mixed_projection` from `CompactificationProjectionComposition`, through `import all`,
and the proved identity-pullback tensor calculation from `SfEtaleGraphTransferTensor`.
The identity normalization follows the specified adjunction unit/counit formulas.

The pullback objects, coefficient comparison, and outer tensor pasting are constructed
for a general coefficient category before specializing to `ModuleCat A`. This keeps
`HasSmallSiteSheafify` certificates shared and avoids the kernel timeout caused by
rebuilding these terms directly over module sheaves. A proved equality identifies the
private generic graph-word construction with the existing `sfGraphWordProjection`.

Updated the item's proof route and added the fully proved factor-square node.
Existing public signatures and definitions are unchanged. No consumer adaptation
or definition-change record is required.

Repair of the 2026-10-26 global-build return: restored the returned packet and
updated `word_strength_source` to unfold `sfGraphProjectionWord` as well as its
`sfGraphWordProjection` wrapper. The wrapper now delegates to that generic definition;
the previous simplification stopped at the delegation. The current-body branch removes the obsolete associator simplification arguments;
a fallback retains the original normalization for the older published inline body.
The initial repair compile confirmed the published build still lacks the new generic
declaration. Both branches prove the same unchanged equality. No signature changed.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Etale.sfGraphMiddleIso_projection`.
The new `AlgebraicGeometry.Etale.properOpenFactor_projection` is also fully proved.

Holes closed: 1. Holes added: 0. Unresolved statements split off: 0.
There are no remaining `sorry` declarations in either delivery module.

The repair's graph proof compiled against the published build in 28.5 seconds;
the factor theorem compiled in 35.6 seconds. Both axiom audits report exactly
`propext`, `Classical.choice`, and `Quot.sound`. The version-dependent private
normalization helper locally disables the unused/unreachable tactic linters, since
one complete branch is intentionally inactive on each version of the wrapper.
The delivery command repeats the combined compilation and per-declaration axiom checks.
The item's signature matches the repository's signature, and the new node's Lean
statement matches its declaration.

## No longer needed

Removed the planned proof dependency `lem-sfb-ringed-derived-monoidal-comparisons`
(`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`). The concrete
`UpperStarCompCoherence` identities and the proved identity-pullback tensor lemma
supply the required coherence. This module was never imported by the original item.

Replaced the direct planned dependency `lem-sf-etale-proper-open-tensor-square` by the
fully proved identity-top factor lemma. The public `etaleProperOpenTensorSquare` theorem
is not imported: its proved generic tensor-square calculation, `mixed_projection`,
is reused directly. The existing source proper/open comparison is retained.

Neither unused planned dependency is withdrawn from the library: other consumers
remain intact. Open projection composition, both graph presentations, and the unit's
route remain needed. No existing declaration or module is withdrawn. No import from
the original item was removed; both new private imports are used.

## Where the brief, the DAG or earlier work was wrong

The returned proof was checked against the old inline body of
`sfGraphWordProjection`. D9's landed generic construction preserved its components
but introduced one additional definition to unfold. The repair now follows that
construction explicitly, as in the maintainer's recorded dependency-repair patch.

The mathematical route in the node is valid. The generic ringed-comparison system
it listed is broader than necessary; the concrete source comparisons suffice.
No statement was weakened or disputed.

## New nodes

`lem-sf-proper-open-factor-projection`, at
`dag/nodes/sec-six-functors-basics/lem-sf-proper-open-factor-projection.json`,
records the fully proved identity-top proper/open projection square. It is one local
factor compatibility, strictly smaller than the assigned intersection of two factor
squares followed by open compositions and an outer proper image. It adds no hole.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
