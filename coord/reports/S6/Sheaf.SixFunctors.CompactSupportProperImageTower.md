## What changed

The unchanged theorem `WeilConjectures.CompactSupportProperImageTower.compactSupportProperImageTower`
is reduced to the independent open-extension quotient square in the new module
`Sheaf.SixFunctors.IntegralOpenReductionQuotientSquare`. Its proof extracts normalized
finite direct-image data from `compactSupportSystemEvaluationCoherence`, obtains the
open-reduction comparison from `integralOpenReductionComparison`, applies the open
quotient square, and performs the direct-image and completed-restriction naturality
calculation. A proved private helper uses `NatTrans.ofOpSequence` and componentwise
invertibility to construct the requested tower isomorphism with exactly the beta
components. All existing public statements and constructions are preserved.

The item node now records this route. The new result is only about an open immersion:
it has no proper direct image, compactification, tower on Y, beta, or tower isomorphism.
It isolates the genuine Step 1 quotient-normalization result, rather than renaming
the item. The remaining combination in the item is actual Lean category algebra.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.CompactSupportProperImageTower.compactSupportProperImageTower`
(node `lem-sf-compact-support-proper-image-tower`). Added one hole:
`WeilConjectures.integralOpenReductionQuotientSquare`
(node `lem-sf-integral-open-reduction-quotient-square`). No other holes are added,
and the item module has zero remaining holes. This is a decomposition, with one
hole closed and one added; it is not a net proof or a claim of axiom-free closure.
The input coherence and open-comparison theorems already exist and retain their
own proof obligations.

The new theorem has a complete source-based proof in its docstring and node.
The ordinary scalar/open comparison is already proved in
`Sheaf.CategoryTheory.RingedOpenScalarAdjunction`. A separate scratch probe also
compiled its transport through the specified finite equivalences, including the
finite ring square from system-map naturality. The remaining work is the generator
normalization, localization and cancellation of the strict-model representative
equations. No incomplete proof fragments or private sorries are delivered.

Validation: the new statement module compiled in 8.5 seconds and the final item
module compiled without warnings in 13.9 seconds through lcompile.py. The source
theorem signature and all existing public imports are preserved verbatim.

## No longer needed

Removed the unused proof imports
`Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`,
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`,
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, and
`Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`.

The item's proof no longer directly needs
`lem-sf-varying-coefficient-composite-sequences`
(`Sheaf.CategoryTheory.VaryingCoefficientCompositeSequences`) or
`lem-sf-derived-coefficient-sequence-realization`
(`Sheaf.CategoryTheory.DerivedCoefficientSequenceRealization`): the short naturality
calculation and the Mathlib sequence constructor replace their generic bundles.
It also no longer uses `lem-sf-compact-support-restriction-of-scalars`,
`lem-weil-proetale-direct-image-restriction-of-scalars`,
`def-weil-l-adic-coefficient-extension`, or
`def-weil-integral-derived-restriction-of-scalars` as separate proof steps;
the definitions required by the statement remain, and the normalized direct-image
comparison comes from the existing evaluation-coherence witness. Removed the
obsolete direct-image node from the top-level `tool_uses`, retaining the order of
the remaining approval. These are dependencies removed from this argument, not
claims that their modules have no other consumers. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old Step 1 describes the open quotient equation in words, but its existing
Lean dependencies do not directly expose the equation with the actual adjunction
transposes and the standard exact-localization square used by this item.
`IntegralOpenReduction.Comparison.strictModel` exposes strict representatives;
turning their horizontal naturality into this specific derived equation is the
remaining independent result. The new node makes that missing interface explicit.

The original generic composite-sequence and realization route is unnecessary:
a naturality rewrite for the direct-image coefficient comparison, followed by
naturality for the successive completed restriction, proves the required equation
without constructing two extra bundles.

The evaluation-coherence theorem is used as a tool for its normalized direct-image
data in independent site/coefficient universes. Its node is
`lem-trf-compact-support-system-evaluation-coherence`. I checked that its DAG
closure has no path back to this item, and the import-direction check accepts its
module. Any tool-use approval belongs to the maintainer; none was added here.

## New nodes

`lem-sf-integral-open-reduction-quotient-square` in
`dag/nodes/sec-smooth-purity/lem-sf-integral-open-reduction-quotient-square.json`
states the generator-normalized open scalar comparison and its compatibility with
the actual consecutive derived quotient arrows. Sources are Stacks 0E8I and 0GL1,
with the specified strict representatives and scalar adjunctions already recorded
by the open-reduction comparison and coefficient calculus. The empty open,
identity open, zero complex, n=0 (positive exponent one), and unbounded complexes
are covered by the same direct-sum and degreewise argument. Mathlib searches and
a whole-blueprint search found no matching result. There is no definition or
statement change, so no change record is required.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
