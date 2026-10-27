## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.FpqcCartierIdealReflection`
with a proof following the four-step route. Flat tensor-to-extended-ideal comparison
provides the specified inclusion-compatible isomorphism. Existing effective-Cartier
and sheaf-module comparison lemmas give rank one on the cover. Fixed-rank fpqc
descent applies to the original module and its canonical descent datum. Finally,
a local free generator maps under the ideal inclusion to a nonzerodivisor generator.
No statement, public import, definition, or existing external module changes.

Added private proof imports of `WeilConjectures.AlgebraicGeometry.EffectiveCartier`
and `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`.
Updated the item's proof steps, proof dependencies and proof origin to match Lean.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.fpqc_cartier_ideal_reflection`
(node `lem-trf-fpqc-cartier-ideal-reflection`). No holes added or split off.
There are no remaining sorry declarations in the delivery.
The theorem uses the library's existing descent and tensor-comparison declarations.

## No longer needed

Removed the private import
`WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage` and the
item's direct dependency and tool-use entry
`lem-pc-closed-subscheme-base-change-ideal-image`. The Mathlib equality
`Scheme.IdealSheafData.ker_fst_of_isClosedImmersion`, transported by pullback
symmetry, identifies the kernel with the extended ideal directly. The tensor
comparison then supplies the required inclusion-compatible isomorphism.
This is pruning of this item's direct route, not withdrawal of that source module
or a claim that its other consumers no longer need it.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned regular-generator calculations and descent argument are valid.
Step 1's separate ideal-image theorem is unnecessary because Mathlib already
identifies the kernel ideal under base change. The existing theorem
`IdealSheafData.IsInvertible.isInvertible_toModules` supplies step 2.
The general fixed-rank descent API also derives quasi-coherence from the covering
components, so no additional ideal quasi-coherence theorem is needed.
The unit route and all statement hypotheses and conclusions are preserved.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
