## What changed

The item module now assembles `tensorComparison_coherence` from two named strict
components: `tensorComparison_coherence_associator` and
`tensorComparison_coherence_unit_symmetry`. The compositor theorem is assembled from named normalized descent and tensor components, preserving its original interface.

## Proved and sorry left

The existing `finiteDerivedComparisonNormalization` proof and
`coefficientComparison_identity_successive` proof remain complete. The original `tensorComparison_coherence` and `tensorComparison_composition` holes are closed by real conjunction and uniqueness assembly. Four strictly smaller named component holes remain: `tensorComparison_coherence_associator`, `tensorComparison_coherence_unit_symmetry`, `tensorComparison_composition_descent`, and `tensorComparison_composition_tensor`; each has a node in `dag/nodes/sec-smooth-purity/`. The existing `tensorComparison_coefficients` hole remains unchanged.

## No longer needed

The proof no longer needs the unavailable `RingedKFlatWord.comparison_descent_iso` call or the local proof route that invoked it. The parent node records the four component nodes used by the assembled statements. No imports were removed.

## Where the brief, the DAG or earlier work was wrong

The source module called `RingedKFlatWord.comparison_descent_iso`, but the adopted
word-comparison module exposes only `descent_existsUnique`; the former identifier
is unavailable in the compiled environment. The compositor source proof referred to an unavailable identifier; the delivery replaces that local route with two strictly smaller named components while leaving the public theorem statement unchanged. The brief's requirement that each split statement have its own
module could not be met without introducing an import cycle, because all four
components use definitions introduced earlier in this item module; they are named
public declarations with matching nodes in the item module.

## New nodes

The delivery adds `lem-pur-finite-derived-comparison-normalization-associator`, `lem-pur-finite-derived-comparison-normalization-unit-symmetry`, `lem-pur-finite-derived-comparison-normalization-composition-descent`, and `lem-pur-finite-derived-comparison-normalization-composition-tensor`.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
