## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PicardTermwiseModelComparison.lean` from
its quarantined source and retained the complete proof of
`AlgebraicGeometry.Scheme.picard_termwise_model_comparison`. The proof constructs
the restricted chain map by termwise pullback and the canonical source and target
restriction isomorphisms, proves its degree-zero component, and combines the
source and target coherence equations with counit naturality. Its imports now
refer to the current `WeilConjectures.AlgebraicGeometry` source modules after the
source-tree retirement of duplicate `Sheaf` copies.

## Proved and sorry left

The declaration `AlgebraicGeometry.Scheme.picard_termwise_model_comparison`
(node `lem-sc-picard-termwise-model-comparison`) is proved with no `sorry` left.
This delivery adds no declarations and leaves no `sorry` in the item module. It
closes one existing hole and splits off zero holes.

## No longer needed

No proof dependency used by the retained route was removed. The proof does not
need direct imports of `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` or
`Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf`; the required counit and
flatness facts are supplied through the existing coherence declarations and the
current `WeilConjectures` source modules. No DAG node or module is pruned by this
restoration.

## Where the brief, the DAG or earlier work was wrong

The prior delivery was reverted by the merge queue during the cluster restore,
while its proof remained valid. The quarantined module therefore needed to be
restored verbatim at the proof level, with only imports adapted to the current
source-tree module names. The theorem statement and its DAG node are unchanged.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
