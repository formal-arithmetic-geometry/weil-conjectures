## What changed

Repaired the returned delivery `ebce3b65641`. Its global build failed with:

```
a non-private declaration `AlgebraicGeometry.ProEtale.supportComparison_eq`
has already been declared
```

The current `Sheaf.SixFunctors.ComparisonOpenTensorCoherence` exports that lemma
publicly. Removed the duplicate private declaration from the returned proof. Its comparison
equality is now a local `have hsupport` inside the assigned theorem proof, used
in the final comparison normalization. This avoids a declaration-name collision
regardless of whether the imported helper is public or private.
The inverse-direction square and the projection-isomorphism cancellation argument
are retained. This addresses the reported global failure without changing any
statement, definition, public import, or consumer.

The dispatcher sandbox contained only metadata on restart, despite the repair brief
saying the delivered sources were retained. Reconstructed the returned proof and
DAG update from the preceding session record against the current shared source.
Compared with the returned implementation, the substantive repair is replacing
the duplicate helper declaration by a proof-local fact; compared with current main, the original single hole is
filled and the proof route is recorded in the DAG.

The proof-only imports are `Sheaf.SixFunctors.ComparisonOpenTensorCoherence` and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
The latter provides the natural-isomorphism inverse compatibility used when
expanding the canonical restriction comparison. The unit route is preserved.

Validation: single-file server compilation through `lcompile.py`; final delivery
also runs the server preflight. No local Lake or global build was run.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.openProjectionTransport_projection_square`
(node `lem-pur-open-projection-comparison-square`).

Zero holes remain in the item, zero holes are added, and zero statements are
split off. The comparison equality is proved locally inside the theorem; no helper
declaration is added.

## No longer needed

Removed the duplicate private `supportComparison_eq` from the returned version.
A proof-local fact `hsupport` supplies the equality without adding a declaration.

The original proof imports `Sheaf.AlgebraicGeometry.OpenComparisonTensorNormalization`
and `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison` are unnecessary here:
`comparison_open_tensor_coherence` already proves the inverse-direction derived
square with the canonical comparisons. Their nodes
`lem-sf-open-comparison-tensor-normalization` and
`lem-cbc-proetale-extension-zero-comparison` are no longer direct proof dependencies
of this item. The canonical extension isomorphism itself stays available through
the unchanged public source imports. No module or node is withdrawn, and other
users and the reused theorem's dependencies remain.

## Where the brief, the DAG or earlier work was wrong

The returned proof duplicated a helper that became public in an imported module.
The prior isolated compile accepted the then-private name, but the global build
correctly rejected it against the newer public declaration. This repair replaces
the duplicate declaration by a local fact. The compile server initially did not
expose the newer public helper, so using that public name directly was insufficient.
The local proof works with either version of the imported module.

The original DAG plan needlessly repeated the mate and tensor argument already
proved by `lem-sf-comparison-open-tensor-coherence`. The repaired DAG records the
same shorter route as the returned delivery: identify its canonical comparisons,
then cancel the two projection isomorphisms. The assigned statement is unchanged.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
