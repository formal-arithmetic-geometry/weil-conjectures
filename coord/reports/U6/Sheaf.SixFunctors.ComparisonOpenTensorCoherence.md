## What changed

Proved `AlgebraicGeometry.ProEtale.comparison_open_tensor_coherence` in
`Sheaf.SixFunctors.ComparisonOpenTensorCoherence`. The three existing public
signatures and the bodies of both public comparison definitions are unchanged.

The proof computes the underived mate of the literal open-restriction square,
localizes its unit equation, transports the existing derived tensor compatibility
along `L ≅ D`, and applies `CategoryTheory.Adjunction.projectionMap_mate`.
Cancellation of the projection and extension isomorphisms gives exactly the
published equality. Private helpers contain complete categorical proofs; no
additional mathematical assumption or chosen witness is introduced.

Added proof-only imports of `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique`,
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat`,
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison`.
Updated the item's node proof and dependencies to this route. The generic
projection-map theorem is already proved in the source library and recorded by
`lem-asd-adjunction-projection-map-mate`; its reuse needs no new node.
The unit's comparison-transport step is retained.

Validation: the complete proof compiled through `lcompile.py`; final clean-file
and delivery checks are recorded by the delivery tooling. No other module or
consumer requires adaptation because the public declarations are unchanged.
The static preflight flags command changes for private proof helpers; the record
`coord/changes/comparison-open-tensor-proof-commands.md` documents their scope and
lists both downstream modules.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.comparison_open_tensor_coherence`
(node `lem-sf-comparison-open-tensor-coherence`).

Actual holes remaining in the delivered module: 0. Holes added: 0. Split off: 0.
This is a proof, not a decomposition. Imported dependencies retain their existing
proof status; no dependency is replaced with a new assumption.

## No longer needed

Removed the proof-only import `Sheaf.SixFunctors.OpenTensorNormalization` and the
node dependency/tool approval `lem-sf-open-tensor-normalization`. The actual
projection isomorphisms are already defined by the required adjunction units,
counits and mixed tensorators. Their compatibility follows formally from the
mate and monoidal comparison equations, so the generic ringed-site normalization
construction and a fresh K-flat/pure-tensor/stalk calculation are unnecessary
for this item. Other parent modules may still use that normalization module.

All other declared dependencies are retained for the canonical operations,
exactness, comparisons, or projection isomorphisms. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original five-step plan was longer than necessary. The source library
already proves the required generic projection-map mate theorem and compatibility
of the derived comparison tensorators. The delivered proof uses these with an
explicit calculation of the prescribed restriction mate. The mathematical
statement, arbitrary-unbounded scope, coefficient universe and all hypotheses
remain unchanged. There is no disputed statement and no definition repair.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
