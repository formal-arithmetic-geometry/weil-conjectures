## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.etaleSchemeMap_openImage` in the assigned
module, preserving its complete signature and both public imports. The proof applies
`AlgebraicGeometry.AlgebraicSpace.etale_open_image` to the existing `schemeSpace U`.
The only added project import is the private proof import
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, for that existing construction.
Added the private proof import `Mathlib.Topology.Category.TopCat.EpiMono` for the
surjective open-immersion test over a field spectrum.

The proved private helpers paste, cancel and base-change the representing pullback
squares; establish the sheaf property of a representable presheaf over a sheaf;
bundle an open subfunctor as an algebraic space using its diagonal and an atlas;
and handle the two directions of the field-extension condition. The subfunctor
and its structure maps are the ones supplied by the general open-image theorem.
No arbitrary presheaf data are chosen from an existence assertion.

Updated the item's existing DAG proof, proof dependencies and proof origin to
include the actual scheme-space construction and the explicit bundling and field
calculations. No statement, definition, source-library module, public import,
consumer or unit realization changes. The static preflight classifies the added
`CategoryTheory.Limits` opening and proof elaboration options as an environment
change; `coord/changes/EtaleSchemeMapOpenImage.md` records the original and new
commands and the downstream audit. No consumer adaptation is required.

Remote compilation after removing the unused experimental imports passed without
errors or warnings (7.9 seconds). An axiom print for the public theorem lists
`propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`: the latter is
expected from the existing general open-image theorem and scheme-space property.
All newly written helpers have complete proofs; delivery preflight checks them
individually. The public theorem is proved from the stated library dependencies,
not yet an unconditional theorem with its dependencies closed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.AlgebraicSpace.etaleSchemeMap_openImage`
(node `lem-a1-etale-scheme-map-open-image`).

Holes added: zero. Holes remaining in the delivered module: zero. Split off: zero.
No other module is delivered or changed. Existing dependency holes used are
`AlgebraicGeometry.AlgebraicSpace.etale_open_image`
(node `lem-a1-space-etale-open-image`) and
`AlgebraicGeometry.AlgebraicSpace.schemeSheaf_isAlgebraicSpace`
(owned also by `def-trf-scheme-algebraic-space`).

## No longer needed

No baseline import, declared proof dependency, node or module is pruned: the proof
retains `lem-a1-space-etale-open-image`, as the plan requires. Within its conclusion,
the point-image equality, topology, base-change and compactness clauses are unused.
The displayed field equivalence is proved directly from scheme-test surjectivity
and the open inclusion, so no additional point-class quotient calculus is required.

Removed experimental proof imports of
`Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`,
`Mathlib.CategoryTheory.Sites.Subsheaf`,
`Mathlib.CategoryTheory.Limits.Types.Pullbacks`, and
`Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks` before validation.
These were not baseline imports. No withdrawal is requested.

## Where the brief, the DAG or earlier work was wrong

The planned specialization is mathematically correct. Its existing Lean interface
returns an open subfunctor rather than a bundled algebraic space, so specialization
alone does not elaborate: the sheaf property, representable diagonal and scheme
atlas must be constructed. These are now proved in private helpers. The existing
`schemeSpace` construction is reused from its actual module, rather than restated.
Only this generic scheme-as-algebraic-space construction is used from the enlarged
site module; none of its topological, cohomological, trace-formula or duality results
is used. The added DAG dependency is its definition node
`def-trf-scheme-algebraic-space`, not the enlarged-site comparison theorem.

The field condition does not require extracting a direct relation from equality
in `Quot`. In the forward direction test the surjective factor over Spec K and use
a point's residue field. In the reverse direction the representing open scheme
has an L-valued point, hence its open immersion into the singleton Spec K is
surjective and an isomorphism. The code proves exactly the original condition.
This works for an empty U, an empty image, an open immersion, a surjective atlas,
and sections that lift only after a nontrivial field extension. No separation,
quasi-compactness, algebraic closedness or rational-point assumption is introduced.

Sources read: Stacks `spaces-properties.tex`, Tag 06NF,
`lemma-etale-image-open`; the existing general open-image node and module; the
scheme-space definition node and its two existing declarations; Mathlib's Yoneda,
fppf subcanonicity over S, pullback pasting/cancellation, residue-field construction,
full faithfulness of Spec, and `IsOpenImmersion.isIso`. The unit's `realized` lists
are empty for this auxiliary branch, and the planned general theorem is retained.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
