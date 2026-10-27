## What changed

Reduced `AlgebraicGeometry.ProEtale.AffineSpaceTrace.affineSpaceTraceFactorization`
to two strictly smaller canonical-map obligations and wrote the combining proof in Lean.
The dimension-one clause is the existing ordered-transpose projection theorem's unit
specialization. The successor clause uses an explicit last-line contraction, evaluates
it via the specified binary product, and moves the previous integration through tensor
and coefficient unitors by two proved private categorical lemmas.

The eight existing coordinate definitions move unchanged into
`Sheaf.Paper.AffineSpaceTraceProductData`, publicly re-exported by the item. This is
necessary for the new obligations to import them without a cycle. The new contraction and source isomorphism are irreducible caches to prevent
consumer elaboration from unfolding the full derived-functor construction. The contraction
is a real composition of source maps, the canonical inverse compositor, origin change,
inverse projection and the normalized line trace. It selects no data from an existence
theorem. See `coord/changes/D3-affine-space-trace-coordinates.md`.

## Proved and sorry left

Closed upper hole:
`AlgebraicGeometry.ProEtale.AffineSpaceTrace.affineSpaceTraceFactorization`.
This is a decomposition, not a net proof: one upper hole closed, two lower holes added.
The item module has zero remaining holes. The new holes are:

- `AlgebraicGeometry.ProEtale.AffineSpaceTrace.integration_successor_contraction`
  (`lem-pur-affine-space-trace-successor-contraction`), the ordered-comparison source
  and compactification matching in the composite transpose.
- `AlgebraicGeometry.ProEtale.AffineSpaceTrace.lastLineContraction_product`
  (`lem-pur-affine-space-trace-contraction-product`), the line-evaluation and binary
  product matching. It mentions no exceptional transpose or old-block integration.

The source is the current blueprint Integration paragraph and the corresponding
original node Steps 1--3. Each remaining theorem has a complete proof in words in its
docstring and its node. All new definitions have actual constructed bodies.

## No longer needed

Removed the item's unused private `Sheaf.Paper.TwistPreservesFiniteness` import;
the new obligations retain `prop-weil-twist-preserves` as a proof dependency.
The item's original public imports are retained through the unchanged public imports
of the coordinate module. No public visibility is lost.

The original three obligations (composite transpose, base-changed line evaluation,
last-factor product), finite compact projection, compact-support base change and Tate
finiteness remain needed by the two coordinate obligations; none is claimed pruned.
The direct assembly now uses `lem-pur-ordered-affine-transpose-projection`,
`lem-pur-affine-space-trace-successor-contraction`, and
`lem-pur-affine-space-trace-contraction-product`. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies state the geometric identities in different source,
coefficient-unit and compactification coordinates. These are actual canonical-map
matching obligations; they are not definitional equalities in the existing API.
The new steps record them explicitly. The unit's ordered recursion is retained;
there is no permutation or alternate purity route. The existing ordered-transpose
projection theorem already includes the dimension-one identity, so redoing its
normalization in this item is unnecessary.

`tools/downstream.py` reports zero Lean importers of the item in this snapshot;
its DAG parents remain relevant, and the item is preserved with unchanged signature.
No source-library file is changed and no other group's held module is adapted.

## New nodes

`def-pur-affine-space-binary-trace-coordinates` records the eight relocated canonical
coordinate constructions and predicates. `def-pur-affine-space-last-line-contraction`
records the actual constructed last-line contraction and source comparison.
`lem-pur-affine-space-trace-successor-contraction` records the first remaining step;
`lem-pur-affine-space-trace-contraction-product` records the second. `def-pur-normalized-line-evaluation-trace` and
`def-pur-trace-origin-compactification-change` register the two existing data
constructions used by the contraction (no new Lean declarations). All are in
sec-smooth-purity/sk-prop-an and trace back to the Integration paragraph and the
ancestor composition-law proof. Searches found no duplicate blueprint statement and
no Mathlib theorem about these specified geometric maps.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
