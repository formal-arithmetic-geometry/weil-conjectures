## What changed

Retired `Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit` in favour of
`WeilConjectures.AlgebraicGeometry.FibreProductNeighbourhoodLimit`, as explicitly
requested by its row in coord/retire-items.tsv and the human-approved retirement
hand-off. The prerequisite Sheaf.StrictHenselization copy is already retired.
The item's old file is removed from the sandbox and listed in deleted.txt.
No official-library source or target is changed.

Repointed `lemma-weil-pbc-fibre-product-limit` to the official
`AlgebraicGeometry.fibre_product_neighbourhood_limit` and recorded its exact
signature. Updated the proof description to use the official affine cone.
The mathematical statement and every parent dependency remain intact.
The canonical comparison between the two vertices is
`Scheme.Spec.mapIso (Scheme.smallStrictHenselizationColimitIso s).symm.op`.
Lean also checked the exact affine-leg compatibility equation:

```lean
Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv ≫
  (Scheme.strictHenselizationAffineCone s).π.app (op (op j)) =
    (Scheme.strictHenselizationCone s).π.app (op (op j))
```

After exposing the two Spec-map legs, this is
`Functor.Final.ι_colimitIso_inv` for the representative functor. Thus the
comparison preserves the affine cone legs specified in both theorem signatures.

Validation: the original Sheaf proof compiled. A temporary Lean module importing
only the official twin checked the displayed comparison isomorphism; a second
scratch check verified the affine-leg compatibility equation and printed
its theorem's axioms: propext, Classical.choice and Quot.sound only. That module
compiled and is not part of the delivery. There are no live direct consumers to
compile. The change record is
`coord/changes/F2-fibre-product-neighbourhood-limit-retirement.md`.

## Proved and sorry left

The assigned source had zero direct holes. The existing official
`AlgebraicGeometry.fibre_product_neighbourhood_limit` is completely proved,
with only the three allowed axioms. Holes closed: 0 of 0. Holes added: 0.
Holes left: 0. Split off: 0. This is the requested duplicate retirement,
not a newly closed hole or a decomposition.

## No longer needed

The module `Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit` and its
separate declaration are retired. Its imports disappear with the copy.
The official module, both strict-henselization constructions and their canonical
comparison are preserved. No mathematical dependency node is withdrawn and no
parent dependency is pruned: the existing parents use the official realization
through the updated Lean attachment.

The sole historical importer,
`Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology`, is quarantined.
Its archived source imports the item privately but never calls its theorem.
The archive and its mathematical dependencies are preserved; this delivery does
not infer withdrawal of any parent from its current absence in lean/.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief did not mention the specific retirement assignment;
its source is the item's explicit row in coord/retire-items.tsv. The current
module has no sorry and compiles. 
The old kept-pair reason referred to the unretired Sheaf.StrictHenselization
copy. W4's landed retirement removed that obstruction. The official theorem
restates the result using strictLocalization and its canonical affine cone;
the checked spectrum-colimit comparison reconciles that API difference without
changing the node's mathematical meaning. The unit route is unchanged.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
