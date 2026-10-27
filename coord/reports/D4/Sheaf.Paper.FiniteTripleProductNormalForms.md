## What changed

Replaced the triple theorem's open proof by four applications of
`AlgebraicGeometry.ProEtale.finiteProduct_compactification`, two explicitly proved
categorical substitution calculations, preservation of the four binary open
isomorphisms, and binary unit pasting. Every original and displayed compactification
remains independently quantified. The two intermediate D+ objects and their
retained etale witnesses come from the already-assumed tensor domains.

Moved the coordinate declarations verbatim into
`Sheaf.Paper.FiniteTripleProductDefinitions`, publicly reexported by the original
module. This permits the two binary compatibility lemmas to depend on the exact
existing coordinate maps without importing the triple theorem and creating a cycle.
The change record is `coord/changes/D4-triple-product-coordinate-module.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.finiteTripleProduct_normalForms` by a complete
combining argument, conditional on the explicitly named binary lemmas. Both
isomorphism conclusions use the existing `finiteProductOpenTensor_isIso` theorem.
The private left/right substitution and binary restriction-specialization helpers
contain no holes. The complete item module compiled cleanly in 40.6 seconds.

Added one hole:

- `AlgebraicGeometry.ProEtale.FiniteTripleProduct.restrictPair_pasting`
  (`lem-pur-finite-product-open-restriction-pasting`).

Proved the new simultaneous naturality theorem
`AlgebraicGeometry.ProEtale.finiteProductOrdinary_naturality`
(`lem-pur-finite-product-ordinary-naturality`) without holes, by pasting naturality
of symmetry, projection, exchange and the direct-image compositor. Its module
compiled cleanly in 12.9 seconds.

No holes occur in definitions. This is a decomposition, not a claim of an
unconditional sorry-free proof. The item has one original hole closed and one
strictly smaller binary hole added.
The remaining restriction lemma is a decomposition; it does not duplicate the
triple theorem or its ordinary-product conclusions.

## No longer needed

The geometric product constructions already prove the open/proper properties in
`FiniteProductCompactification`; the triple proof does not separately use
`lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-proper-fp-permanence` or
`def-pc-fibre-product` as new proof steps. The direct uses of
`lem-pur-derived-pullback-tensor-iso`, `lem-cbc-extension-zero-composition` and
`lem-pur-finite-open-product-swap` move to the binary restriction lemma.
The ordinary naturality calculation uses `def-exchange-projection` and
`lem-weil-derived-direct-image-composition`. The binary compactification equations
already quantify all original choices, so `thm-sf-comp-composition` and
`prop-compactification-coherence-detailed` are not separately invoked at the
triple level. All remain available through the existing public definition imports;
no source-library declaration or DAG parent is withdrawn. No whole module is pruned.

## Where the brief, the DAG or earlier work was wrong

The plan correctly identifies the calculation, but the existing binary theorem
only gives the isomorphism of its e; its specific recursive restriction equation
was not available as a Lean theorem. The corresponding swap theorem uses different
pullback/compositor coordinates. The new binary unit-pasting statement isolates
this actual compatibility, rather than assuming a triple normal-form clause.

The two normalized comparison wrappers used by the binary and triple definitions
have identical explicit constructions; the proof checks their identification in
Lean. No statement or mathematical hypothesis is changed.

## New nodes

`def-pur-finite-triple-product-coordinate-data` records the existing explicit
coordinate definitions moved without semantic changes into their own module.

`lem-pur-finite-product-open-restriction-pasting` is the binary naturality and
unit-normalization calculation for arbitrary supplied restrictions. It is used
first with identities, then with the inner binary e in each outer product.

`lem-pur-finite-product-ordinary-naturality` is simultaneous naturality of the
ordinary binary product word. It is used once in each tensor variable.

The unit route and all target statements are preserved. Identity opens, empty
products and zero coefficient objects introduce no exception in either binary lemma.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
