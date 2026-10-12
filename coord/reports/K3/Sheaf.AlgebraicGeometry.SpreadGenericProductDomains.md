## What changed

Proved the unchanged `exists_spread_generic_product_domains` in
`Sheaf.AlgebraicGeometry.SpreadGenericProductDomains` from a localization step and a fully
proved coordinate-image factor construction. Added proof-only imports of
`Sheaf.AlgebraicGeometry.SpreadGenericProductEmbedding` and
`Sheaf.RingTheory.FiniteProductFieldImageFactors`. No existing signature, definition,
visibility, or public import changed; no other existing module was adapted.

The new general theorem `exists_finite_domain_factors_of_product_embedding` constructs each
factor as the coordinate image subalgebra, proves the product map bijective by multiplying
coordinate lifts by the lifted idempotents and summing, proves the fraction-field property
from denominator identities, and uses `Module.Finite.small` and `Shrink.algEquiv` to put the
factors in the base universe. Its proof uses only Mathlib. The original theorem supplies
finiteness of the reduced tensor algebra and injectivity of the base maps into the fields,
then combines the resulting factors with the finite etale model and its scalar towers.

All three modules compile without errors or warnings using `lcompile.py --all`.
Edge cases checked in the proof and remaining statement: the empty product gives an empty
sum and no factor conditions; one coordinate gives the image of the sole projection; the
zero field element uses zero numerator; nonzero denominators stay nonzero by injectivity.
No arbitrary object was introduced by a definition based on an unproved existence theorem.
The constructed factors are actual image subalgebras and their universe shrinks.

## Proved and sorry left

Closed the original hole `exists_spread_generic_product_domains`
(node `lem-weil-pbc-spread-generic-product-domains`). Its body contains no `sorry`.

Added and fully proved `exists_finite_domain_factors_of_product_embedding`
(node `lem-weil-pbc-finite-product-field-image-factors`), with no holes.

One new hole remains: `exists_spread_generic_product_embedding`
(node `lem-weil-pbc-spread-generic-product-embedding`), whose proof is exactly `by sorry`.
It states only the localization/embedding step: a finite etale model, an injective map into
the field product, lifts of coordinate idempotents, and coordinate denominator identities.
It does not construct factors or assert a product equivalence. Its docstring and node give
the torsion killing, lifting, denominator descent, model base change and smallness argument.
The final product decomposition, finite-domain and fraction-field properties, factor universe
shrinking, and assembly are proved in Lean in this delivery.

This is a decomposition: one original hole closed and one lower hole added; net holes zero.
No `sorry` remains in the item's module, and no other hole was added.

## No longer needed

No existing import, node, or module was pruned: the original node had no proof dependencies
and the original module had only public Mathlib imports. Temporary explicit proof imports of
`Mathlib.Algebra.Algebra.Pi`, `Mathlib.RingTheory.TensorProduct.Maps`,
`Mathlib.RingTheory.TensorProduct.Finite`, `Mathlib.RingTheory.Finiteness.Small`, and
`Mathlib.Algebra.Algebra.Shrink` were tested and removed from the item as redundant with the
existing public Mathlib imports. The two new Sheaf proof imports are both used.

The factor construction uses coordinate images directly, so it does not require a new
complementary-idempotent quotient or Chinese remainder lemma. This changes only the route
below the unit level; the unit record has no realized statement or steps to bypass.

## Where the brief, the DAG or earlier work was wrong

The item's existing DAG proof has four substantive steps but `proof_deps = []`; there are
no stated child declarations to import for its localization argument. That argument is now
one named lower statement, while the coordinate factor construction is fully proved.

The cited blueprint source file is absent from this machine's read-only literature tree,
and fetching its exact pinned raw path returned HTTP 404. The complete existing item
and node docstrings supplied the source argument used here; the new node proof origins
explicitly say they were formalized from that existing argument, rather than claiming a
fresh reading of unavailable source text. LeanSearch returned HTTP 500; this is recorded
as unavailable. LeanFinder, Loogle and Mathlib/library source searches ran and are recorded.

## New nodes

`lem-weil-pbc-spread-generic-product-embedding` in
`dag/nodes/sec-smooth-purity/lem-weil-pbc-spread-generic-product-embedding.json` records the
remaining localization step and its public theorem in
`Sheaf.AlgebraicGeometry.SpreadGenericProductEmbedding`. It retains the specified generic
splitting and specified etale model, but concludes an injective product map with lifted
coordinate idempotents and denominator identities, not domain factors.

`lem-weil-pbc-finite-product-field-image-factors` in
`dag/nodes/sec-smooth-purity/lem-weil-pbc-finite-product-field-image-factors.json` records the
fully proved general coordinate-image construction in
`Sheaf.RingTheory.FiniteProductFieldImageFactors`. It needs no Noetherian, tensor, localization,
or etale model assumptions: a finite algebra, injective product map, coordinate idempotent
lifts, injective base maps, and denominator identities suffice. Both nodes inherit the
item's chapter and unit and identify the original finite-algebra blueprint clause.

The existing item node's proof and proof dependencies now follow these two modules.
There are no change records or forced adaptations.

## Second reading by K3

1. **Reading and interface check — pass.** I compared the delivered item module with the repository version. The existing theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body were added. The two new modules have self-contained public statements and their node records match their Lean declarations.

2. **Proof and axioms — pass.** All three sandbox modules compile with `lcompile.py --all`. The item theorem and the coordinate-factor theorem contain no `sorry`; the only remaining `sorry` is the explicitly split theorem `exists_spread_generic_product_embedding`, with its named node and docstring. The proofs use ordinary definitions and the expected algebraic constructions; no forbidden declarations or hollow definitions were introduced.

3. **Statement review — pass.** The target statement is unchanged and the two new statements are strictly smaller than the target: the embedding theorem stops before constructing factors, while the factor theorem assumes the embedding and proves exactly the coordinate-image decomposition. Edge cases include the empty finite product and zero numerators; denominator nonzeroness follows from the stated injectivity hypotheses. Searches recorded in the nodes found no duplicate library or Mathlib theorem.

4. **Pruning and dependencies — pass.** The item imports the two new proof modules as plain imports, and the factor module keeps only the public imports needed by its statement plus proof-only imports for shrinking and smallness. No old proof dependency or module became unused, and the unit route is preserved through the embedding and factor steps.

5. **DAG and delivery metadata — pass.** The existing node proof and `proof_deps` name exactly the declarations used by the item proof. Both split nodes contain source, proof steps, searches, Lean records, chapter and unit metadata. The report records the one decomposition (one target hole closed, one lower hole retained) and no statement or definition change.

I changed only this report by adding the required second-reading record; no Lean source or node content was changed during review.
