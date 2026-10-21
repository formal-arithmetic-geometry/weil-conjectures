## What changed

Proved `CategoryTheory.Functor.existsUnique_mapDerivedCategoryCompIso` in
`Sheaf.CategoryTheory.ExactDerivedComposition`, with its signature unchanged.
Added a private proof import of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
The witness is its already proved `mapDerivedCategoryCompIso F G`, and the required
normalization is exactly `mapDerivedCategoryCompIso_fac F G`.
For another normalized isomorphism, transitivity equates the two normalized composites.
Reassociation and cancellation of the three isomorphisms equate their components at every
`DerivedCategory.Q.obj K`. `Localization.natTrans_ext` equates their hom natural
transformations, and `Iso.ext` equates the isomorphisms.

The existing implementation of the witness realizes the node's steps 1--3: exact
factorizations, the whiskered composite factorization, and lifting the identity through
localization. The new uniqueness proof realizes step 4. Thus the existing DAG route and
all its dependencies remain accurate; no node or unit-route changes are required.
The Stacks localization lemma and the blueprint's exact-composition sentence were read.
The source implementation, Mathlib factorization definitions, and localization
extensionality signature were checked, including the independent category and derived
morphism universes. The server compiled the resulting module cleanly in 2.2 seconds.
The import-direction check permits the new proof import.

## Proved and sorry left

Closed one hole:
`CategoryTheory.Functor.existsUnique_mapDerivedCategoryCompIso`
(node `lem-sfb-exact-derived-composition`).
All 1 of 1 original sorries are proved; zero remain and zero are added.
No split-off statements or new declarations are introduced.

## No longer needed

None. No imports, nodes, or modules are removed. The three existing proof dependencies
remain used: exact derived factorization and localization construct the existing witness,
and localization extensionality proves uniqueness. The existing source declarations stay
unchanged. Search found the existing source compositor and normalization, so there is no
need to duplicate their construction or introduce intermediate nodes.

## Where the brief, the DAG or earlier work was wrong

None. The node's recorded source-library candidates supply existence and normalization
exactly as advertised. Its final uniqueness step is a short cancellation argument.
The current H3 return concerns an unrelated older item; this packet removes no helpers.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
