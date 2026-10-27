## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.etale_relation_restriction_quotient` with its
statement and all three existing definitions unchanged. Added private, proved helpers
for local surjectivity of a specified universal sheafification map and of the Yoneda
map of a surjective étale morphism. Proof imports are
`Sheaf.AlgebraicGeometry.EtalePullbackRelationPresheaf`,
`Sheaf.AlgebraicGeometry.FppfUniversalUnitLocallyInjective`, and Mathlib's
`CategoryTheory.Sites.LocallyBijective`.

The canonical comparison comes from `hη'`. Local injectivity follows from the existing
small-valued universal-unit lemma, injectivity of the presheaf comparison, and cancellation
of the locally surjective universal map. In the surjective case the singleton fppf cover
makes the Yoneda map locally surjective; the comparison is then locally bijective.
Updated the theorem node's proof route to follow this argument. No shared interface changed.

Validation: `lcompile.py` compiled the complete file cleanly in 5.1 seconds.
The theorem signature was also compared byte-for-byte with the current library copy.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.AlgebraicSpace.etale_relation_restriction_quotient`
(node `lem-trf-etale-relation-restriction-quotient`). Added zero holes; none remain in
the delivered module. No split-off statements or new modules.

## No longer needed

Removed the unused private imports `Sheaf.CategoryTheory.SiteCoveringAxioms` and
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.
The planned dependency `lem-trf-fppf-generator-sheafification-comparison`
(module `Sheaf.AlgebraicGeometry.FppfGeneratorSheafificationComparison`) is not needed:
the existing small-valued universal-unit lemma and Mathlib local-bijectivity API suffice.
The old direct tool dependencies `lem-weil-pbc-site-sheafification-sections-local` and
`def-weil-pbc-sites-and-cohomology` are unnecessary as direct proof inputs; their obsolete
`tool_uses` entries were removed. The item is the generator-comparison node's only actual DAG consumer (ignoring historical
review notes), and no Lean file currently imports its module. Removing this dependency
therefore prunes that planned branch. The other removed direct inputs have other uses.
No existing module is deleted. The pullback-relation dependency is retained.
No unit statement or realized proof step is bypassed; the item's unit has no realized
nodes in its `realized` record. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned generator-sheafification comparison has values in
`Type (max (u + 1) v)` and uses lifted Yoneda, while this item's existing statement has
values in `Type u` and ordinary Yoneda. It cannot be applied directly at the required
universe. The already proved small-valued universal-unit lemma resolves this mismatch
without changing either statement or adding assumptions.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
