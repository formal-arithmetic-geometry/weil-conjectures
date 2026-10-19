## What changed

Proved `AlgebraicGeometry.Etale.sf_internalHom_triangulated` by specializing
`CategoryTheory.ringedInternalHom_exactOfUniverses` to the constant coefficient
ring sheaf on the small etale site, then swapping the two conjuncts.
The assigned theorem's signature, hypotheses, universes and visibility are unchanged.

Repaired the existing generic exactness interface in
`Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`: its new
`ringedInternalHom_exactOfUniverses` formulation allows independent site-object,
site-morphism and coefficient universes and uses `derivedInternalHomOfUniverses`.
The old `ringedInternalHom_exact` keeps its exact original signature and is now
proved by the equal-universe specialization. This preserves the old applications
without consumer edits. Neither the tensor adjunction nor restriction is changed.

This is the same generic ringed-site exactness result already assigned to
`lem-weil-pbc-ringed-internal-hom-exact-restriction`, with its universe mismatch
repaired; it is not a new decomposition of the etale theorem. The node's proof
records the independent-universe construction and its declaration list records
the repaired interface alongside the existing signed-calculus interface.
The item node records the direct specialization. No mathematical statement,
definition, unit route or target is changed.

Read Stacks Tag 08JC (`lemma-RHom-triangulated`) and its Hom-complex construction
in Tag 08J7 in `literature/stacks-project/sites-cohomology.tex`, together with the
current blueprint statement and proof. The termwise split cone argument applies
unchanged at independent universes. Earlier recorded LeanFinder and Loogle
searches returned generic triangulated-category results, not this internal Hom.
Source search also found the closed-structure derived-Hom triangle lemmas;
those do not give a CommShift structure for the recorded Hom-complex bifunctor.

Change record: `coord/changes/SfHomTriangulatedIndependentUniverses.md`.

## Proved and sorry left

Assigned item: closed its one hole,
`AlgebraicGeometry.Etale.sf_internalHom_triangulated`
(node `lem-sf-hom-triangulated`); zero holes remain in the assigned module.
Zero separate intermediate results were split off.

Dependency interface repair: closed the old equal-universe proof hole
`CategoryTheory.ringedInternalHom_exact` by specialization and retained its
unproved generic content as `CategoryTheory.ringedInternalHom_exactOfUniverses`
(node `lem-weil-pbc-ringed-internal-hom-exact-restriction`). This is one hole
closed and one hole added by declaration name, with zero net dependency progress;
the generic exactness result is not counted as proved.
The other remaining hole in the delivered dependency is the unchanged
`CategoryTheory.ringedInternalHom_restriction` (the same node).
Thus the two delivered modules go from three holes to two: two declaration holes
closed and one added, for a net reduction of one. No axiom or definition is added.

The retained sandbox compile of the compatibility version passed both modules
in 43.6 and 8.1 seconds. The resumed dry run initially received no response from
the compile server after its retries; the final delivery checks are recorded below.

## No longer needed

Removed the item's proof imports
`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses` and
`WeilConjectures.AlgebraicGeometry.DerivedCategories`.
The proof needs neither the separate normalized shift construction nor the
scheme-derived-category infrastructure. The original public imports are retained.
All five declared proof dependencies remain used: the etale site, size convention,
derived category, derived Hom and generic ringed-site exactness.
No node is withdrawn, and no unit statement or step is bypassed.
These are removed direct imports; no claim is made that their modules become
unreachable from every other target dependency.

## Where the brief, the DAG or earlier work was wrong

The dependency's old equal-universe signature could not be applied to the recorded
small etale site: that site has object universe u+1 and morphism universe u.
The independent-universe shift module supplies only covariant exactness and a
source-shift comparison, not the full contravariant CommShift assertion.
The generic theorem must therefore allow the existing independent-universe
Hom construction. Its original equal-universe statement remains available.

The previous sandbox report described an obsolete version which changed the
old theorem's signature and adapted five consumers. The current delivery keeps
the old signature, contains only two Lean files, and adapts no consumer.
The downstream inventory was refreshed: 1,792 downstream modules; five actual
external callers of the old theorem. The change record lists them all.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
