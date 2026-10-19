## Worker report

The module `Sheaf.CategoryTheory.CorepresentedEquivalence` states
`CategoryTheory.Spaces.corepresented_equivalence`.  It uses the explicit covariant
corepresented functors `CategoryTheory.Spaces.corepresented` from
`Sheaf.CategoryTheory.InfinityCategoryOfSpaces` and the coherent equivalence predicate
`SSet.Enhanced.AreNaturallyEquivalent` from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`.

The hypotheses bind a quasicategory `C`, vertices `g,a`, an edge `e:g→a`, an inverse edge
`e':a→g`, and two 2-simplex inverse-triangle witnesses.  The conclusion is a coherent natural
equivalence between the explicit functors `h_a = corepresented C a` and
`h_g = corepresented C g`.  The declaration docstring records that the component at each
vertex is the singular-realization enriched precomposition map obtained by inserting the
specified edge in the first variable of the Hom pairing; the inverse 2-simplices provide the
coherent inverse triangles.  Full Kan complexes are retained because `corepresented` lands in
`Spaces.infinityCategory`, the coherent nerve of Kan complexes.

Dependencies used: `Sheaf.CategoryTheory.EnhancedDiagramsCones`
(`SSet.Enhanced.IsEquivalenceEdge`, `SSet.Enhanced.AreNaturallyEquivalent`),
`Sheaf.CategoryTheory.InfinityCategoryOfSpaces`
(`CategoryTheory.Spaces.corepresented`),
`Sheaf.CategoryTheory.InfinityPresheafYoneda` (the explicit Hom-pairing construction used by
the deferred proof), and `Sheaf.CategoryTheory.PointwiseEquivalences`
(`SSet.Enhanced.pointwise_equivalences`).

Edge cases checked: the quasicategory and vertex binders permit empty mapping spaces; no
nonemptiness, colimit, accessibility, or finite-index assumption is introduced.  The two
triangle equations use the identity degeneracies exactly as in `IsEquivalenceEdge`.

Searches: `msearch.py grep corepresent|precomp|equivalen` in
`AlgebraicTopology/Quasicategory` (no matching quasicategorical corepresented construction);
`msearch.py loogle "Quasicategory", "Iso"` (no match); `msearch.py leanfinder` for
precomposition-induced natural equivalence (ordinary-category results only); `rg` over
`WeilConjectures` and `lean/Sheaf` (the explicit constructions found in the dependency modules,
no existing theorem for this node).  No new nodes or dependency repairs were needed.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
