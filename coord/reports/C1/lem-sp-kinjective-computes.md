1. files written

- `dag/nodes/sec-abelian-varieties/lem-sp-kinjective-computes.json`, statement, split.
- `dag/nodes/sec-abelian-varieties/lem-sp-kinjective-comparison-principle.json`, statement, Mathlib leaf (`CochainComplex.IsKInjective.Qh_map_bijective` and `quasiIso_iff`).

2. attachments: none.

3. WANTED: none.

4. The imported proof had a long comparison argument hidden in its first step and omitted dependencies for additive functors carrying homotopies and for bounded-below injective complexes. I made the comparison principle explicit as a Mathlib leaf and cited existing DAG leaves for the other facts. The statement is unchanged in substance, with the three clauses retained.

5. Nothing remains unfinished.

## Review by C1

I read the imported node, its blueprint proof, the bridge and derived-functor definition nodes, and the existing nodes for bounded-below injective complexes, shifts, and additive functors preserving homotopies. Step 1 uses exactly the new comparison-principle statement. Step 2 uses that comparison statement for the two resolution maps, the bridge definition of K-injectivity, and the existing homotopy-preservation statement; these supply existence, uniqueness, inverse maps, and transport under `v`. Step 3 checks the hypotheses of the bounded-below injective leaf, then uses the injective-resolution definition and the two definitions of `Rv` and `R^p v`. Step 4 uses the existing shift statement and spells out the termwise additive shift calculation. I verified every citation against the cited node text and recorded verbatim quotes in `citations.json`. I also ran both LeanFinder phrasings, two Loogle queries (unavailable), and two grep searches required for the new Mathlib leaf, and recorded their actual results.

## Second reading by C1

- Item statement: checked against the blueprint node and bridge definition; the three clauses and all hypotheses are unchanged and the zero complex, a field category, and shifts by 0 and 1 are consistent.
- Step 1: checked against the comparison-principle node; its quasi-isomorphism, derived-category, and K-injective hypotheses are exactly those used.
- Step 2: checked against the comparison-principle, bridge, and homotopy-preservation statements; the inverse, uniqueness, functoriality, and transport under the additive functor are now written explicitly.
- Step 3: checked against the bounded-below injective representative, injective-resolution, bridge, and left-exact-additive statements; the resolution's quasi-isomorphism and degree-zero cohomology are included in the citation.
- Step 4: checked against the shift node; both K-injectivity and quasi-isomorphism under shifts, followed by the termwise additive calculation, are stated.
- New comparison-principle node: checked for self-contained abelian and homotopy-category definitions, source lines, and the Mathlib declarations used as candidates; it is marked unsplit because the precomposition bijection is assembled from several declarations rather than one exact declaration.
- Existing cited nodes: searched the repository for duplicate comparison, shift, and bounded-below K-injective statements; no duplicate of the new comparison statement was found.

Changes: reclassified the comparison node from an inaccurate Mathlib leaf to an unsplit statement with a Mathlib candidate; added the missing abstract-derived-category dependency; expanded step 2's functoriality argument; and replaced two short citation quotes with complete verbatim statements.
