1. Files written:

- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-additive-total-transport.json` — statement, three sourced proof steps, and two proof dependencies; split.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-additive-finite-coproducts.json` — statement; Mathlib leaf, exact match `CategoryTheory.Functor.preservesFiniteCoproductsOfAdditive`.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-map-total-iso.json` — statement; project-specific unsplit infrastructure node, no Mathlib exact match.
- `citations.json` — verbatim quotes for every dependency used by every item step.

2. Attachments: none. No sorry-free declaration in the source states the item exactly.

3. WANTED: none.

4. What was wrong or incomplete: the imported item was unsplit and had no proof. The source implementation is split between `BicomplexColumns.lean` (finite diagonal support and preservation) and `TotalComplexMap.lean` (`mapTotalIso` and naturality); the proof now follows those two places. Searches of the DAG and current blueprint found no duplicate node or blueprint statement for either dependency. The source's support condition is sufficient because on a diagonal a nonzero term has `n ≤ p ≤ b`; this also covers the empty-diagonal case `n>b`.

## Not duplicates

- `lem-sfb-left-resolution-additive-finite-coproducts` vs `lem-sfb-left-resolution-bicomplex-total-exists`: the new node is the general Mathlib theorem that an additive functor preserves any finite coproduct; the existing node is a specialized existence statement for a resolution bicomplex and does not state preservation.
- `lem-sfb-left-resolution-map-total-iso` vs `lem-sfb-left-resolution-bicomplex-total-exists`: the new node gives the generic comparison isomorphism and its naturality under existing total and preservation hypotheses; the existing node only establishes totals for one bounded resolution bicomplex.
- `lem-sfb-left-resolution-map-total-iso` vs `lem-sfb-left-resolution-additive-total-transport`: the new node has no bounded-support hypothesis and supplies only the comparison infrastructure; the item specializes it to the stated integer bounds and proves those hypotheses.

5. What I could not finish: nothing.

## Review by N0

I read the item against the source declarations in `WeilConjectures/FromJoel/Algebra/Homology/BicomplexColumns.lean:877–911` and `WeilConjectures/FromJoel/Algebra/Homology/TotalComplexMap.lean:27–145`, and read the chapter and unit records. The item hypotheses match the source: both categories are preadditive, only the source category needs a zero object and finite coproducts, and the additive functor supplies the mapped finite coproducts. I also checked the source's `mapTotalIso` differential calculation and both naturality lemmas, including the fact that no common upper-bound witness is required.

Step 1 uses the finite-coproduct node only for the assertion it states: an additive functor sends an existing finite coproduct to a coproduct of the images and the comparison is an isomorphism. The remaining support calculation is elementary: `p+q=n`, `p≤b`, and `q≤0` imply `n≤p≤b`, a finite interval; the zero-object condition supplies the excluded terms. Additivity sends zero morphisms to zero morphisms, so applying `F` gives a bicomplex. Step 2 uses the map-total node for exactly its stated componentwise chain isomorphism, after Step 1 supplies the total and preservation hypotheses. Step 3 uses only that node's explicit naturality equation; because that node is formulated without bounds, it applies when the two complexes have different first-index bounds.

For the Mathlib leaf I read `Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean:213` and checked that its `PreservesFiniteCoproducts` conclusion is exactly the dependency statement. For the project node I read `mapTotalXIso`, `mapTotalIso`, `mapTotalIso_hom_naturality`, and `mapTotalIso_inv_naturality`; its statement records the needed total-existence and preservation assumptions rather than relying on implementation details. I tested the item on the zero bicomplex, a bicomplex concentrated in one bidegree, a diagonal with `n>b` (empty support), and maps between examples with distinct upper bounds. No statement correction was needed, and no cycle or duplicate was introduced.
