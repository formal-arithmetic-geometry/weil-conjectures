# Stage-1 delivery: lem-sf-prescribed-residue-cell-cone-model

## Files written

- `dag/nodes/sec-six-functors/lem-sf-prescribed-residue-cell-cone-model.json`: statement, split into six proof steps; no Mathlib match for the full statement.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: worker report and self-review.

New nodes: 0. New Mathlib leaves: 0. No Lean or unit file written.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for prescribed-residue/residue-cell terminology, then for cohomology splitting and cone terminology in the relevant SixFunctors and CategoryTheory sources. No project declaration giving every clause of this item was found. The existing source declarations concerning residue fields in algebraic geometry are unrelated.

## WANTED

None. All sources needed for this elementary cone expansion are present in `literature/stacks-project/`.

## Findings and corrections

The item is sound as stated. No statement or statement dependency was changed. In particular the evaluation hypothesis is imposed only on T, not on every object U; coefficient completeness and integral quotient towers are not needed. The inherited blueprint ancestry points to the evaluation paragraph of lem-fix-weil-operations, whose local-projective-model branch created the parent item. I read the main-20261015 ancestor proof and the chapter/unit records; I kept that local-model route. The substantive source here is Stacks 09C3, proetale.tex, lemma-local-structure-constructible-complex, final induction paragraph (lines 5920-5939 in this copy). The source omits the shorter-amplitude argument. This delivery supplies it for the precise free residue model of this item. Its proof is marked agent-written because these extra details are an expansion rather than text present in Stacks.

The existing lem-sf-projective-cohomology-split-model already supplies all prescribed splittings and the natural shifted-free generator bijection. Recreating a cohomology-splitting lemma would be a duplicate. The existing lem-sf-triangle-morphism-iso is a Mathlib leaf for Stacks 014A, so no triangle-comparison node is needed. The literal cone decomposition, contraction, and finite zero-differential tensor calculation are explicit elementary steps; creating new nodes for those would reproduce clauses of the item. The final step is 1306 characters; every step is shorter than 2000 characters.

The imported item already carries Q151's Mathlib searches. I preserved them, ran fresh logged LeanFinder, Loogle, grep and two LeanSearch queries, and read the returned hits. The Loogle/grep searches reproduce queries already present in the imported record, so those records are retained without duplicate entries. Read Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean:93 (identity-cone homotopy), DegreewiseSplit.lean:89-130 (cone of the connecting map of a split short complex), Factorizations/CM5b.lean:109-110 (specific cone projection homotopy equivalence), and DerivedCategory/Ext/EnoughProjectives.lean:40 (a projective single-term split epimorphism). These do not give the full sheaf statement with its prescribed cohomology, universal quantifier over splittings and tensor formula. The two semantic phrasings likewise give no match for the whole item.

Whole-DAG statement searches found the existing projective splitting, triangle and restriction nodes. Whole-blueprint searches for prescribed top cell, free cohomology, projective-cohomology, bounded flat and mapping cone found no blueprint node stating this item. Its `blueprint.same_as` remains empty. The ancestor command returns lem-fix-weil-operations, agreeing with the inherited exact place and via list. No new node requires a same-tag duplicate comparison.

## Not duplicates

No new nodes. All reused results are cited in place.

## Unfinished work

None for this one-level split. The cited unsplit or already-split results remain existing DAG work; no new helper node was introduced.

## Review by Q98

I read Stacks 09C3's final induction paragraph and checked the source's use of a top free cell against the present prescribed cohomology hypothesis. I also read derived.tex definition-cone (the matrix with target plus shifted source), Tag 064B (maps from bounded-above projectives), Tag 014A (two isomorphic components), sites.tex Tag 00XR (restriction and limits/colimits), sites-modules.tex Section 03DH (localized ringed sites) and Section 03EK (sheafified tensor), and homology.tex Tag 0116. No SGA source is used.

Step 1 takes exactly the first conclusion of lem-sf-projective-cohomology-split-model: a chain map to any representative inducing the specified theta in every degree. Its T/evaluation, coefficient ring sheaf, bounded cohomology and finite-rank hypotheses all agree. Localization inverts that quasi-isomorphism by def-weil-abstract-derived-category. Step 2 uses the same node's displayed natural Hom-to-global-sections bijection. It compares u with ANY prescribed phi followed by the top inclusion; identical induced theta_b means identical generator sections, hence identical arrows. This checks the all-model clause separately, rather than assuming the particular model in the existence assertion suffices.

Step 3 cites the actual TR3 clause of def-weil-triangulated-category and the distinguished cone construction of def-weil-abstract-derived-category. The square commutes in the correct direction because phi^{-1}u=Q(i). The existing Mathlib leaf lem-sf-triangle-morphism-iso states exactly that two isomorphic components force the third to be an isomorphism. It supplies an isomorphism of triangles, with no false uniqueness assertion for the third component.

Step 4 uses the cone matrix explicitly stated in def-weil-abstract-derived-category. I checked its degree b-1 to degree b differential, including the case b-1=a, where the lower summand and the extra top source coexist. The reordering maps are inverses, the disk differential is +identity, and h^b=identity satisfies the stated positive-sign contraction. Projection to W is a quasi-isomorphism by direct kernels and cokernels; thus its derived inverse follows just from localization, without silently citing a contraction theorem.

Step 5 uses all three relevant clauses of lem-weil-proetale-weakly-etale-localization for the site and constant ring. The input U is precisely an object of T's small pro-etale site, as that lemma requires. lem-pur-localized-module-restriction-quasi-iso applies to unbounded module complexes on any localized site and says exactly that quasi-isomorphisms survive restriction; the localization universal property then gives a derived functor preserving our isomorphism. lem-weil-pbc-site-constant-restriction identifies constant module matrices, including identities and zero maps. Its small-site hypothesis is met in the chosen site universe. These two non-Mathlib off-unit results are declared as generic tool uses in split_report: site identification and restriction preservation are not alternative routes for the top-cell argument.

Step 6 cites the actual signed total tensor in def-pc-tensor-complex-sheaves and the sheafified tensor in def-pur-sheaf-tensor-product. The basis-coordinate maps identify finite-free tensor with finite sums, explicitly. Thus tensor with an acyclic complex is a finite sum of shifted signed copies, whose kernels/images show acyclicity; this verifies K-flatness by def-pc-kflat-complex without using flatness of all field sheaves or an uncited bounded-flat theorem. def-weil-derived-tensor explicitly allows a K-flat first factor to compute tensor with an arbitrary second factor. Putting F in degree zero removes all differentials and gives the desired derived object, not merely a cohomology-wise assertion. The support is exactly what def-weil-proetale-tor-amplitude tests.

I tested a=b (empty W, acyclic identity disk), a=b-1 (disk overlaps the unique lower term), r_b=0 (the source cell and disk vanish), lower zero ranks, the all-zero ranks case, negative values of b (the same cochain degrees and parity signs), and the empty scheme (all module objects zero). Each formula remains valid. I checked delivery-errors B-E: no new non-self-contained node, fabricated search, restated-clause helper, uncited non-elementary assertion, cyclic dependency, route substitution or additional hypothesis is used. Every citation was read from its node statement, and citations.json copies those statements verbatim. No correction to the mathematical statement was necessary.
