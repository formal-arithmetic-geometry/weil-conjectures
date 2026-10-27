# Stage-1 report: lem-sfb-space-single-complex-tensor-inheritance

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-single-complex-tensor-inheritance.json: statement, now split into seven steps; no Mathlib match.
- citations.json: verbatim statements supporting all eighteen step/node citation pairs.
- report.md: this report. Existing search-*.txt and searches.jsonl were read and retained; one second-phrasing leanfinder search was added to the log.

No new DAG nodes and no Mathlib leaves were created. All helper results already exist in the live DAG. The earlier sandbox contained searches only, with no node or report to repair.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, single-complex/base-change terminology and tensor inheritance. AlgebraicGeometry.singleComplexInheritedTensorCondition in WeilConjectures/AlgebraicGeometry/SingleComplexInheritedTensorCondition.lean:45 is a scheme theorem with ordinary scheme stalks, attached to lem-pc-rf-single-complex-inherited-tensor-condition. It does not quantify over algebraic spaces or their geometric small-etale stalks, so it cannot attach this item. The ring theorem ModuleCat.localizedTensorComparison_inheritance is already represented by lem-pc-localized-tensor-comparison-inheritance; it is used rather than duplicated.

## WANTED

None. All sources used are present in literature/stacks-project. The current blueprint was read from literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially paragraph (3). The chapter and unit records and the three blueprint levels in SETUP.md were read. No chapter or unit route was changed.

## Errors and changes

The item had a statement and searches but no argument. Its statement agrees with Stacks spaces-perfect.tex, Tag 0DKI(1), using precisely equation-bc before Tag 0DKG. There is no statement dispute and no hypothesis was added or removed. The source's very brief reference to tensor transitivity is expanded by the existing ring-level inheritance lemma and a representative-level identification of the actual canonical maps. The inherited blueprint.from.node is null; blueprint_refs.py ancestor reports None for the item, so this is retained rather than inventing an ancestor. Its detailed inherited from.place is retained, and same_as is [] after whole-blueprint searches for single-complex and 0DKI and a broader tensor search.

The Mathlib searches already in searches.jsonl were read through search-0.txt to search-4.txt. They give ordinary ring tensor/base-change, flatness and stalk-rank results, not this algebraic-space derived assertion. A second semantic phrasing returned rankAtStalk_baseChange and Module.Flat tensor exactness results. None provides geometric-stalk tensor inheritance. Imported searches in the live item are retained as historical records, separately from the genuinely logged sandbox searches appended to the item.

## Not duplicates

No new nodes. In particular the flat geometric-stalk lemma, quasi-coherent closure, arbitrary ringed-topos tensor pullback, normalized stalk facts and ring-level tensor inheritance are existing nodes. The scheme inheritance theorem is not generalized silently to algebraic spaces.

## Review by Q111

I read delivery-errors B through E in full, including the repeated copy, and checked the actual statements rather than treating a title or definition as a theorem. The mathematical source for the item is spaces-perfect.tex Tag 0DKI(1): its first paragraph invokes quasi-coherent closure, and the tensor argument invokes transitivity. I also read Tag 0DKG's preceding comparison and its geometric strict-local setup, more-algebra.tex Tag 0BYJ's K-flat associativity argument, sites-cohomology.tex Tag 07A4's resolution formula and Tag 0DEN's K-flat stalk criterion, sites-modules.tex Tag 05V3's exactness and Tag 05V5's pullback-stalk calculation, derived.tex Tag 070I, and injectives.tex Tag 079P. There are no new nodes needing separate source validation.

In step 1, lem-sfb-space-derived-qcoh-pullback-tensor explicitly asserts both closure operations on unbounded algebraic-space complexes; lem-weil-pbc-ringed-topoi-derived-tensor-pullback states the canonical bifunctorial isomorphism for arbitrary small ringed topoi and its flat-term K-flat computation. This verifies that the proposed map has quasi-coherent source and target without imposing bounds.

In step 2, lem-pc-kflat-resolution supplies the two flat-term K-flat representatives. prop-pur-kinjective-resolutions-exist supplies a K-injective target on the small ringed site, and lem-weil-pbc-kinjective-hom-derived gives the Hom bijection that realizes the given derived coefficient map by a chain map. The ringed-topos tensor-pullback node supplies the derived-pullback representative. In particular the coefficient map is not assumed to be a quasi-isomorphism.

In step 3, lem-sfb-ringed-site-point-exact ensures that the chosen stalk complexes represent the derived stalk objects. lem-sfb-ringed-site-kflat-stalk-criterion asserts K-flatness at every point, without boundedness. lem-sfb-space-geometric-stalk-tensor-calculus states exactly flatness of A tensor_R B -> C and both ordinary and derived pullback-stalk identifications, including the canonical comparison. I checked that this is flatness over the tensor ring, not flatness of A over R; the proof never replaces one by the other.

In step 4, lem-sfb-ringed-site-point-tensor supplies the signed total-complex comparison and lem-pur-independent-inverse-image-tensor-comparison fixes its pure-tensor normalization. The ringed-topos tensor-pullback node and the K-flat stalk criterion make F(U) a K-flat C-complex, so its tensor with N computes the target even though N need not be K-flat. The geometric-stalk calculus gives F(Q) as the actual pulled-back stalk representative. I wrote out the tensorator on c tensor (u tensor q), kept the homogeneous factor order and checked the signed differential; this prevents a noncanonical monoidal structure from being substituted for the morphism in the item.

In step 5, lem-pc-base-derived-tensor-cohomology-action supplies the actual existence of universal derived extension, its canonical tensor-ring action and counit. def-pc-base-derived-tensor-cohomology-model specifies the further C-linear extension and the formula for its localized comparison; it is used to identify that map, not as a substitute for a tensor-exactness theorem. The geometric-stalk calculus identifies the same derived-to-ordinary comparison in equation-bc. I compared the maps before passing to cohomology and stated their common value on h tensor c. This supplies the input comparison required by the ring lemma.

In step 6, the statement of lem-pc-localized-tensor-comparison-inheritance has precisely the four commutative rings, C flat over A tensor_R B, two K-flat A-complexes, an arbitrary C-complex N, and an arbitrary map t:F(Q)->N used here. Steps 3 and 5 verify each hypothesis in all degrees. Its output uses the inverse scalar-extension tensorator, exactly the formula written in step 4. Step 7 only substitutes those already proved equalities and quantifies over the arbitrary point and integer. It is elementary and cites no further black box. The quotes in citations.json are copied verbatim from the statement of every cited node.

The generic inputs from other units are declared individually in split_report.tool_uses. They are tools for the stalk computation, not a replacement for the unit's alteration/direct-image route. The same-unit geometric stalk calculus and quasi-coherent closure remain on the inherited route. No new lemma restates a clause of the item, and there is no circular use of its conclusion. Each proof step is below 2000 characters; none hides an additional comparison lemma behind a word such as 'transports'.

I tested zero complexes, empty X', identity g, and unbounded E. Zero complexes give zero comparisons, and empty X' makes the assertion vacuous. With identity g the canonical comparison is the familiar one, with the same tensorator orientation. General unbounded E is handled by actual K-flat signed direct-sum totals and the unbounded ring lemma, not an invalid bounded spectral sequence or truncation limit. No noetherian, qcqs, Tor-independent or flat-square hypotheses are used.

## Unfinished work

None for this one-level split. Existing cited unsplit lemmas remain their own stage-1 items. No Lean file was written and no compiler or build command was run.
