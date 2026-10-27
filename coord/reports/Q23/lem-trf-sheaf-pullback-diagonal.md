# Worker report: lem-trf-sheaf-pullback-diagonal

## Files written

- dag/nodes/sec-trace-formula/lem-trf-sheaf-pullback-diagonal.json: existing statement split into four explicit elementary steps; no whole-item Mathlib match.
- citations.json: five verbatim statement excerpts, one for every step/node citation.
- report.md: this report and self-review.

New nodes: 0. New Mathlib leaves: 0. The statement and its five statement dependencies are unchanged.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag and for representable diagonals, algebraic spaces and sheaf fibre products found no project declaration stating all clauses. Generic scheme diagonal results cover different objects. No Lean was written or compiled.

## WANTED

None. All sources used are present locally.

## Findings and repairs

The unsplit item had no proof. I read spaces.tex, Tag 04T9 (lemma-fibre-product-spaces-over-sheaf-with-representable-diagonal), and Tag 02X2 (lemma-fibre-product-spaces), together with sites.tex, Tag 00VM (definition-sheaf-sets). The larger Stacks result assumes algebraic spaces and a representable diagonal for H to obtain a scheme atlas. The item's smaller claims require only sheafness of H and representable diagonals for F,G: the explicit scheme-test calculation below proves precisely that, without importing the atlas part or assuming representability for H. There is no statement dispute.

I expanded the universal-property sentence of 02X2 into a pointwise inverse on natural transformations. I expanded the cartesian-square argument of 04T9 into an explicit natural bijection on scheme tests, including its map to T and the evaluation-at-identity argument for arbitrary h_T-valued tests. These expansions avoid needing general representability permanence or a separate Yoneda theorem as unexplained black boxes. Each step is under 1000 characters and contains only substitution into the existing definitions and the fibre-product universal property.

I searched the whole DAG by tags 04T9 and 02X2 and by the sheaf-fibre-product/representable-diagonal notions, and ran blueprint_refs.py searches for “sheaf pullback”, “representable diagonal” and “fibre product”. No blueprint statement duplicates this explicit lemma. The parent lem-trf-space-fibre-products-etale-covers adds algebraic-space atlases and stability of jointly surjective etale families; citing it would also risk circularity. I retained the historical ancestor and exact existing from.place. No unit realization fields change because this item is not the unit's key statement.

The inherited mathlib_searches are retained as received. Five current searches were run with msearch.py and read, and their exact tool/query pairs and results were appended from searches.jsonl. LeanFinder was tried with two phrasings. All current services answered. Sites/Limits.lean:139, Sheaf.isSheaf_of_isLimit, gives the sheafness clause in general, but not the explicit diagonal comparison. Representable.lean:588,639,670 gives of_diag, diag_of_map_from_obj and diag_iff for a single object's relative representability, not the component equality-locus construction. The other hits concern equalizer sheaf conditions, Zariski representability or scheme pullbacks. The whole item is therefore split, rather than marked as a leaf.

## Not duplicates

No new nodes are created, so there are no new/existing tag pairs to distinguish.

## Review by Q23

I checked the split against delivery-errors B through E with the source and cited statements open. Step 1 uses exactly the matching-family/equalizer sheaf condition in def-weil-pbc-sites-and-cohomology: component gluing is unique in F,G, and uniqueness in H proves the remaining equation. The functor laws and restriction equation are written out. Step 2 uses the same node's statement that sheaves form a full subcategory with natural transformations as morphisms; its inverse is given on every section, naturality is checked, and both composites are identities on ordered pairs.

For Step 3 I checked def-trf-algebraic-space's definition of scheme-test representability and h_U(T)=Mor_S(T,U), and def-pc-fibre-product's full existence and unique-lift universal property. The representable-diagonal hypotheses supply A and B over the same scheme T. A test map into A is a map u with one uniquely determined section z; removing that forced variable gives exactly x_1|_u=x_2|_u. The identical calculation in G and the fibre-product universal property give maps into A times_T B. No claim about topological images, reduced schemes or scheme-valued H is used.

Step 4 substitutes the literal subset definition of P, so equality is componentwise; the forward map and inverse are explicit. I checked that precomposition replaces u by u composed with v in both descriptions, proving naturality and compatibility with the map to T. The last paragraph evaluates any alpha at 1_T and uses its naturality to show every test is covered, which is precisely the representability criterion quoted from def-trf-algebraic-space. This is a direct calculation, not an invocation of a missing general Yoneda statement. citations.json copies the relevant portions of all cited node statements verbatim, and every quoted portion was checked as an actual substring.

Edge cases: an empty fppf cover forces F(T),G(T),H(T) to be singletons, and the same gluing proof gives P(T) a singleton; if either component equality locus is empty, the product and the P-equality locus have no sections over nonempty tests; if p_1=p_2 then A and B both represent h_T and the result represents h_T as required. Taking H terminal recovers the ordinary product, while taking F=G=H with both maps identities recovers F. The Hom bijection also holds when Q has no sections on a test, since its formula is pointwise. The statement's existing size/site convention is retained; no new limit indexed by a large category is used.

I found no omitted non-elementary lemma: every step is the explicit few-line gluing or unique-lift calculation just described. No new nodes restate clauses of the item, no new unsplit proof sketches are introduced, and no route-changing tool theorem is cited. Only the sandbox was written. Stage 1 only; no compiler, Lake, build, direct git command, launcher edit or repository edit was used.

## Unfinished work

None in the mathematical split. Required server dry run and direct delivery follow this report.
