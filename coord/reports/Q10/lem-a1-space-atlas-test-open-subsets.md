## Worker report

Files written: `dag/nodes/sec-purity-real-sheaves/lem-a1-space-atlas-test-open-subsets.json` (statement; split, not a Mathlib leaf), `citations.json`, and this report. The existing statement, source, statement dependencies and blueprint ancestry are retained. The previously empty proof is replaced by six steps; proof dependencies are exactly the union of their citations. No Lean was written or compiled.

## New nodes

None. The point-lifting fact already exists as `lem-a1-space-fibre-product-point`; etale openness already exists as the Mathlib leaf `lem-weil-pbc-etale-morphism-open-map`. Representability and the two etaleness tests are instances of the explicit scheme-test definition in `def-trf-algebraic-space`, not new permanence lemmas.

Attachments: none. Searches of `lean/WeilConjectures/` for the item tag, algebraic spaces, point classes, and atlas/open terminology found no declaration proving the item. The existing point-lifting node's local Sheaf declaration is recorded as a sorry statement, not treated as an attachment.

WANTED: none.

The imported item had no proof. No statement error or source error was found; all clauses are preserved. No dependencies were removed. Nothing remains unfinished within the one-level split; its cited existing non-leaf nodes remain their own work items.

## Searches and blueprint

Read the current main-20261015 chapter, Rankin--Selberg unit, and the statement and proof of `lem-a1-affine-hc0`, as well as the DAG chapter/unit records. This is a lower-level scheme-test tool on the existing algebraic-space representability branch of the lissity/support proof. The parent `lem-a1-space-affine-etale-cover` uses exactly this item to prove continuity and etale openness in its final step. No chapter or unit text is changed.

`tools/blueprint_refs.py ancestor` identifies `lem-a1-affine-hc0`. Whole-blueprint searches for points cartesian, etale open, atlas and 03H4 found no equivalent imported node. The etale-open query returned unrelated purity/exchange definitions and an admissibility theorem. Whole-DAG searches for 03BX, 03H4, lemma-topology-points and lemma-points-cartesian located the existing point-lifting node, the parent and its sibling atlas-comparison node. The sibling assumes both maps are surjective etale and therefore does not prove this arbitrary-test-scheme assertion. The broader point-open-calculus node already uses the topology being constructed and is not cited, avoiding circularity.

The required msearch commands ran for this item: LeanSearch, Loogle, grep, and LeanFinder with two phrasings. Exact queries and returned records are appended to `mathlib_searches` and logged by msearch in `searches.jsonl`. No service was unavailable. Read the returned names/types: scheme covers and etale sites do not concern an algebraic-space target. The closest result, `AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback` (Mathlib/AlgebraicGeometry/PullbackCarrier.lean:420--429), assumes a pullback in schemes, including a scheme base; it cannot be applied to arbitrary E. Mathlib's `Scheme.SpecToEquivOfField` supplies scheme point representatives, not the entire assertion. Thus the item remains a split, not a Mathlib leaf. The existing open-map leaf's source was also read at Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean:48.

## Not duplicates

No new node is proposed. In particular, no duplicate of the existing 03H4 point-lifting node or of the scheme etale-open Mathlib leaf is introduced, and none of the item's clauses is moved into a new node.

## Review by Q10

I read Stacks spaces-properties.tex, `lemma-points-cartesian` (03H4), including its common-extension proof, and `lemma-topology-points` (03BX), including the presentation pullback square and openness argument. I also read morphisms.tex `lemma-etale-open` (03WT), spaces.tex `lemma-representable-diagonal` (025W), and the actual statements of all five cited DAG nodes. The source proves the scheme-test identities through the same pullback; extending the notation to arbitrary subsets introduces no topological assumption on E. No new node has a source to review.

Step 1 uses the exact scheme-test clause of `def-trf-algebraic-space`: w is representable, so Q is a scheme, and w is surjective etale, so its test projection q is surjective etale. This needs neither etaleness nor surjectivity of t. Both projections are morphisms of schemes, whose underlying maps are continuous by the locally ringed space definition in `def-pc-scheme`. The cited open-map leaf explicitly says that an etale scheme morphism sends each open subset to an open subset; applying it to q supplies precisely the missing openness assertion. No claim about openness of b is made here.

Step 2 uses `def-a1-algebraic-space-point-classes`, whose statement gives both the common-field relation and the residue-field representative of the map from scheme points. The residue-field maps at q(z) and b(z) put both classes over kappa(z); the equality of transformations in the pullback square makes those representatives equal there. This is the elementary point-map commutativity, not an unsupported assertion that point sets preserve fibre products.

Step 3 checks membership using that commutativity and then uses the already established surjectivity of q to obtain the image equality. Both inclusions are written. Step 4 takes a continuous inverse image under b and then an open image under q, identifying the result by step 3. These are elementary applications of the definitions of continuous/open maps to scheme spaces, requiring no quotient topology on E.

Step 5 uses the statement of `lem-a1-space-fibre-product-point`: two points in the scheme sources with equal images in the field-valued point set have a point in their sheaf fibre product projecting to the specified two points. Its hypotheses match C=T, U=W, c=t, u=w, with E algebraic and both sources schemes over S. The forward inclusion uses step 2; for the reverse inclusion, the chosen x in B and y in W satisfy exactly the equality required by that cited statement. Point lifting, not merely commutativity, is essential. I checked that this cited node's statement gives existence for the specified pair, rather than just nonemptiness of some fibre.

Step 6 uses the extra hypothesis on t only here: the scheme test of t along w is exactly b, and `def-trf-algebraic-space` makes b etale. The open-map leaf applies to b. Since q is continuous, q-inverse(B) is open when B is; the image identity in step 5 identifies its b-image with the required subset. This proves the final clause without introducing a topology on E. The only off-unit theorem cited is the existing Mathlib open-map leaf, which is automatically a tool; no non-leaf off-route theorem is used.

For section E I tested T empty (all relevant subsets/images are empty), E and W empty (surjectivity of w forces every scheme mapping to E to be empty), A empty or full, and B empty or full. With E a scheme and w its identity, the formulas reduce to ordinary set identities and etale openness. A noninjective fibre-product point map, such as Spec C times over Spec R with Spec C, causes no problem: step 5 requires existence, never uniqueness, of a compatible lift. The proof does not assume b surjective or etale before the final additional hypothesis. There are no quasi-compactness, separation, finite-type or affine hypotheses being used silently.

Against B--E: every non-elementary fact is cited by a node whose statement was opened and quoted in citations.json. The direct scheme tests and set calculations are kept as arguments rather than relabelled nodes. Existing dependencies are read literally; no proof-only construction from a cited node is used. The proof has no step longer than 2000 characters, no hidden standard comparison, no new statement requiring a small-case audit beyond the unchanged item, and no source-route departure. I corrected no imported statement; the substantive change is supplying the previously missing argument, including both reverse image inclusions.
