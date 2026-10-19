# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-invertible-interval-product-projection.json`: statement, split; Mathlib verdict no match. Four proof steps, no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotations for all seven step citations.
- `searches.jsonl`: five actual search records from the required search command, including a second semantic phrasing; all services answered. Existing item searches were preserved.
- `report.md`: this report and the author's review.

## Attachments

None. Searches of the read-only slopmaster2 `WeilConjectures/` by the exact blueprint id and by categorical equivalence, Joyal, walking isomorphism and invertible interval found no candidate project theorem. The upstream-name index has no binding for this item. There is no Lean attachment or declaration to audit transitively.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Corollary 2.2.5.4, Proposition 1.2.7.3 and Proposition 2.2.5.8, for lem-coef-invertible-interval-product-projection; https://people.math.harvard.edu/~lurie/papers/HTT.pdf, read online but no local archival copy found.

WANTED: Denis-Charles Cisinski, Higher Categories and Homotopical Algebra, July 30, 2026 revision, Remark 3.6.5 and Theorem 3.6.8, for the cited test-functor criterion; https://cisinski.app.uni-regensburg.de/CatLR.pdf, read online but not archived locally.

No source was downloaded or written into the shared repository. The proof is marked agent-written: it gives an explicit contraction for this particular interval, rather than claiming to reproduce the general product theorem's proof. No Stacks tag states this quasicategorical result.

## Findings and changes

The statement is correct as imported, including arbitrary small R and arbitrary input universes. It was kept verbatim. The source pointed to the general product theorem but the item had no proof. I supplied the nerve contraction, its parametrized action on every simplex of the functor object, the two inverse-triangle witnesses, and the existing test-functor criterion. I did not replace the problem by ordinary equivalence of R, assume R is a quasicategory, or add a general product-preservation theorem as a new node.

The existing definition node supplies the degreewise products, nerve, internal Fun, and definition of coherent natural equivalence. The existing `lem-coef-joyal-functor-equivalence-test` states both the required internal-Hom fibrancy and equivalence of the testing conditions. `lem-coef-joyal-model-structure` states the item's exact categorical-equivalence convention. The two theorem nodes are in the same unit as the item; the definition node is in sk-prop-sf-cbc, which is allowed because definitions specify notions rather than a proof route. Its source ancestor is the paragraph computing the mapping-complex adjunction in `prop-coef-integral-exceptional-adjoint`; the immediate auxiliary use remains step 3 of `lem-coef-join-slice-cocone-comparison`. The chapter and unit records were read and are unchanged; this auxiliary item is not a unit's key statement.

## Not duplicates

There are no new nodes. Whole-DAG searches for categorical equivalence, walking isomorphism, invertible interval and HTT 2.2.5.4 found the existing test-functor and interval infrastructure. Blueprint searches `invertible interval` and `categorical equivalence` found no blueprint node stating this result; `groupoid` found seven unrelated geometric blueprint nodes. `blueprint.same_as` remains empty. In particular `lem-coef-quasicategory-invertible-interval` concerns maps from the interval to quasicategories and endpoint evaluation, rather than arbitrary R times the interval; its stronger infrastructure is unnecessary for the explicit contraction proof.

## Mathlib search assessment

The new queries and their exact responses are recorded in searches.jsonl and appended to mathlib_searches. I read the returned signatures and Mathlib's `AlgebraicTopology/SimplicialSet/CoherentIso.lean` (walking isomorphism at line 39, coherentIso at line 141, and inverse data through line 214), plus `NerveCodiscrete.lean` (equivFun at line 33). They construct the interval and its inverse triangles. The other hits describe nerves and two-truncations, products of standard simplices, or ordinary natural-isomorphism constructors. They do not state categorical equivalence of this projection, and obtaining the claimed test-functor equivalence still requires the contraction calculation. No hit is a one-line specialization of the item. The two different LeanFinder phrasings both returned this more elementary nerve/homotopy-category material.

## Review by Q121

I read HTT Corollary 2.2.5.4 (printed p.92), Proposition 1.2.7.3 (printed p.39) and the testing-convention discussion and Proposition 2.2.5.8 (printed pp.94-95), and Cisinski Remark 3.6.5 and Theorem 3.6.8 (printed pp.114-116). HTT allows the product factor to be an arbitrary simplicial set. The source's general theorem confirms the statement, but the actual proof below is the explicit agent argument recorded in the node. Cisinski's theorem confirms the literal (ii) to (iii) implication used, and that there is no fibrancy assumption on the domain X of the tested map. There are no new nodes whose sources or hypotheses require a separate review.

Step 1 uses `def-cbc-enhanced-diagrams-cones`: I opened its statement and checked the nerve is functors from [n] and product operators act on each coordinate. Because every morphism of this particular groupoid is unique, object strings specify every nerve simplex; the Boolean formula commutes with restriction, including repeated entries. This proves the section and contraction directly, rather than using an uncited theorem that nerves preserve equivalences or products. It is elementary computation from the cited definitions.

Step 2 uses that definition's precise internal Fun formula and the first assertion of `lem-coef-joyal-functor-equivalence-test`. I opened the criterion statement: for an arbitrary small map A to B it explicitly says both functor simplicial sets into each quasicategory C are quasicategories. With A=X=R times I and B=R, these are exactly D and E. Thus the source hypothesis here is on C, not R. The identity QP is checked by precomposing with the section-projection composite in every parameter degree, not only on vertices.

Step 3 uses only the internal Fun and simplicial-operator definitions in `def-cbc-enhanced-diagrams-cones`. I checked types: F has domain X times Delta^n, t has domain Delta^n, and beta is an m-simplex of Delta^n, so t beta and a are both m-simplices of I. Kappa retains beta and r. The equality after restriction by gamma verifies the map into X times Delta^n. The separate parameter-restriction check proves K is a simplicial map on D times I. Currying is specified by the actual formula, not cited as an unidentified comparison theorem. This is elementary substitution in the definitions, with no hidden lemma about general homotopies.

Step 4 uses the definition node's exact inverse-triangle notion of coherent natural equivalence, the criterion's (ii) implies (iii), and the Joyal node's exact hFun testing definition. I checked that the two long edges in strings 010 and 101 are identities in the groupoid, hence degenerate in its nerve. Simplicial maps preserve them, so the two image triangles are precisely the two inverse witnesses, with endpoints PQ and identity. QP is strict identity, so its witness can be taken degenerate. This supplies a coherent functor equivalence of the specified precomposition map P, not merely an unrelated equivalence of D and E. The criterion then produces the required ordinary-category equivalence. Each cited statement literally supplies what is used; the verbatim statements are in citations.json. No pointwise-equivalence theorem is used implicitly.

For E1-E7 I checked empty R, R=Delta^0, R=Delta^1, and shapes R with unfilled inner horns. The formulas are defined on every degree and never select a vertex or a filler of R. When R is empty, both functor objects are terminal, even for empty C. When R is nonempty and C is empty, both functor objects are empty and the maps still exist, so the universal testing condition causes no nonemptiness exception. All output strings have the same finite degree as the input strings. Products remain small in the original universe; the testing construction is repeated in any containing universe. No finiteness bound is needed. I checked that the existing criterion's statement and proof dependencies do not reach the item (60 nodes inspected by a read-only dependency traversal), so its use introduces no cycle.

For B1-B10, there is no new unsplit node, no statement-only clause masquerading as a lemma, no new definition, no alleged Mathlib leaf, and no attachment claim. All notions have the two existing statement dependencies, and the elementary constructions were kept as proof steps. For C1-C8 every non-elementary input is a cited existing statement, all quotes were checked against the actual JSON statements, and proof_deps is the union of the uses lists. No other-unit statement tool use is present; the definition node is an allowed notion from another unit. For D1-D5, the proof contains the contraction and its action on functor objects rather than renaming the result or citing the source's omitted details. No step exceeds 2000 characters. I corrected the draft step sources to name Cisinski's exact criterion at steps 2 and 4; the statement itself required no correction. There is no STATEMENT-DISPUTED issue, no weakened clause, and no unfinished mathematics.

## Unfinished work

None for this stage-1 split. Archival copies requested above remain a literature-maintenance task; the proof is explicitly marked agent-written in accordance with the brief.
