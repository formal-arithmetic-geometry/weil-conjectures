# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-latching-degenerate-subset.json`: statement, split; no exact Mathlib match for the latching colimit. Six proof steps use only the two existing definitions and the existing Mathlib leaf for unique nondegenerate decomposition.
- `citations.json`: all 12 step/node pairs, each with the verbatim statement of the cited node.
- `searches.jsonl`: actual msearch results for this attempt, retained for audit.
- `report.md`: this report and self-review.

No new nodes; zero new Mathlib leaves. No unit records, Lean files, live files, launcher files or shared-repository files were written. This resumed attempt found the completed six-step split, report, citations and search log from the earlier worker. I retained them, compared the item with the current repository, and started the required dry run before making repairs. The original creation record (Q57, parent lem-coef-bisimplicial-reedy-division-calculus) is restored; Q103 is the splitter, recorded in split_report, rather than the creator of this existing node.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the full blueprint id, by latching/degenerate terminology and by the source tag; also searched Comparator by the id. No project declaration states this item. The upstream master was treated only as reference. The existing normal-form result is already a Mathlib node, not a project attachment.

## WANTED

None needed for this proof. The Joyal–Tierney Section 2 context is not archived in the literature directory; this split does not claim to follow that unarchived proof. Its mathematical source is the archived Stacks Tag 017R, and the explicit latching-colimit argument is marked `proof_origin.by = agent`.

## Findings and changes

The repository item remains statement-only; the earlier sandbox attempt already supplied the split. Its statement, source, chapter, unit and blueprint ancestry are retained, and its statement dependencies already name exactly its two external notions. There is no statement dispute or correction. The warning after Stacks 017R matters: a simplicial map can take a nondegenerate simplex to a degenerate simplex, so functoriality of the nondegenerate splitting is unavailable. Step 6 instead proves the naturality of the degenerate-subset colimit maps from the naturality equation on every proper surjection.

The proof constructs a colimit cocone directly on the set of degenerate simplices. Thus it does not silently need an uncited theorem on existence of arbitrary set colimits, or a quotient presentation of a chosen colimit and its element representatives. The ordinary universal-property definition suffices. The direction of the decisive arrow is `tau -> sigma`, where `tau = rho composed with sigma` and `y = T(rho)z`.

Whole-DAG searches included `017R`, latching/proper-surjection and nondegenerate terminology. Whole-blueprint searches for latching and for nondegenerate found no blueprint statement of this item; `same_as` remains empty. The existing `lem-weil-pbc-simplicial-set-nondegenerate-decomposition` is reused. `SimplicialObject.Splitting.isColimit` is a coproduct of nondegenerate summands with a discrete index, rather than the colimit of full lower-degree simplex sets with their transition maps. Likewise `SSet.isColimitCoconeN` is the colimit of monogenous subcomplexes. Neither is a one-line specialization for the item. No duplicate or auxiliary child node is necessary.

Searches were run through msearch and their actual records are appended to the item's existing search history. Two semantic phrasings, LeanSearch, Loogle and grep were read. One Loogle name query reported an unknown identifier; this is recorded as an invalid name query, not evidence of absence. A single-file grep caused msearch's printed file/line fields to be malformed; the source was read directly and a directory grep repeated the same question with correct paths and lines. The final directory query finds Split.lean:212, 229 and 233. This is only a search-output formatting issue; no launcher modification or workaround was made.

## What could not be finished

Nothing mathematical remains for the assigned one-level split. The required dry run and push follow this report.

## Review by Q103

I read Stacks `simplicial.tex`, Lemma 017R (`lemma-splitting-simplicial-sets`, source lines 1795–1815), the splitting formula preceding it, and the paragraph immediately after it about failure of functoriality. The tag map confirms 017R. I also read `categories.tex`, Definition 002F (`definition-colimit`, lines 1309–1335) and its empty-diagram explanation. The item is a consequence of 017R, not its literal statement: the report and proof origin distinguish those facts. I read the chapter record, unit `sk-prop-sf-biduality-general`, the current blueprint ancestor's proof paragraph 2 in `main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/`, and parent `lem-coef-bisimplicial-reedy-division-calculus` step 3. This calculation supplies the parent's latching identification and its naturality in inner simplicial operators; it does not replace the unit's adjunction or biduality route. The only external statement used is already a Mathlib leaf, and both other dependencies are definitions/Mathlib notions, so no additional off-unit tool declaration is required.

I opened the complete statements of every cited node. In particular the normal-form node asserts uniqueness of the integer, surjection and nondegenerate simplex, which is exactly the uniqueness needed here; it is not merely existence or a definition of splitting. The colimit definition asserts factorization and uniqueness, not a general existence theorem, so the proof explicitly constructs the candidate colimit before comparing with a chosen one. The simplicial-set definition includes arbitrary lower-dimensional maps in the degeneracy definition and natural transformations as morphisms; both clauses are used as written.

Step 1 uses the simplicial-set definition for contravariance and the colimit definition only for what a cocone/universal property means. The transition equation is written with correct variance: when sigma = rho composed with sigma', T(sigma') composed with T(rho) = T(sigma). Finiteness is enumeration of maps between fixed finite sets and gives smallness, as required by the colimit definition.

Step 2 uses the entire normal-form theorem and the actual arbitrary-map definition of degeneracy. I checked the missing comparison carefully: factor f by enumerating its nonempty image, decompose the resulting simplex, and use uniqueness. The surjections impose b <= a <= m < n, so the normal-form object is a proper surjection. This avoids assuming without proof that the source definition already restricted to surjective maps. There is no new hypothesis such as finiteness or nonsingularity of T.

Step 3 uses the normal-form node both on y and on j_sigma(y), and the colimit definition for the equation of an arbitrary cocone. I checked that r <= k < n makes both tau and sigma legitimate indexing objects, including rho = identity. The arrow tau -> sigma is precisely the one declared in the item's statement. The written equation proves descent on every y, not only on nondegenerate y. No non-elementary comparison is omitted.

Step 4 uses just the normal forms already obtained and the universal-property definition: every x equals j_tau(z), forcing uniqueness. In degree zero the diagram has no objects and the degenerate set has no elements, so the construction and uniqueness reduce to the empty function. There is no unjustified assumption that the index category is nonempty or filtered.

Step 5 is the two universal-property factorizations, with their inverse equations checked after each structure map. The composite into T_n has exactly the same cocone maps as lambda_n. Thus the identification is with the specified canonical lambda_n, rather than with an unspecified bijection. Injectivity and the image statement then follow from a bijection followed by the subset inclusion.

Step 6 uses the natural-transformation clause and colimit universal property, with the equation phi_n T(sigma) = T'(sigma) phi_k displayed. That equation proves preservation of degeneracy and commutation on each structure map. Colimit uniqueness gives naturality of the identifications. Nothing assumes preservation of nondegenerate simplices. I checked the extreme example Delta[1] -> Delta[0], which collapses the nondegenerate edge, to ensure that the proof still applies.

For small cases I checked n=0, n=1 (only the surjection [1] -> [0], so the claim is the injectivity of the constant-edge degeneracy), the empty simplicial set in all degrees, and a constant simplicial set in degree 2. In the last case the two [2] -> [1] representatives agree in the colimit through the common [2] -> [0] representative, with arrows in the direction used in step 3. General simplicial sets may be infinite; no step depends on their cardinality. All six proof steps are below 2000 characters (lengths 785, 960, 885, 539, 793, 804), and the only substantive ingredient is separately cited. No standard lemma is hidden inside a long step. These checks cover delivery-errors B–E: no new-node form issue, every non-elementary citation says exactly what is used, no relabelling of an item clause as a child, and all dimensions, variance and naturality hypotheses verified.

## Resumed review by Q103

I reread the complete split and all three cited statements against the current repository, Stacks 017R and 002F, and the pinned Mathlib normal-form declarations. The statement and blueprint ancestry still agree with the repository. I checked every step/node citation quote as a verbatim substring and verified all 12 required pairs are present. The indexing arrow in step 3 is from the composite proper surjection to the original proper surjection, so its cocone equation is in the correct direction. Normal forms are used only to construct the universal factorization; step 6 proves naturality on structure maps, without assuming nondegenerate simplices are preserved. There is no additional hypothesis or hidden comparison lemma.

I repeated the project-source attachment check by exact item id and by latching/degenerate terminology throughout WeilConjectures and by the item id in Comparator: there is no matching declaration. I read and retained the earlier logged search results, including three later searches omitted from the item's search list, and added those actual records to mathlib_searches. No search was repeated or invented. The invalid Loogle identifier is explicitly recorded as unavailable. I restored the original creation metadata rather than attributing the preexisting item to this split. The mathematical proof is retained unchanged. No new node is introduced, so no duplicate-pair section is needed.
