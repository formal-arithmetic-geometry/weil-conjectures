# Stage-1 worker report: lem-sfb-dg-finite-cell-compact

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dg-finite-cell-compact.json`: statement split, with its original statement and statement dependencies unchanged; no exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-dg-derived-admissible-triangles.json`: new statement-only node, unsplit; no Mathlib match. It states the DG derived triangulation and the triangles for graded-split short exact sequences, without a finite-cell or compactness hypothesis or conclusion.
- `citations.json`: seven verbatim statement quotations, one for every step/node incidence.

## Attachments

None. Searched the live project's `lean/WeilConjectures/` for the item id, finite-cell/semi-free phrases, DifferentialGraded and DGModule, and related DG-module/projective-complex names. No project declaration states this item. Ordinary Koszul complexes, sheaf Ext and category compactness do not attach the general DG-algebra theorem.

## WANTED

None. All sources used for the split and new statement are present in `literature/stacks-project/`.

## Findings and corrections

The item agrees with Stacks 09R3, proposition-compact (2) => (1), using the identity retraction. It was unsplit with no proof; there was no sandbox attempt or report to recover. There is no released repair note. The statement needs neither countability of A nor any boundedness of its cohomology. I did not change it.

I initially considered creating a free-DG-module Hom lemma, but the statement of `lem-coef-dg-module-projective-resolution` already gives its non-elementary input in greater generality. Step 1 now writes the evaluation-at-one argument and applies that existing mapping-complex formula, so there is no extra node for this special case. I likewise reuse the coproduct clause of `lem-sfb-dg-sequential-colimit-triangle` rather than create a coproduct node.

The ancestry command returns `None`: the created.item chain ends at `Sheaf.SixFunctors.CtfStabilityDirectImages`, although `lem-sfb-admissible-direct-image` records det-thm-sf-ctf-stability-direct-images as its blueprint parent. I retained the inherited null ancestor and the complete via chain, and extended the precise source place for the new node. I read the latest blueprint (current snapshot main-20261024), in particular paragraph (3) of sk-thm-sf-ctf-stability-direct-images.proof.md, the unit record and chapter record. This is supporting DG infrastructure for the existing coherent-family/Quot telescope route, not a replacement for the direct-image proof. No unit realization is edited: this item is not its key statement.

## Not duplicates

The whole DAG and blueprint were searched for 09K1, 09KY, 09QI, 09K6, 09K8, 09KJ, 09KW, 09KX; for compact, admissible short exact, graded split/graded-split, graded submodules, shift-free and DG module; and the live source was searched for the corresponding notions. No existing node has the new statement. No existing DAG source cites any of the new node's five source tags. The following closest comparisons explain why the new input is still needed:

- lem-sfb-dg-derived-admissible-triangles vs lem-coef-dg-abc-homotopy-category-triangulated: the latter triangulates H^0 of an abstract dg category satisfying (A),(B),(C); it does not assert that the DG-module quasi-isomorphism localization is triangulated or that localization preserves the specified triangles.
- lem-sfb-dg-derived-admissible-triangles vs lem-coef-dg-module-cone-triangulation: the latter is a homotopy category of labelled modules closed under strict cones; it does not localize at quasi-isomorphisms.
- lem-sfb-dg-derived-admissible-triangles vs lem-sfb-dg-sequential-colimit-triangle: the latter has coproducts and a sequential telescope triangle, not the triangles of arbitrary graded-split short exact sequences.
- lem-sfb-dg-derived-admissible-triangles vs lem-coef-dg-module-projective-resolution: the latter computes derived mapping complexes and gives replacements, not the distinguished triangles needed for filtration induction.

## Mathlib searches

Every query recorded in the item additions and the new node was run through msearch.py and is retained as emitted in searches.jsonl. Both formulations of each question were read. LeanSearch, LeanFinder, Loogle and source grep all answered. Loogle's ShortExact/distinguished hit is `CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished`; the stronger-looking search hits are `DerivedCategory.triangleOfSES_distinguished` and `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`. I read ShortExact.lean:31-93 and DegreewiseSplit.lean:31-95: their objects are ordinary cochain complexes over one abelian category, rather than modules over an arbitrary DG algebra with a differential on the algebra. The Hom/Ext hits have the same limitation; I also read HomComplexCohomology.lean. Applying them here requires DG-module and localization constructions, not one specialization. No new Mathlib leaf is claimed.

## Review by Q40

I read dga.tex 09R3, proposition-compact, especially its final paragraph, against the entire item. It reduces finite-filtration compactness to finite sums of free shifts exactly as our split does. I checked 09K1, lemma-hom-from-shift-free, and 09KY, lemma-hom-derived, to ensure the free-shift formula is a statement about the DG derived category, rather than just the homotopy category. I read 09QI, lemma-derived-products, clauses (1) and (2), and derived.tex 09QH, lemma-compact-objects-subcategory. For the new node I read 09KJ, proposition-homotopy-category-triangulated; 09K6, lemma-triangle-independent-splittings; 09K8, definition-distinguished-triangle; 09KW, lemma-acyclic; and 09KX, definition-unbounded-derived-category. The precise arrows in its triangle are the inclusion and quotient, and graded splittings need not commute with d. No SGA source is involved.

Step 1 uses only the mapping-complex clause of the existing general projective-resolution node. I opened its full statement: homotopically projective means Hom into every acyclic module is acyclic; it explicitly asserts that the ordinary Hom complex computes the derived mapping complex for such a source, compatibly with localization. The single-object dg category has composition the multiplication of A and right modules exactly the modules here. Evaluation at 1 identifies degree-r maps with M^(r-k); d(1)=0, so their differential evaluates to d_M. This proves the hypothesis on A[k], and degree-zero cohomology gives H^(-k)(M), naturally for the strict coprojections we use. This is a short computation using a cited theorem, not an uncited projective-resolution existence argument.

Step 2 takes only the explicit arbitrary-small-coproduct clause from the existing telescope node, which I opened and quoted. It does not take a coproduct result from that node's proof. The coordinates of a cycle have finite support and a finite family of boundary coordinates has a finite family of preimages; I wrote both directions so the cohomology/direct-sum comparison needs no hidden exactness theorem. Naturality of Step 1 identifies this with the canonical map in the compact-object definition, whose full statement I opened and quote.

Step 3 uses only that compact-object definition plus the additive universal property of a finite direct sum. I wrote the finite union of supports which interchanges the finite product with the arbitrary direct sum. It includes the empty finite sum. This two-line elementary consequence is not a new finite-sum compactness node.

Step 4 checks the graded-splitting hypothesis of the new triangle node, rather than assuming that all short exact sequences split. Each quotient has a graded free homogeneous basis because it is a finite sum of shifts of A; lift those generators homogeneously through the degreewise surjection and extend A-linearly. The resulting section is only graded, precisely what the new statement requires. The new node then gives the displayed triangle with the actual filtration maps. This construction is elementary from the stated free basis; the non-elementary DG exact-triangle theorem has its own node.

Step 5 uses the full statement of lem-sc-compact-objects-thick: it explicitly includes zero and isomorphism invariance and closure under distinguished triangles, for the universe of the given coproducts. The new node supplies the triangulated hypothesis and the reused telescope node supplies all small coproducts. The induction starts at F_(-1)=0, applies compactness of each finite-sum quotient, and concludes compactness of each middle term, ending at P. I checked that the cited nodes' statement/proof dependency closures contain no reference to the item, so none introduces a cycle. The two off-unit statements are declared as generic tool uses in split_report; neither replaces the unit's route.

Small cases checked: P=0; r=0; zero quotients; an empty sum; A=0; A concentrated in degree zero, recovering the bounded finite-free complex case; negative and positive shifts (the generator of A[k] has degree -k); and a DG algebra of uncountable cardinality. The new triangle node includes K=0, M=0 and a graded splitting with nonzero off-diagonal differential. That last case gives a nonzero connecting map, so it is essential that no differential-compatible splitting be asserted. An infinite free sum of copies of a nonzero ordinary ring would not pass the finite-support factorization argument for the source; the statement's finiteness is used at exactly Step 3 and in the induction length.

I checked delivery-errors B through E point by point with the files open. The one new node is self-contained with inline DG definitions, exact source tags, definition dependencies and genuine search results; its proof and proof_deps are empty. It neither restates finite-cell compactness nor gives compactness as any clause. All non-elementary inputs are cited statements, with exact quotations in citations.json, and each elementary calculation is written out. All five steps are shorter than 2000 characters (790, 691, 608, 555, 566). The only correction made during this self-review was eliminating the prospective duplicate free-Hom node in favor of the general existing statement. Nothing mathematical remains unfinished in the item's split; the new input is deliberately statement-only for its next stage-1 worker.

## Unfinished work

None for this delivery. The new statement is queued unsplit as required.
