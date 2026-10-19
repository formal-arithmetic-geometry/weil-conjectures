# Q132 — lem-coef-simplicial-marked-cylinder-comparison

## Files written

- dag/nodes/sec-six-functors/lem-coef-simplicial-marked-cylinder-comparison.json — existing statement, split; no Mathlib match. The original statement and its two statement dependencies are unchanged. The proof is a two-stage computation of the homotopy mapping property, with the interval identification now justified explicitly.
- citations.json — verbatim current statements for every step/dependency pair.
- report.md — this report. Searches and the sandbox repair script are retained locally.

New nodes: 0. New Mathlib leaves: 0. No unit realization file is appropriate: this is a created descendant, not its unit's key statement.

## Attachments

None. Searches under /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag and for marked cylinders, walking groupoids, Bergner, and simplicial localization found no declaration stating this enriched marked-cylinder comparison. The exact upstream master was also searched for the tag and interval reference; its sorry declarations would not constitute an attachment in any event. There is no Lean audit on this created node requiring a different declaration to be inspected. No Lean file was written and no compiler, Lake or build was run.

## WANTED

WANTED: Jacob Lurie, Higher Topos Theory, archival copy of Appendix A.3.5 (Notation A.3.5.1, Lemma A.3.5.3, Proposition A.3.5.5, Lemma A.3.5.14) and A.3.6.17, for lem-coef-simplicial-marked-cylinder-comparison. I read the online primary source at https://people.math.harvard.edu/~lurie/papers/HTT.pdf on 2026-10-17; it is not archived under literature/. Accordingly proof_origin.by remains agent. No Stacks tag states this enriched homotopical comparison. No SGA source is used.

## What was wrong and what changed

The resumed sandbox had a proof and citations but no report and no active Q132 delivery process. Its first step silently identified the localization of the walking arrow with the walking groupoid. The current existing walking-groupoid function-complex theorem plus the framed-mapping theorem supplies precisely that identification after taking components; no new lemma is necessary. The old citation file also quoted a no-fibrancy sentence that is absent from the current universal-property statement. I replaced those citations with current statements and checked the actual hypotheses.

I kept the earlier horizontal-then-vertical route. Rather than transporting an unspecified image marking across an isomorphism, the new proof computes two restriction maps: the first inverts H, and the second inverts R_J. The literal formula s(v,1_e)=(v,1_e) identifies the second image condition with the remaining marking R on the original cylinder. Their composite therefore has exactly the required image, and injectivity supplies the isomorphism under the cylinder. Endpoint identities are proved by restricting along q, where injectivity applies. The explicit essential-surjectivity hypothesis is retained, although it is unnecessary for this proof. There is no statement dispute or weakening.

## Blueprint and searches

I read the chapter and unit records and the current main-20261015 statement and proof of prop-coef-integral-exceptional-adjoint. The ancestry is inherited through the comparison-calculus chain, ultimately supporting the derived coefficient adjunction in paragraph 2. The present work supplies the interval comparison within that chain; it does not replace a unit-level argument or change the chapter route. The item's blueprint.from.place was already specific and remains so. blueprint_refs.py ancestor confirms the ancestor. Searches of all blueprint nodes for marked cylinder comparison, walking groupoid, simplicial localization and marked found no node stating the item in another form; same_as stays empty. DAG concept searches found the product-parameter and walking-groupoid support nodes and the parent comparison-calculus node, which uses this item and cannot be cited back.

The earlier sandbox searches.jsonl survives. I read its hits, preserved the inherited search records, and added its distinct actually logged searches to the item with the exact tool/query text. The two semantic phrasings in that log return ordinary localization/product constructions and simplicial-set homotopy categories, not the Bergner marked-cylinder theorem. I read Mathlib/CategoryTheory/Localization/Prod.lean:110-145, particularly Functor.IsLocalization.prod at line 139, and OfQuotient.lean:65-90. These concern ordinary categories and do not specialize in one line to this item. The additional msearch.py grep on Prod.lean is logged; because its subargument is a single file the command's output labels are line numbers 19 and 139 rather than filenames, and the known subargument supplies the file. No search not actually run has been added. The item is not a Mathlib leaf.

## Not duplicates

No new node is created. The existing product-parameter theorem localizes only arrows in one factor; the walking-groupoid theorem identifies a function-complex restriction; neither states this cylinder's combined marking and endpoint comparison. Their combination is the proof here. The parent comparison-calculus theorem uses this item, so it is not a usable proof dependency.

## Review by Q132

I read delivery-errors B through E in full against the node, not just the mechanical checks. For the item I read HTT's online Notation A.3.5.1 and subsequent universal-property discussion, Proposition A.3.5.5 (printed p.893), Lemma A.3.5.14 (printed p.896), and the final interval argument of Lemma A.3.6.17 (printed p.904). The source gives the product and localization route; the detailed composition of restriction maps is written out here. There are no new nodes with additional literature to check.

For step 1 I opened the entire statements of lem-coef-simplicial-walking-groupoid-components, lem-coef-simplicial-derived-pushout-mapping, and lem-coef-simplicial-inversion-universal-property. The first explicitly gives a weak equivalence onto the union of invertible-arrow components, the second explicitly identifies components of framed mapping complexes with homotopy-category morphisms compatibly with restriction, and the third characterizes localization by the resulting injective image condition. This repairs the previously unsupported interval identification. The target can be replaced fibrantly by the cited statements; no fibrancy of A is introduced.

For step 2 I read the full product-parameter statement: with C=[1], D=A and W={t}, its marked set is exactly H after the explicit factor symmetry. It states the canonical comparison induced by the localization unit, so the comparison is under B. The universal-property statement then gives exactly the claimed restriction injectivity and image. For step 3 the same two statements apply with C=A, D=J and W=V, giving precisely R_J, not any saturated or enlarged marking. The two-object set is unchanged by [1] to J, so the map of R is literally onto R_J.

For step 4 I checked both directions of the image criterion. A class inverting U first extends uniquely across s because it inverts H; its extension inverts every element of R_J because all these elements are images of elements of R. Conversely a class on the final product restricts to a U-inverting class. The framed-mapping statement gives functoriality on path-component categories up to natural isomorphism, so the invertibility tests remain valid for homotopy classes rather than only strict representatives. The uniqueness clause is used to produce inverse maps under B; this is an elementary application of the already cited mapping properties, not an uncited associativity theorem for homotopy pushouts.

For step 5 the universal-property statement explicitly supplies localization functoriality compatible with composition and restriction injectivity. The endpoint functor sends V into U, hence k_e exists with the stated restriction. The two composites out of L_VA agree after q, so that exact injectivity proves the endpoint equality. I also rechecked the arbitrary-mapping-set and no-saturation clauses in product-parameter and walking-groupoid-components instead of relying on the stale sentence in the old citation file. Every target used is small in the fixed universe. All four proof dependencies are in the same unit as the item, so no off-route tool use is needed.

Small cases: A empty gives empty categories on both sides and no markings; A a point and V empty gives the walking-arrow localization J; V empty for arbitrary A leaves only H and reduces to the first product comparison; identity markings impose no condition; A=[1] with V its distinguished arrow inverts all four sides of the square and yields J times J. The proof treats a set V with repeated endpoints or identities without requiring a subcategory or saturation. Neither essential surjectivity nor local Kan conditions were smuggled into a product comparison.

For B, the only delivered node is existing, its TeX and statement are retained, every new notion in the argument is introduced, and no new statement-only node or Mathlib leaf needs a source audit. For C, every non-elementary input is one of the four opened statements and has a verbatim quotation in citations.json; no citation uses a proof body or a definition as an extra theorem. For D, the proof carries the argument rather than moving a clause into a new node, and its mapping-property uniqueness argument is explicit. For E, the sets H, R, R_J and U, all comparison maps, endpoints, target sizes and lack of fibrancy/saturation assumptions were checked directly. Every step is below 2000 characters, so no long step hides a further lemma. The statement is unchanged and no source error was found.

## What remains

No mathematical part of this one-level split remains. The four existing support nodes remain dependencies of the project and are not modified by this delivery. Server dry run and direct push are the final validation and delivery steps; their results follow below.
