# lem-coef-chunk-bifibrant-localization

## Files written

- dag/nodes/sec-six-functors/lem-coef-chunk-bifibrant-localization.json: item, statement, split into six steps; statement unchanged, not a Mathlib leaf.
- dag/nodes/sec-six-functors/lem-coef-enriched-natural-localization-homotopy.json: new statement-only lemma, unsplit; not a Mathlib leaf. This is a general relative simplicial-category transformation lemma, with no model-category or chunk hypothesis.
- citations.json: verbatim statements for every per-step citation.

Retained dag-node.json and all earlier searches.jsonl records. The interrupted attempt contained no split, report, or delivery result, so there was no interrupted deliver.py invocation to repeat. No Lean written, no compiler or Lake invoked, no live project/launcher modifications, no agents started.

## Attachments

None. Searches for the blueprint tag and bifibrant, Dwyer--Kan, enriched natural and chunk terminology in /home/ubuntu/weil-src-slopmaster2/WeilConjectures found no declaration stating this enriched comparison. Ordinary Mathlib model-category localizations are not an attachment of a project theorem.

## WANTED

WANTED: Jacob Lurie, Higher Topos Theory, https://people.math.harvard.edu/~lurie/papers/HTT.pdf, Lemma A.3.6.17, printed p.904, for the item and lem-coef-enriched-natural-localization-homotopy. Read the entire lemma and proof online (PDF page 922, zero-based 921); no archival copy was found in literature. The proof is therefore marked agent, with the external source and exact place recorded. This assertion has no Stacks tag; no SGA source is used.

## Corrections and source audit

No statement dispute or statement change. The starting node had no proof. Its empty-cofan closure already provides enriched cofibrant replacement inside the chunk; a global replacement need not preserve the chunk and was not used. The nonempty one-fan closure ensures that a factorization used to invert a bifibrant weak equivalence has its intermediate object in U. The final functor need not commute with replacement: naturality concerns inclusion followed by localization.

The imported comparison-calculus node proves an interval argument in its proof, but its statement does not assert the general natural-transformation lemma. C4 therefore forbids citing that proof as a black box. The new node makes that independent assertion available. Its future proof can encode the transformation by C times the discrete walking arrow, invert the source markings and all vertical identity arrows, and use lem-coef-simplicial-inversion-product-parameter twice to identify the result with L_V C times the walking groupoid. The two endpoints become the same inverse to projection. For extra objects in a representative of L_V C, essential surjectivity of localization supplies the missing vertical inversions; this follows from its homotopy mapping universal property by factoring through its full essential image. This is the interval argument in the source, rather than an assertion that an arbitrary ordinary transformation is already a simplicial homotopy.

## Not duplicates

lem-coef-enriched-natural-localization-homotopy vs lem-coef-simplicial-localization-comparison-calculus: the latter's statement contains localization at existing equivalences, the whole-model-category comparison, and homotopy limits; it contains no general assertion about an enriched transformation between arbitrary relative simplicial functors. Such an argument appears only in its proof.

lem-coef-enriched-natural-localization-homotopy vs lem-coef-simplicial-inversion-universal-property: the latter gives injectivity and image on homotopy classes of functors, not how an enriched natural transformation identifies those classes.

lem-coef-enriched-natural-localization-homotopy vs lem-coef-simplicial-inversion-product-parameter: the latter is the product/localization comparison; the new statement is a consequence requiring the interval and both markings, and states a different general tool.

lem-coef-enriched-natural-localization-homotopy vs lem-coef-enhanced-localization-universal: the latter concerns D(Z)-enriched infinity categories and dg enrichment, not simplicial-enriched categories or the Bergner model homotopy category. No identification of those coefficient/enrichment categories is made.

Whole-DAG searches by transformation, localization and exact candidate names, plus whole-blueprint searches for cofibrant, bifibrant, enriched natural, natural transformation and localization, found no matching node statement. Checked nearby dk-cofibrant-localization-comparison and cofibrant-simplicial-inversion: these concern degreewise inversion and hammock comparison, not this relative transformation assertion. No new node repeats a Stacks tag.

## Review by NN

I read the standing brief, stage 1, worker role, SETUP's three blueprint levels, GOAL, dag-sync and delivery-errors B through E. I read the recorded chapter and unit, the nearest ancestor's current 20261015 proof, both statement dependencies, and the complete statement of every cited node. This remains the inherited enriched-localization foundation under paragraph 2 of the integral exceptional-adjoint argument. The item is not the unit key statement, so no unit realization is changed.

For step 1, the empty cofan gives the initial-object factorization by the item's hypothesis; the projective-model-calculus statement supplies the model and enriched conventions. Cofibrancy, fibrancy by composition, and preservation of weak equivalences are written out. Enriched functoriality is explicitly assumed in the item, not inferred from arbitrary ordinary functorial choices.

For steps 2 and 3, the one-fan supplies the intermediate object in U. The domain is cofibrant and the codomain fibrant, so its intermediate object is both. I checked both lifting squares for r and s and both SM7 substitutions against the exact statement of simplicial-projective-model-calculus. The Kan-Quillen node explicitly gives boundary lifting for trivial fibrations, including the boundary in dimension one used to join the two indicated vertices. Fullness of U gives exactly the actual mapping sets used in the component-category calculation. The inverse is rs, and both products with f are computed explicitly.

Step 4 uses only the localization-at-already-invertible-arrows clause of simplicial-localization-comparison-calculus. That statement applies to U^{cf} once step 3 is proved. The separate inversion-universal-property statement gives induced maps and compatibility with composition. No theorem about the entire ambient model category is silently applied to a chunk.

Step 5 uses the new node twice, once with markings W and once G. Step 1 verifies both preservation and component hypotheses. The statement of model-localization-detects-weak-equivalences has no bifibrancy restriction on a morphism, so it applies to bar i in the Bergner model category supplied by inversion-universal-property. Both inverse equalities are displayed before this detection step. The canonical composite is inclusion followed by localization, not a functor secretly involving the chosen Q.

Step 6 uses the explicit functoriality of derived-pushout localization asserted in comparison-calculus and the restrictions hypothesized for F. I checked the equality of the two composites, including the distinction between functorial model choices and the model-independent equality in the homotopy category. No extra hypothesis on F appears.

For the new node, I read HTT's interval paragraph on p.904 and checked the arbitrary-source formulation against the stated product/localization and homotopy mapping universal properties. I tested empty C, empty markings, identity transformation and the walking-arrow transformation: empty C gives the unique maps, empty W allows a transformation only when it has no components, an identity transformation requires identities among W as stated, and the walking-arrow example requires its component to be inverted. There is no implicit saturation or fibrancy hypothesis. The statement explicitly defines enriched naturality as equality of simplicial composition maps. It contains no proof and is strictly different from the item's chunk comparison.

I reused prior semantic searches after reading their logged hits and ran the current exact-query searches recorded in the new node. Loogle and LeanSearch return ordinary localization extension/lifting of transformations; their signatures and Mathlib's Construction/Predicate sources do not assert equality of enriched localization maps in h(sCat). LeanFinder returns ordinary model localizations or truncated simplicial homotopy-category facts. The grep for enriched localization, Dwyer or Bergner in CategoryTheory has zero hits. The earlier alternative semantic phrasing is retained too. Thus no one-line Mathlib specialization was found. The item's original recorded searches are preserved unchanged.

I checked B1-B10 (statement-only new lemma, complete hypotheses/definitions, genuine logged searches, blueprint ancestry, no exact Lean attachment), C1-C8 (every non-elementary input stated by a citation, all statements opened, verbatim citation ledger, no use of cited proofs), D1-D5 (the comparison argument stays in the item; the new node is a general interval lemma), and E1-E7 (all lifting hypotheses, mapping objects and preservation conditions). The item allows empty U: then both subcategories and both localizations are empty and the proof has no object choices. The proof does not require finite products to belong to U. Every proof step has fewer than 2000 characters; the independent interval argument is a new node rather than hidden in a long step.

## Unfinished work

No part of this one-level split remains unfinished. The new interval lemma is intentionally unsplit and enters the stage-1 queue. No Mathlib leaves are claimed.
