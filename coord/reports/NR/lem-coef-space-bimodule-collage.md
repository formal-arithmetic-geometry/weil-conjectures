# Worker report: lem-coef-space-bimodule-collage

## Files written

- dag/nodes/sec-six-functors/lem-coef-space-bimodule-collage.json: repaired item with five strict simplicial-category proof steps.
- dag/nodes/sec-six-functors/lem-coef-strict-bimodule-rectification.json: new statement-only auxiliary node; Mathlib searches found no matching theorem.
- citations.json: 14 exact verbatim statement quotes, one for every cited node in every proof step.

## Attachments

None. I searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item id, collage/bimodule terminology, and the blueprint tag; no sorry-free declaration states this item.

## WANTED

- WANTED: archival copy of Lurie, Higher Topos Theory, §2.3.1, Definition 2.3.1.3 and Remark 2.3.1.4, for the correspondence/collage construction.
- WANTED: archival copy of HTT §§2.2.1, 2.2.5 and Appendix A.3.3 for the strictification/model comparison used by the new auxiliary node.

## What was wrong and what changed

The returned proof tried to strictify a two-variable coherent functor by applying one-variable straightening and enriched-presheaf rectification. Those cited nodes do not provide a strict bimodule with simultaneous A-op and B actions. Its string construction then asserted strict simplicial identities from homotopy-coherent Segal data; on mixed higher simplices this is invalid. It also invoked the Reedy homotopy-Segal comparison without establishing its vertical Reedy-fibrancy hypothesis, and its naturality sentence repeated the same strictness gap. The retained text also contained tab characters in place of \\to and lost backslashes and dollar delimiters.

I added lem-coef-strict-bimodule-rectification, which states the missing two-variable strict Kan-valued enriched presentation and its action-preserving coherent equivalence. The item proof now follows the existing lem-coef-triangular-cofibrant-resolution route: choose Bergner cofibrant locally Kan endpoint models; rectify H to a strict Kan-valued bimodule; form the directed strict collage; apply the triangular cofibrant-resolution lemma; take the coherent nerve; and use the natural complete-Segal comparison. Every TeX arrow, backslash, and delimiter was rewritten in valid JSON.

## Not duplicates

- lem-coef-strict-bimodule-rectification vs lem-coef-enriched-presheaf-rectification: the new node is simultaneous two-variable A-op-times-B rectification with both actions; the existing node is one-variable presheaves and representable evaluation.
- lem-coef-strict-bimodule-rectification vs lem-coef-triangular-cofibrant-resolution: the new node rectifies a coherent space-valued bifunctor to a strict Kan-valued bimodule; the existing node glues an already given strict bimodule into a cofibrant triangular simplicial category.

## Review by NR

I reread the item, its chapter and unit records, the returned review, and the full statements of lem-coef-coherent-nerve-comparison, lem-coef-simplicial-model-coherent-diagrams, lem-coef-simplicial-projective-model-calculus, lem-coef-triangular-cofibrant-resolution, lem-coef-complete-segal-quasicategory-comparison, def-cbc-enhanced-diagrams-cones, and def-coef-infinity-category-of-spaces. I also read the complete source place in HTT §2.3.1; the archival copy is unavailable, so the construction-specific refinements remain marked WANTED and are written as agent proof text.

Step 1 uses the coherent-nerve node for the Bergner model structure and locally Kan replacements, the two-variable rectification node for the strict functor M and its Kan values, and the universe/space conventions of the two definition nodes. The new node says exactly that the two actions transport to precomposition and postcomposition, including units and all higher simplices; this closes C3/C4 and the former one-variable misuse.

Step 2 uses only the new node. Its strict enriched functor gives literal commuting action maps, so the endpoint and mixed composition maps satisfy associativity and units as equalities of enriched structure; no Segal-space face is treated as a strict composite. The empty reverse homs and Kan mixed values are checked directly from the constructed category.

Step 3 uses the full triangular-resolution statement: its hypotheses are a directed target category D, endpoint local trivial fibrations with cofibrant sources, and empty reverse homs. These are supplied by Step 2 and the chosen Bergner endpoint replacements. The conclusion supplies the projectively cofibrant mixed bimodule N, objectwise trivial Kan fibration N to M, empty reverse homs, and functoriality. Since M(a,b) is Kan, N(a,b) is Kan by the fibration property; this repairs the former missing fibrancy check without invoking lem-coef-reedy-homotopy-segal-comparison.

Step 4 uses the coherent-nerve statement that a locally Kan simplicial category has a quasicategorical coherent nerve and that its enriched mapping sets are naturally equivalent to infinity-categorical mapping spaces. The endpoint models are identified with C and D through the chosen equivalences, and the triangular map plus the rectification equivalence gives N(a,b) equivalent to H(a,b). Empty reverse homs give the reverse mapping-space assertion.

Step 5 reads the enriched-functor definition of the coherent nerve from the coherent-nerve statement: labels are nondecreasing because a B-to-A mapping simplex is empty, and a mixed string has a unique crossing. The strict action and composition equations give every face and degeneracy. I then use the complete-Segal comparison for the natural equivalence R from infinity categories to complete Segal spaces and its mapping-fiber preservation. This replaces the invalid claim that homotopy-coherent Segal data themselves have strict face maps.

I tested edge cases on the repaired construction: an empty C or D deletes the corresponding endpoint and all incident mixed objects; an empty H(a,b) gives an empty mixed hom; terminal one-object endpoints with H the point give the walking arrow; and with both endpoint blocks empty the collage is empty. I checked every uses entry against the cited node statement and regenerated citations.json; all 14 quotes are exact substrings. The new node has all required search kinds, two alternative phrasings, no Mathlib match, and a blueprint ancestor/place. No SGA source is used.
