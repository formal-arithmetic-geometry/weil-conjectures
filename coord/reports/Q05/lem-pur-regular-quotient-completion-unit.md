# Q05 stage-1 delivery: lem-pur-regular-quotient-completion-unit

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-regular-quotient-completion-unit.json`: statement; split into five proof steps; not a Mathlib leaf. Existing statement and provenance retained; no new nodes.
- `citations.json`: ten step/node entries, each quoting the actual statement of its cited node verbatim.
- `report.md`: this report. `searches.jsonl` is the unmodified output log maintained by msearch.py. The sandbox also contains a source-text extract and the script used to write the split; neither is a proposed repository file.

## Attachments

None. The exact blueprint-tag search in `lean/WeilConjectures/` had no hit. Searches for completion, Koszul and Roos notions found infrastructure and specialized adic results, not the whole general small-ringed-site assertion with all three conditions and the specified zero-component map. The existing Koszul reconstruction declaration covers a dependency, not this item's local-completeness criterion, so it is reused as a node rather than offered as an attachment.

## WANTED

None. All source documents needed for this item are present locally.

## What was wrong or missing

The assigned node was statement-only. Its statement needs no correction. In particular, an isomorphism of the first vertices of two Roos triangles would not by itself identify the specified zero-coordinate completion map with that isomorphism. Step 2 establishes the actual unit equation using strict-augmentation normalization. Step 5 avoids assuming uniqueness of such a triangle lift: it first obtains completeness and then invokes the fixed-unit criterion.

The current blueprint has moved the scalar-extension ancestor into `sec-proper-base-change/sk-thm-properbasechange/`. I read its statement and `.proof.md` in the main-20261015 snapshot, including the integral completed-tensor paragraph. The recorded ancestor and via chain are retained; this item supplies the regular principal completion comparison needed below that paragraph. The older DAG chapter/unit placement is not edited. The unit record is a definition with no proof steps; this item is not its key statement, so no unit realization is changed.

## Unfinished work

None in the requested one-level split. Existing dependency nodes retain their own proof and implementation status. No Lean was written, compiled, or built.

## Mathlib searches

I read the inherited search results and retained those records unchanged. I also ran seven fresh searches through the required Q05 msearch.py command. Each fresh record is copied from the actual tool log, with the exact tool/query and actual hit names/counts. These check the more general derived-completion interpretation as well as the explicit Koszul/quotient unit question:

- LeanFinder and LeanSearch: `Derived completion of module sheaves at a nonzerodivisor is the homotopy inverse limit of derived quotient tensors with the canonical unit`.
- Loogle: `"DerivedCategory", "limit"`.
- grep: `derived.?complet|[Kk]oszul.*complet|complet.*[Kk]oszul`.
- LeanFinder, second formulation: `The Koszul tower for a principal ideal computes local derived completeness of a sheaf complex and identifies the quotient augmentation unit`.
- Loogle, second formulation: `"CochainComplex", "mappingCone"`.
- grep, second formulation: `Roos|[Hh]omotopy[Ll]imit|derivedCompletion|[Kk]oszul`.

All services answered. Natural-language hits concern ordinary `AdicCompletion`, local cohomology, sheaf limits, or period rings. Loogle's first query has no hits and its second returns mapping-cone constructors and coordinate lemmas. The first grep has no hits; the second gives only Koszul connections and two TODO comments about Koszul methods. No result states local derived completeness for arbitrary module sheaves or the equivalence for the specified strict quotient unit. There is therefore no Mathlib match for the item.

## Not duplicates

No new nodes are proposed. Whole-DAG searches for 0A0E, the completion/Koszul terms and regular quotients exposed the existing results reused in the split. Whole-blueprint searches for `Koszul completion`, `regular quotient` and `completion unit` produced no node stating all the clauses of this item with these hypotheses. The narrower adic/pro-etale reconstruction statements are not silently generalized. In particular, `prop-weil-pbc-koszul-reconstruction` needs a Noetherian adic coefficient datum, whereas the reused general ringed-site reflector does not.

## Review by Q05

I read Stacks `algebraization.tex`, Tags 0999 (definition-derived-complete), 099B (lemma-derived-completion) and 0A0E (lemma-derived-completion-koszul), including the proof realizing completion as derived internal Hom out of the extended Cech complex and then as the limit of the Koszul tower. These are ringed-site assertions, so they apply to this item without a Noetherian or boundedness assumption. I also read `sites-cohomology.tex`, Tag 0941 (lemma-derived-limit-is-ok), including the K-injective tower proof and the product sequence giving the Roos triangle. Finally I read Bhatt--Scholze Lemma 3.4.12 and its proof, which emphasizes reconstruction via the natural map. I do not use repleteness from the context of that paper as an unmentioned hypothesis of this item's general ringed-site result; the general statements come from Stacks and the existing DAG interfaces.

For Step 1 I opened `lem-pur-derived-complete-koszul-reconstruction` and read its whole statement. It gives a levelwise quasi-isomorphism and an augmentation-compatible isomorphism of derived limits for exactly a regular global section and a K-flat representative. Its hypotheses are satisfied by the given a and P. The elementary power calculation shows that every a^n remains regular; the two transition composites really are identical quotient maps. The K-flat transport is supplied by this cited theorem, not inferred from a definition of ordinary flatness. No termwise flatness or underived tensor-exactness hypothesis is smuggled in.

For Step 2 I read the whole statements of that reconstruction node, `lem-weil-strict-roos-comparison`, and `lem-weil-pbc-ringed-koszul-completion-reflector`. The reflector defines the degree-zero Koszul unit, the reconstruction states compatibility with the strict augmentations, and the strict Roos node explicitly identifies the zero shifted-coordinate map with the derived augmentation. Exact countable products and the site-size hypothesis required by the strict comparison are present in the item. Thus the equation theta eta = kappa is an equation for the specified morphisms. This is stronger than merely matching their projections.

For Step 3 the reflector's statement explicitly asserts both local completeness of the target and invertibility of its actual unit exactly for locally complete inputs. Its condition ranges over all slices and all sections of the generated ideal, with the same sheafified localization as in the item. It therefore supplies precisely the vanishing condition used here. Invariance of that condition under an isomorphism follows directly by applying the two functors to the isomorphism and comparing to zero; no new theorem is being hidden there.

For Step 4 I opened `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, whose statement actually supplies the natural distinguished triangle with products in the derived category, and `def-weil-triangulated-category`, whose TR1 clause makes an isomorphic triangle distinguished. The strict Roos node states preservation of projections as well as augmentation normalization. Replacing the first vertex along h leaves the two products and 1-s fixed, changes the last map to inverse h[1] composed with delta, and yields exactly q_n at each projection. This avoids an unsupported assertion that termwise products automatically compute derived products: the cited strict-limit theorem supplies the derived-product triangle directly.

For Step 5 I again checked the reconstruction node's second paragraph. It assumes the prescribed quotient-component Roos triangle and concludes existence of an isomorphism from its first vertex to the Koszul limit. Those are exactly the available assumptions, not a stronger canonical-unit hypothesis. The general reflector makes that Koszul limit locally complete. Transporting completeness back to P and then using Step 3 proves invertibility of the designated unit. I deliberately make no equality claim between the arbitrarily provided triangle isomorphism and that unit.

No new node needed a separate source or small-case test. I tested the item and each use on P=0, on the zero ring, and on an invertible a: then every quotient and the completion vanish, and the three conditions all reduce to P=0. For a=0 in a nonzero ring, the regularity assumption fails, so that case is not incorrectly used to justify the quotient/Koszul comparison. The ordinary one-point example O=Z, a=p, P=Z gives completion Z_p and a noninvertible unit, so neither completeness of the output nor mere existence of a map to the cone is mistaken for completeness of the input. No positive-rank, nonzero-ring, finite-generation, termwise-flatness or boundedness assumption is used.

I checked delivery-errors B1--B10: there are no invented unsplit nodes, the statement introduces its objects and retains its defining references, TeX is singly escaped after JSON decoding, sources identify the Stacks labels/tags, recorded searches really ran, and no infrastructure hit is mislabeled as a leaf. The item's blueprint provenance is retained and same_as is empty only after the whole-blueprint search. The exact Lean attachment check was done before splitting.

I checked C1--C8 by opening every cited statement, giving the verbatim quotes in citations.json, and checking hypotheses above. Every non-elementary fact is a cited node; no source tag alone serves as a dependency and no proof-only construction is borrowed. A local read of the dependency graph found no path from the four cited theorem nodes back to the item. The two off-unit mathematical tools (regular Koszul reconstruction and the ringed-site reflector) and the generic strict-limit existence theorem are declared in split_report.tool_uses. They implement the integral completion argument below the existing route, without replacing any unit step.

I checked D1--D5: the proof carries the unit equation and both directions of the triangle argument; it creates no clause-restating helper node and does not shift the conclusion into a new unsplit node. No induction is assumed, and no omitted source details are cited as if proved. All five non-elementary steps are shorter than 900 characters; none conceals a separate comparison lemma beyond the existing named dependencies it cites.

I checked E1--E7: the regularity, K-flatness, exact-product and universe hypotheses match their uses; the quotients are the sheaf quotients and the localization is sheafified; the transition and augmentation equations are stated explicitly. The proof distinguishes local internal-Hom completeness from pointwise ordinary module completeness and distinguishes the specified unit from an arbitrary triangle lift. I found no source error or false imported clause to repair. This review is my signature under the five-step split.
