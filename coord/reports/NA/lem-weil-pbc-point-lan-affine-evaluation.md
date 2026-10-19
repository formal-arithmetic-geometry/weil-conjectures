# Stage 1 report: lem-weil-pbc-point-lan-affine-evaluation

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-proetale-affine-components-maps.json`: statement-only unsplit node; Mathlib searches found no exact scheme pro-etale correspondence.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-point-lan-affine-evaluation.json`: split item; no Mathlib match for the whole assertion.
- `citations.json`: verbatim citations for every step citation.

## Attachments

None. No sorry-free declaration in `WeilConjectures/` states this item.

## WANTED

None.

## Not duplicates

- `lem-weil-pbc-proetale-affine-components-maps` vs `lem-weil-pbc-proetale-point-components-maps`: the new node applies to every affine pro-etale object; the existing node assumes weak contractibility, while both state the component quotient and maps to `X[S]`.

## What I checked and corrected

I read the imported item, the `sk-thm-properbasechange` unit, the `sec-proper-base-change` chapter, Bhatt–Scholze Lemma 4.2.13(1), and the archived master `RefactorInstruction.tex` proof of `lem:point-eval`. I searched `WeilConjectures/` and found no declaration tagged for this item and no finished declaration with the same statement. The existing `lem-weil-pbc-proetale-point-components-maps` is insufficient because its weak-contractibility hypothesis is absent from this item; I therefore created the generalized component-map node and recorded the relationship in `Not duplicates`.

Step 1 uses the new node, whose statement explicitly supplies profiniteness and the Hom-to-`X[S]` correspondence under the exact affine hypothesis. Step 2 uses only that correspondence. I corrected my initial finite-quotient-colimit phrasing: condensed sheaves do not in general commute with those colimits. The actual Kan index uses all profinite sets; its terminal object is `(pi_0(V), q)`, and the explicit unique-arrow and cocone calculation proves evaluation in each coefficient category. No sheafification theorem or geometric inverse-image identification is needed here. Step 3 is marked elementary and spells out the finite coproduct component decomposition, the sheaf product axiom, the empty-family case, and pointwise operations. I verified that all cited node quotes are verbatim and that `proof_deps` is the union of the step citations. I tested the empty-family and disconnected-affine edge cases in the natural-language argument and kept the exact coefficient categories and hypotheses of the item.

## Review by NA

I checked the source and every cited statement directly. The source's proof first identifies maps to finite disjoint unions with continuous maps from connected components, then computes the left-Kan colimit using its terminal object, ; my final step derives finite-coproduct product evaluation explicitly from the sheaf axiom. The imported DAG had already split a weakly-contractible specialization; I corrected the route by adding the strictly broader affine component-map statement rather than citing that narrower node under missing hypotheses. I also recorded all required Mathlib searches (LeanFinder, Loogle, grep, and unavailable LeanSearch) for both the item and the new node, and preserved the blueprint ancestry from `thm-weil-pbc-qbar`.

## What could not be finished

The new generalized component-map node remains unsplit because it is not a one-line Mathlib result; it is intentionally statement-only for the next stage-1 worker.

## Dry run

`deliver.py NA lem-weil-pbc-point-lan-affine-evaluation --no-push` printed `OK (not pushed)` with preflight passed. No delivery was pushed. The wrapper logs searches under its item argument: searches for children must be run with this delivered item argument to be visible to its search check. I reran the needed queries that way instead of editing the log.

## Second reading by NA

- Item statement: checked against RefactorInstruction.tex `lem:point-eval` and Bhatt–Scholze Lemma 4.2.13(1); the source assumes a weakly contractible affine basis object, so I repaired the imported all-affines statement to that hypothesis and its finite-family consequence.
- New node `lem-weil-pbc-proetale-affine-components-maps`: checked against Bhatt–Scholze Lemma 4.2.13(1) and the preceding connected-component discussion; its profiniteness and Hom correspondence are self-contained, statement-only, and the recorded searches found no Mathlib declaration.
- Step 1: checked that the cited component-map node supplies exactly profiniteness and the correspondence for the weakly contractible affine object; verdict pass after the hypothesis repair.
- Step 2: checked the index-category orientation, terminal object, and cocone universal property directly from the correspondence; the argument is elementary and handles all three coefficient categories.
- Step 3: checked finite coproducts, the empty family, restrictions, naturality, and operations against the sheaf axiom and the source paragraph; verdict pass.

### Source correction

STATEMENT-DISPUTED: The imported statement was too strong: the cited source proves evaluation on weakly contractible affine basis objects, not arbitrary affine objects. The statement and all proof steps now use that source hypothesis; this is marked `STATEMENT-DISPUTED` in the reading record rather than silently weakening the target.

### Changes made

- Restricted the item from arbitrary affines to weakly contractible affine objects, matching `lem:point-eval`.
- Updated steps 1–3 and the finite-family clause to use the repaired hypothesis.
- Corrected `created.item` metadata on both node files to the delivered item.
