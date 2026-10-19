# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proper-birational-normal-curve-iso.json` — item, split; two proof steps and two new-node dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-proper-birational-curve-finite.json` — statement-only unsplit node; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-birational-normal-iso.json` — statement-only unsplit node; Mathlib searches found no match.
- `citations.json` — verbatim statement quotations for both proof-step citations.

## Attachments

None. No declaration in `WeilConjectures/` states this item or either new node with a sorry-free proof.

## WANTED

None.

## Not duplicates

- `lem-trf-proper-birational-curve-finite` vs `pqf-lem-proper-lqf-finite`: the existing node is the general proper locally quasi-finite implies finite theorem (and is a Mathlib leaf); the new node is the curve-specific finiteness consequence of Tag 0AB7 from properness, one-dimensional target, and a generic function-field isomorphism.
- `lem-trf-proper-birational-curve-finite` vs `lem-sc-normalization-properties`: the existing normalization node concerns the canonical normalization morphism of one scheme, while this node concerns an arbitrary proper birational morphism between two integral curves and does not assume the source is a normalization.
- `lem-trf-finite-birational-normal-iso` vs `lem-sc-normalization-properties`: the existing node only states that a normalization is an isomorphism over a normal open; this node states Tag 0AB1 for every finite birational morphism between integral schemes with normal target.

## What was checked and changed

The imported item statement was retained. I added `def-sc-function-field` to `stmt_deps`, because the displayed isomorphism of function fields is part of the statement and that definition was missing from the imported dependency list. The source route is the two equivalent Stacks routes already named by the item: Tag 0AB7 in `literature/stacks-project/varieties.tex` supplies finiteness over every codimension-one point of a one-dimensional target, and Tag 0AB1 in `literature/stacks-project/morphisms.tex` identifies a finite birational morphism with an isomorphism over a normal integral target. I also checked Tag 0BFP's codimension-one formulation; it gives the same normal-curve conclusion, but the split uses the shorter 0AB7/0AB1 route.

The first new node is statement-only and self-contained: it introduces the field, both integral separated finite-type curves, their dimension-one hypotheses, the proper dominant map, the function-field isomorphism, and the finite conclusion. The second is statement-only and self-contained: it introduces integral schemes, a finite map, the induced function-field isomorphism, local normal-domain hypotheses on the target, and the isomorphism conclusion. I searched the whole DAG by the Stacks tags and key phrases before creating either node. The recorded LeanFinder, LeanSearch, Loogle, and Mathlib-source grep searches are in each node's `mathlib_searches`; the Loogle query for the second node returned an unknown identifier and is recorded as unavailable rather than as a false negative.

## Review by Q17

I read the item source sentence and the two Stacks source lemmas at their actual labels. For item step 1, the cited `lem-trf-proper-birational-curve-finite` statement says exactly that the given proper dominant map of integral one-dimensional finite-type curves, with the displayed function-field isomorphism, is finite; the step checks each of those hypotheses against the item and uses only the target-local finiteness conclusion of Tag 0AB7. For item step 2, the cited `lem-trf-finite-birational-normal-iso` statement says exactly that a finite map of integral schemes inducing the function-field isomorphism is an isomorphism when every target local ring is a normal domain; the step checks finiteness from step 1 and normality from the item's local-ring hypothesis. No step uses normality of the source or perfection of the field.

I opened every cited node and verified that the quoted formulas in `citations.json` are verbatim. Both new nodes have complete statements with all objects introduced, correct Stacks labels and places, no proof sketch because they are unsplit statement nodes, and no Mathlib match. I tested the edge cases conceptually: the identity map of a normal affine line satisfies both nodes; a normalization of a singular integral curve is excluded from the second node exactly when the target is non-normal; and no perfectness assumption enters either Tag 0AB7 or Tag 0AB1. The split has no cycle and does not duplicate the existing proper-quasi-finite Mathlib leaf or the normalization-specific curve nodes.
- `lem-trf-finite-birational-normal-iso` vs `lem-trf-proper-birational-normal-curve-iso`: the new node concludes isomorphism from finiteness and normality for arbitrary integral schemes, while the item first assumes properness and dimension-one curves and derives finiteness.
- `lem-trf-finite-birational-normal-iso` vs `lem-sbc-normal-dense-open-integral-section`: the existing node extends integral sections from a dense open; it does not assert an isomorphism for a finite birational morphism.
- `lem-trf-finite-birational-normal-iso` vs `lem-sbc-normalization-dense-open`: the existing node concerns a canonical relative normalization in a dense open; the new node concerns an arbitrary finite birational morphism and gives the affine normal-ring argument of Tag 0AB1.
- `lem-trf-proper-birational-curve-finite` vs `lem-trf-proper-birational-normal-curve-iso`: the new node proves only finiteness and has no normality hypothesis or isomorphism conclusion; the item adds normality and concludes isomorphism.
