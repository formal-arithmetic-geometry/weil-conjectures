Files written:
- `dag/nodes/sec-picard-framework/lem-pc-direct-image-bounded-coherent.json`: statement item, split proof, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-coherent-support-proper-higher-direct-image.json`: statement-only child, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-direct-image-qc-support-reduction.json`: statement-only child, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-derived-direct-image-hypercohomology-ss.json`: statement-only child, no Mathlib match.
- `citations.json`: verbatim statement quotations for every proof dependency.

Attachments:
- None. I searched `WeilConjectures/` for the item id, its Stacks label, and direct-image/coherent terminology; no exact sorry-free declaration states this item.

WANTED:
- None; the Stacks source files needed for Tags 08E2 and 08DS were available in `/home/ubuntu/c1-stacks-review`.

## Review by C1

I read the item's source, Stacks `perfect.tex` Lemma 36.11.3 (Tag 08E2, `lemma-direct-image-coherent`), including its spectral-sequence argument and its boundedness paragraph. I also read the direct source for the proper-support sheaf input, `coherent.tex` Lemma 30.11.3 (Tag 08DS, `coherent-lemma-support-proper-over-base-pushforward`), and `derived.tex` Lemma 13.20.4 (Tag 015J, `derived-lemma-two-ss-complex-functor`). The three new statements are smaller than the item: the first concerns a single coherent sheaf, the second only performs the quasi-compact support reduction, and the third only supplies the hypercohomology spectral sequence.

Step 1 cites the spectral-sequence child, whose statement explicitly gives the E2 page, abutment, convergence, and finite filtrations. Step 2 cites the proper-support higher-direct-image child, and its hypotheses match the coherent cohomology sheaf and proper-support hypotheses one q at a time. Step 3 uses exactly those two statements; the remaining finite-filtration extension argument is written as an elementary local Noetherian-module argument. Step 4 uses only the spectral-sequence child's bounded-below/convergence content. Step 5 cites the quasi-compact reduction child for the restriction isomorphism and then the existing uniform truncation bound; after reduction, its quasi-compact/quasi-separated and quasi-compact-base hypotheses are explicit.

I checked the statement dependencies against the definitions named in the node, searched the whole DAG and blueprint before creating each child, and ran all required LeanFinder, Loogle, grep, and LeanSearch searches. LeanSearch was unavailable for all four searches and is recorded as unavailable; the other searches found no scheme-level theorem. Small checks included the identity morphism (the claim reduces to bounded coherent E), a coherent sheaf in one degree (the 08DS child gives the usual higher-direct-image result), and the zero complex (all conclusions are immediate). No source statement was changed or weakened.

What was wrong in the imported item was only that its proof was empty: the imported statement itself agrees with Tag 08E2. The existing dependent perfectness node already cites this item, so no unrelated node was edited.

## Not duplicates

lem-pc-derived-direct-image-hypercohomology-ss vs lem-weil-pbc-hypercohomology-e1-pullback-functorial: the existing node states functoriality of pullback maps between etale hypercohomology spectral sequences, while the new node states the direct-image E2 page, abutment, convergence, and finite filtrations.
lem-pc-direct-image-qc-support-reduction vs lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect: the existing node states perfectness of Rf_*E under finite Tor dimension, while the new node states the quasi-compact-open restriction and its direct-image isomorphism.
lem-pc-direct-image-qc-support-reduction vs lem-pc-proper-direct-image-finite-tor: the existing node states finite Tor dimension of Rf_*E, while the new node states the quasi-compact-open restriction and its direct-image isomorphism.

## Second reading by C1

- Item statement: checked against Stacks Tag 08E2, label `perfect-lemma-direct-image-coherent`, hypothesis by hypothesis; verdict agrees, including Noetherian base, locally finite type morphism, bounded coherent complex, and proper supports.
- Step 1: checked against the statement of `lem-pc-derived-direct-image-hypercohomology-ss` and Tag 015J; verdict uses exactly its spectral sequence, convergence, and finite-filtration clauses.
- Step 2: checked against the statement of `lem-pc-coherent-support-proper-higher-direct-image` and Tag 08DS; verdict hypotheses match each cohomology sheaf and its proper support.
- Step 3: checked the finite-row filtration and closure of coherent modules on the Noetherian base; verdict is an elementary finite-subquotient and extension argument from Steps 1–2.
- Step 4: checked the lower-bound conclusion against the bounded-below spectral-sequence range in the cited child; verdict follows from nonnegative direct-image degree and the lower bound on E.
- Step 5: checked the restriction isomorphism against the support-reduction statement (the union is finite because E is bounded) and the uniform truncation statement; verdict gives the required quasi-compact, quasi-separated replacement and upper bound.
- `lem-pc-coherent-support-proper-higher-direct-image`: checked statement-only form, self-contained definitions, Tag 08DS label, and zero/field/identity cases; verdict is a strict input lemma and not a duplicate.
- `lem-pc-direct-image-qc-support-reduction`: checked statement-only form and the support-reduction paragraph in Tag 08EV, label `perfect-lemma-perfect-direct-image`, including the restriction isomorphism; verdict is the needed smaller geometric input and not a duplicate.
- `lem-pc-derived-direct-image-hypercohomology-ss`: checked statement-only form against Tag 015J specialized to derived direct image, and bounded-below/one-degree/zero-complex cases; verdict is the needed spectral-sequence input and not a duplicate.

Changes made: corrected the item source label to `perfect-lemma-direct-image-coherent`, corrected the 08EV child source label to `perfect-lemma-perfect-direct-image`, and corrected the item node's `created.item` to this item so delivery ownership is accurate. No mathematical statement or proof step was otherwise changed.
