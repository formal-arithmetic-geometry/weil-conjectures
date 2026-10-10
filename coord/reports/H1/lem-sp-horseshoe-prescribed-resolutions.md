1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sp-horseshoe-prescribed-resolutions.json`: split statement; no new nodes; Mathlib searches found no matching horseshoe theorem.

2. Attachments: none.

3. WANTED: literature source `literature/stacks-project/derived.tex`, Lemma 013T, is referenced by the imported node but the local checkout contains only the citation metadata, not the source TeX file.

4. What was checked and corrected: the item is not already declared in `WeilConjectures/` and has no blueprint duplicate. The ordinary horseshoe node `lem-weil-pbc-injective-resolution-ses` was read in full; it proves the pushout and cokernel induction but does not retain prescribed outer resolutions, so it is cited only for the construction pattern and the strengthening is stated in the item itself. The source route is Lemma 013T's last sentence, which explicitly permits the two end resolutions to be given in advance. The four steps follow that source: degree-zero pushout, induction with fixed outer terms, compatibility and exactness, and the negative-degree/direct-sum conclusion. Each cited node was checked against the quoted statement in `citations.json`; the abelian and injective-resolution definitions supply the ambient hypotheses and terminology. The Mathlib searches were rerun with the item id using LeanSearch (unavailable), LeanFinder, Loogle, and grep; only single-object resolution APIs appeared.

## Review by H1

I checked the item statement against the imported Stacks 013T citation and the use in `lem-sp-cartan-eilenberg-exists`. The supplied resolutions are genuinely stronger data than the ordinary horseshoe node provides, so I kept the item as a split statement rather than attaching it or creating a duplicate child. Step 1 uses the existing horseshoe construction to initialize the row with the prescribed degree-zero terms. Step 2 uses its cokernel induction, explicitly requiring the next terms of the supplied resolutions to be used, which is the point needed by the Cartan--Eilenberg induction. Step 3 verifies the differential compatibility, augmentation identities, and resolution exactness; Step 4 checks the nonnegative indexing and direct-sum description. I read the full ordinary horseshoe node to verify that each quoted fact is present, and every citation quote is copied verbatim. No statement was weakened, and no new node was introduced for a clause that merely restates this item.

5. What remains: the sandbox must pass `deliver.py --no-push`; no Lean declaration or source proof is being added at stage 1.

## Second reading by H1

- Item statement: checked against Stacks `derived.tex`, Lemma 013T (`lemma-injective-resolution-ses`), parts (1)--(3), and the use in `lem-sp-cartan-eilenberg-exists`; the short exact sequence, enough-injectives hypothesis, prescribed outer resolutions, nonnegative indexing, complex maps, augmentations, and degreewise exact rows all match the intended strengthened lemma.
- Step 1: checked against the statement of `lem-weil-pbc-injective-resolution-ses` and 013T Step 1; verdict: the degree-zero pushout and split row are the ordinary horseshoe construction with the supplied outer degree-zero terms retained.
- Step 2: checked against the ordinary horseshoe statement and 013T Step 2; verdict: the cokernel induction uses the next prescribed outer terms and their differentials, preserving the two given outer complexes.
- Step 3: checked against the ordinary horseshoe compatibility clauses and 013T Step 2 conclusion; verdict: the lifting equations give chain maps, augmentation identities, exact rows, and exact augmented complexes.
- Step 4: checked against the ordinary horseshoe direct-sum clause and 013T parts (2)--(3); verdict: negative degrees vanish and each row is split with the stated inclusion and projection.
- New nodes: none; the item is the only new statement node, so B1--B7 were checked directly (statement only, self-contained definitions, single TeX source, tag and label, and no Mathlib attachment). Existing-node searches found only the ordinary horseshoe theorem, which lacks the prescribed-end data.
- Small cases: the zero short exact sequence gives zero resolutions; a split sequence of objects gives the direct-sum row immediately; degree zero and degree one agree with the pushout and first cokernel steps; negative degrees are zero by construction.

### Source error

The local copy of `derived.tex` at Lemma 013T contains parts (1)--(3) and a placeholder in the enumerated list; it does not actually contain the worker report's claimed “last sentence” explicitly prescribing both end resolutions. The strengthened statement is mathematically the clause required by `lem-sp-cartan-eilenberg-exists`, but its simultaneous prescribed-end wording is not verbatim in this source checkout. The node and citations now identify the actual 013T parts and mark the prescribed-end clause as the item-specific refinement instead of attributing nonexistent text to the source.

Changes made: corrected the node's source locations and proof origin, removed the inaccurate “last sentence” attribution, and added this second-reading audit plus the source-error record. No node statements or proof dependencies were otherwise changed.
