1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-tor-amplitude-qcoh-test.json` — statement, split proof, no Mathlib match.
- No new child nodes.

2. Attachments: none.

3. WANTED: the local Stacks Project source `perfect.tex`, Lemma 36.10.6 (Tag 08EA), for the affine Tor-amplitude criterion used in step 2.

4. The imported node had no proof and only a single Mathlib grep. I preserved its statement and corrected the record by adding the three proof steps, all four required Mathlib search records, `status: split`, and the split report. The central affine criterion is a specialization of this item's own assertion, so I did not create a duplicate child node. I checked that the item has no matching project declaration in `WeilConjectures/` and that no existing DAG node states Tag 08EA's quasi-coherent testing criterion.

## Review by K1

I read the item and its parent use in `lem-pc-proper-direct-image-finite-tor.json`, including the sentence that applies the quasi-coherent testing lemma. I checked the statement's hypotheses against the cited Tag 08EA label: quasi-separated scheme, object of the quasi-coherent derived category, integer interval, and vanishing first for quasi-coherent modules, then for arbitrary modules. Step 1 records the affine-local reduction and the role of quasi-separatedness. Step 2 records the substantive affine criterion and explicitly notes that the source packet is unavailable, so this is an agent-written rendering of the cited Stacks implication rather than an attachment. Step 3 checks compatibility on overlaps and the local-to-global vanishing conclusion. I searched Lean source for the blueprint tag and relevant Tor-amplitude declarations; no declaration states this item. I also ran LeanFinder, Loogle, grep, and LeanSearch searches and recorded their exact outcomes, including LeanSearch being unavailable. Small cases checked mentally include `E = 0`, `a = b`, and an affine point, where the assertion reduces directly to the corresponding module statement.

5. Nothing else was left unfinished beyond the unavailable local Stacks source noted above.

## Second reading by K1

- Item statement: checked against Stacks Tag 08EA online, hypothesis by hypothesis; verdict correct (the source gives the equivalent two conditions, and the item states (2) implies (1)).
- Step 1: checked against Tag 08EA's affine-open reduction and the existing `pqf-lem-pushforward-qcoh` statement; verdict repaired, because quasi-coherent extension by affine pushforward was previously uncited.
- Step 2: checked against Tag 08EA together with Lemma 36.3.5 (Tag 06Z0) and the affine criterion Lemma 36.10.4 (Tag 08E9); verdict repaired, because the criterion was substantive and was incorrectly marked elementary.
- Step 3: checked against Tag 08EA's local conclusion and restriction of derived tensor; verdict correct and elementary.
- New node `lem-pc-affine-tor-amplitude-criterion`: checked against Tag 08E9, self-contained definitions and TeX; verdict correct, statement-only, no Mathlib match after three searches.
- Existing definition dependencies: checked that `def-pc-scheme`, `def-weil-quasi-separated-morphism`, `def-pc-derived-category`, `lem-pc-affine-qcoh-derived-equivalence`, and `pqf-lem-pushforward-qcoh` state the notions used; verdict consistent.

Changes made: added the missing affine criterion child node; rewrote steps 1 and 2 with the actual Stacks proof route and citations; changed step 2 to non-elementary; filled `citations.json` with verbatim node statements; retained the imported maintainer metadata unchanged. Small cases checked: zero complex, affine point, empty scheme, and intervals with a=b or a=0.
