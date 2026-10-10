1. Files written:
   - `dag/nodes/sec-picard-framework/lem-pc-finite-flat-proper-support-descent.json`: split item, two proof steps.
   - `dag/nodes/sec-picard-framework/lem-pc-flat-bounded-complex-descent.json`: statement-only node; Mathlib no-match.
   - `dag/nodes/sec-picard-framework/lem-pc-proper-support-descent.json`: statement-only node; Mathlib no-match.
   - `citations.json`: exact statement quotations for both proof steps.
2. Attachments: none. No project declaration tagged `lem-pc-finite-flat-proper-support-descent` exists in the Lean source, and the item is not stated by another DAG node.
3. WANTED: none.
4. The imported item had no proof. I checked the neighboring `lem-pc-noetherian-approximation-data` node, which uses this item exactly for the bounded flat complex and proper supports, and checked the existing `lem-pc-perfect-complex-descent` node to avoid duplicating perfect-object descent. The two new statements are strictly narrower than the item: one omits proper-support conclusions and the other concerns a single already chosen finitely presented module model. For step 1, the cited statement explicitly supplies boundedness, finite presentation, flatness, and the base-change isomorphism. For step 2, the cited statement explicitly supplies eventual proper support for each chosen model; finitely many terms permit a common later stage by directedness while retaining the differentials. I searched the whole DAG for Tags 01ZR, 05LY, 081G and the support/flatness keywords; no duplicate statement was found. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch for each new node; LeanSearch was unavailable and recorded as such.
5. What I could not finish: no Lean proof is written at stage 1; both new nodes are intentionally unsplit statement inputs.

## Review by J1
I read the item source metadata and the parent approximation node, then checked the relevant Stacks tags named there. I verified that step 1 cites a node whose statement contains exactly the bounded finitely presented flat complex and its base-change identification. I corrected step 2 after noticing that a fresh descent of each term could discard the chosen complex differentials. Its cited node now states eventual properness for each existing finitely presented model, so a common-stage base change keeps the complex intact. I checked every cited node's statement rather than relying on its proof text, searched for duplicates by tag and keywords, and recorded all Mathlib searches. The item and both new nodes carry the required blueprint references.

## Not duplicates
lem-pc-flat-bounded-complex-descent vs lem-pc-finite-flat-proper-support-descent: the new node omits all proper-support hypotheses and conclusions and isolates only bounded finitely presented flat-complex descent.
lem-pc-flat-bounded-complex-descent vs lem-pc-noetherian-approximation-data: the new node has no perfect object, no proper-support conclusion, and no simultaneous-stage assertion; it is the flat-complex component only.
lem-pc-proper-support-descent vs lem-pc-finite-flat-proper-support-descent: the new node concerns eventual properness for one already chosen finitely presented module model, not descent of a bounded complex with termwise flatness.
lem-pc-proper-support-descent vs lem-pc-noetherian-approximation-data: the new node concerns eventual properness for one fixed module model and omits the complex, flatness, perfect object, and simultaneous-stage data.

## Second reading by J1

- Item statement: checked against Limits Lemmas 32.10.2 (Tag 01ZR), 32.10.4 (Tag 05LY), 32.13.5 (Tag 081G), and Cohomology of Schemes Lemma 30.26.7; the directed inverse system, affine transitions, limit, stage change, bounded complex, flatness, and termwise proper supports are all stated explicitly. Verdict: repaired and accepted.
- Step 1: checked against the exact statement of `lem-pc-flat-bounded-complex-descent`; it supplies the bounded finitely presented complex, stagewise flatness, and the base-change isomorphism under the stated inverse-system hypotheses. Verdict: accepted.
- Step 2: checked against the exact statement of `lem-pc-proper-support-descent`; it applies termwise and uses finiteness of the bounded complex to choose a common later stage while preserving differentials by base change. Verdict: accepted.
- `lem-pc-flat-bounded-complex-descent`: checked against Tags 01ZR and 05LY; its statement is self-contained and statement-only, with all notions linked to definition nodes. Tested on the zero complex and one-term complexes over a field. Verdict: repaired to make the inverse system and base changes explicit.
- `lem-pc-proper-support-descent`: checked against Tag 081G and Cohomology Lemma 30.26.7; its statement is self-contained and statement-only, with scheme-theoretic support and base change explicit. Tested on the zero module, a finite module over a field, and the empty support. Verdict: repaired to make the inverse system and stagewise support explicit.
- Item edge cases: the zero complex, a one-term complex, a field stage, and empty support satisfy the formulation without hidden hypotheses. Verdict: accepted.
- Mathlib searches: reran LeanFinder with a general filtered-colimit support query and Loogle with `IsProper support filtered colimit`; no exact declaration was found (the recorded service-unavailable LeanSearch result remains unavailable). Verdict: statement nodes remain unsplit.
- Changes: corrected the item ownership in `created.item`; added the `def-pc-base-change` dependency; rewrote the item and both new statements to quantify the directed inverse system and define every later-stage base change. These changes repair B2/B3 self-containment and E1 ambiguity about “increasing i”.
