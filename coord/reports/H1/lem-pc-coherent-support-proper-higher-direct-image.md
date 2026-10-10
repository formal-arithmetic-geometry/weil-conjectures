Files written:

- `dag/nodes/sec-picard-framework/lem-pc-coherent-support-proper-higher-direct-image.json`: item split into three proof steps; no new nodes; Mathlib searches recorded (no match, with LeanSearch unavailable).
- `citations.json`: verbatim statement quotes for all cited nodes and steps.

Attachments:

- None.

WANTED:

- None.

What was wrong or incomplete in the imported item:

- The item had no proof and no proof dependencies. I supplied the support factorization, derived composition, and proper-coherence argument while retaining the Tag 08DS statement and hypotheses.
- No duplicate child was created: `lem-weil-pbc-module-support-proper-over-base` already states the scheme-theoretic support factorization needed by the proof.

What could not be finished:

- Nothing.

## Review by H1

I read the item source in `literature/stacks-project/coherent.tex`, Lemma 30.11.3 (Tag 08DS), and checked its proof route against the existing DAG statements. Step 1 cites `lem-weil-pbc-module-support-proper-over-base`; that statement explicitly gives a closed subscheme carrying the sheaf, properness over the base, and a finite-type quasi-coherent module whose pushforward is the original sheaf. Step 2 cites `lem-pc-derived-direct-image-composition`, whose statement gives the canonical derived composition isomorphism; exactness of pushforward along a closed immersion is the sectionwise elementary observation used to identify the derived pushforward with ordinary pushforward. Step 3 cites `lem-pc-coherent-hi`, whose properness, locally Noetherian base, and coherent-sheaf hypotheses match the factorization from Step 1, and transfers coherence through the Step 2 isomorphism. I opened each cited node and copied the exact sentences used into `citations.json`. I verified the support, properness, finite-type, and coherence hypotheses, and checked the zero sheaf, identity closed immersion, and proper scheme over a field as small cases. The only correction to the imported metadata was replacing the stale zero-hit grep result with the actual search output, which found only an unrelated support heading and no algebraic-geometry theorem.

## Second reading by H1

- Item statement: checked against `coherent.tex`, Lemma 30.11.3, Tag 08DS / label `lemma-support-proper-over-base-pushforward`; hypotheses and conclusion agree exactly, including locally Noetherian S, locally finite type f, coherent F, support proper over S, and every p >= 0.
- Step 1: checked against Tag 08DS and the statement of `lem-weil-pbc-module-support-proper-over-base`; the factorization supplies the proper composite g and F = i_*G, with the properness wording corrected.
- Step 2: checked against Tag 08DS, `lem-pc-derived-direct-image-composition`, and the closed-immersion sectionwise exactness observation; the cited statements support the derived composition and identification of higher direct images.
- Step 3: checked against Tag 08DS and `lem-pc-coherent-hi`; Z is locally Noetherian as a closed subscheme of the locally finite type X over locally Noetherian S, so finite type quasi-coherent G is coherent and the proper-coherence hypotheses match.
- Existing-node audit: searched the DAG for the support factorization, derived direct-image composition, and proper higher-direct-image coherence; all three existing nodes were reused and no duplicate child was needed.
- New-node audit: there are no new child nodes; B1-B7 therefore introduce no additional statement or source obligations.
- Edge cases checked: F = 0, an identity closed immersion, S = Spec(k), and p = 0 all reduce to the stated factorization and proper-coherence result.
- Changes: corrected `created.item` to this item (delivery preflight requirement), corrected Step 1's properness sentence, and recorded this review. Mathlib searches remain recorded verbatim; LeanSearch is marked unavailable.
