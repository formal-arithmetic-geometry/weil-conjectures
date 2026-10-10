# Stage-1 report: lem-pc-pseudo-coherent-summand

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-pseudo-coherent-summand.json`: split the scheme statement into the affine reduction and local conclusion.
- `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-summand.json`: new statement-only ring lemma (no Mathlib match).
- `citations.json`: verbatim citations for every dependency used by every item step.

## Attachments

None. I found no sorry-free project declaration stating the item.

## WANTED

None.

## What was wrong and what changed

The item was unsplit although its source proof is the affine-module argument of Stacks Tag 08CE. I preserved the item statement and added the missing ring-level lemma from Tag 064X/08CE. I did not create a node for locality or for the zero-summand case, since those are direct uses of the pseudo-coherent definition. Searches found no Mathlib declaration for either the scheme or ring direct-summand result.

## Review by C1

I read the item source in `cohomology.tex`, the ring proof in `more-algebra.tex` (the proof of `lemma-summands-pseudo-coherent`), and the existing node `def-pur-pseudo-coherent-complex`. Step 1 uses exactly the definition's local bounded-above finite-free condition and the new ring lemma's conclusion for both module summands; the restriction of an isomorphism and direct sum to an affine open is the stated affine reduction in Tag 08CE. Step 2 uses only the definition's locality to glue the affine witnesses, and the zero-summand case is immediate. I checked the hypotheses on the ring lemma (an arbitrary ring and every integer m) and on the item (arbitrary scheme and derived-category objects), and tested the statement on the zero and one-summand decompositions. The Mathlib searches were rerun for the new ring node with LeanFinder, Loogle, grep, and LeanSearch; no Mathlib result states the lemma.

## Unfinished

Nothing.

## Second reading by C1

- Item statement: checked against Cohomology Tag 08CE (`lemma-summands-pseudo-coherent`), with the scheme specialization and both summands matching the intended use; zero and one-summand cases are valid.
- Node `lem-pc-ring-pseudo-coherent-summand`: checked against More Algebra Tag 064X (`lemma-summands-pseudo-coherent`), including arbitrary ring, integer m, and the pseudo-coherent consequence; tested on the zero complex and a field.
- Item step 1: checked the affine reduction against Tag 08CE and the cited affine equivalence and criterion; the original step omitted those interfaces, so it was expanded to state the module transport explicitly.
- Item step 2: checked against the local definition in Tag 08CE; the conclusion for each summand and the zero-summand case are elementary once affine witnesses exist.

Changes made:

- Corrected the item node's `created.item` metadata from `lem-pc-perfect-summand` to `lem-pc-pseudo-coherent-summand`.
- Added citations to `lem-pc-affine-qcoh-derived-equivalence` and `lem-pc-affine-pseudo-coherent-criterion` and rewrote Step 1 to justify passage between sheaf and module complexes.
- Updated `proof_deps` to match the repaired Step 1.
