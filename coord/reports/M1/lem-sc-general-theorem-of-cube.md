# Stage 1 report: lem-sc-general-theorem-of-cube

## Files written

- Item: `dag/nodes/sec-abelian-varieties/lem-sc-general-theorem-of-cube.json` (repaired split, 8 proof steps).
- New statement-only nodes: `lem-sc-proper-flat-global-sections` (Tag 0E0L, no Mathlib match), `lem-sc-picard-diagonal-locally-closed` (Tag 0BDP, no Mathlib match), `lem-sc-picard-locus-closed` (Tag 0BF0, no Mathlib match), and `lem-sc-picard-product-open` (Tag 0BF3, no Mathlib match).
- `citations.json` contains verbatim quotes for every cited node use.

## Attachments

None.

## WANTED

None.

## What was wrong

The returned version made the item a one-line specialization of a new unsplit arbitrary-base theorem, which violated D1/D2. I removed that node and followed the actual proof of Tag 0BF4 in `more-morphisms.tex` after line 9682. The proof now makes the product pushforward, universal locally closed locus, closedness, openness, connectedness, and final slice pullback explicit. The four non-elementary Stacks inputs are separate statement-only nodes.

## Not duplicates

lem-sc-proper-flat-global-sections vs existing DAG: no node with Tag 0E0L or the universal structure-sheaf pushforward statement was found.
lem-sc-picard-diagonal-locally-closed vs existing DAG: no node with Tag 0BDP or the Picard diagonal universal-locus statement was found.
lem-sc-picard-locus-closed vs existing DAG: no node with Tag 0BF0 or the closed Picard locus statement was found.
lem-sc-picard-product-open vs existing DAG: no node with Tag 0BF3 or the product Picard openness statement was found.

## Review by M1

I read the item statement and its application in `dag/nodes/sec-abelian-varieties/thm-sc-theorem-of-cube.json`, then checked the source proof in `/home/ubuntu/c1-stacks-review/more-morphisms.tex`, especially the theorem-of-the-cube proof after line 9682 and the definitions of Tags 0BDP, 0BF0, and 0BF3. Step 1 checks the proper, flat, finite-presentation and geometrically integral product hypotheses over a field; this is elementary from the field and product assumptions. Step 2 uses the exact universal pushforward conclusion of Tag 0E0L, recorded in `lem-sc-proper-flat-global-sections`. Steps 3 and 4 use the universal-factorization characterization from Tag 0BDP, including why the given fibre triviality puts `z` in the locus. Step 5 uses the closed-immersion conclusion of Tag 0BF0, and step 6 uses the neighbourhood-triviality conclusion of Tag 0BF3 after rewriting the product over `Z`. Steps 7 and 8 are the connected clopen argument and the direct pullback along `x × y × id`, so they are elementary. Every cited node was opened and its quoted sentence was copied verbatim into `citations.json`; all hypotheses used by each step are present in those statements. I searched the DAG and blueprint for each tag before creating the four nodes, and ran LeanFinder, Loogle, grep, and LeanSearch for every new node (LeanSearch was unavailable and recorded as such). The obsolete over-base node was removed.

## Second reading by M1

- Item statement: checked against More on Morphisms, Theorem 37.33.8, Tag 0BF4 and the theorem-of-the-cube application; the field specialization and residue-field point agree.
- Steps 1-2: checked against the product-fibre paragraph and Tag 0E0L; product properties and universal pushforward hypotheses are present.
- Steps 3-4: checked against Tag 0BDP; the repaired node defines the cartesian square and projections and the fibre factorization is valid.
- Step 5: checked against Tag 0BF0; the product fibres are geometrically integral and the universal locus is the Tag 0BDP locus.
- Step 6: checked against Tag 0BF3 and lines 9704-9711; slice triviality, residue-field fibre triviality, and factorization of the resulting open neighbourhood through the locus are explicit.
- Steps 7-8: checked against the connected clopen conclusion and final slice pullback in Tag 0BF4.
- New node `lem-sc-proper-flat-global-sections`: statement-only, self-contained, Tag 0E0L, searches recorded.
- New node `lem-sc-picard-diagonal-locally-closed`: statement-only, self-contained after defining the cartesian square, Tag 0BDP, searches recorded.
- New nodes `lem-sc-picard-locus-closed` and `lem-sc-picard-product-open`: statement-only, self-contained, Tags 0BF0 and 0BF3, searches recorded.

Changes: defined the Tag 0BDP node's previously undefined $p,q$; made the product-fibre step explicit; expanded Step 6; synchronized verbatim citations; and recorded this audit.
