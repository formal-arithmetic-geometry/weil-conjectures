1. Files written:
   - `dag/nodes/sec-picard-framework/lem-pc-derived-free-complex-cover.json`: statement, three-step split proof, no Mathlib match.
   - `citations.json`: empty list, because all proof steps are elementary constructions.

2. Attachments: none.

3. WANTED: `literature/stacks-project/dga.tex`, Differential Graded Algebra, Lemma 15.60.8 (Tag 09KN), for `lem-pc-derived-free-complex-cover`.

4. The imported node had no proof. Its statement is the corrected Tag 09KN formulation: the cover includes contractible two-term summands and additional zero-differential shifts for cocycles. No statement change was needed. The local Stacks TeX source is absent, so the source is recorded as WANTED. The whole-blueprint searches for “free two-term complex cocycle cover 09KN” and “two-term pieces shifts A[k]” found no duplicate blueprint node; DAG keyword/tag searches found only this item and its existing use in `lem-pc-derived-filtered-free-resolution`.

5. Nothing remains unfinished in the split. The external source file is unavailable locally, but the construction and its verification are written out from the cited Tag 09KN route.

## Review by H1

I read the item and its dependent use in `lem-pc-derived-filtered-free-resolution`, and checked the statement against the imported Tag 09KN description. The item introduces a ring, a cochain complex, and the required cover, while the existing dependency `def-pc-cochain-complex-modules` supplies the complex notion. I also searched the Lean source in both available checkouts for the item id, the Tag 09KN marker, and the relevant free-complex terminology; no project declaration states this result, so it is not an attachment.

Step 1 constructs, for each element m in each degree, the two-term identity complex mapping its generators to m and d(m). The cited source statement is not used as a black box; the map condition is the elementary identity d^2=0, and these lower generators prove degreewise surjectivity. Step 2 adds one zero-differential shift for each cocycle z, mapped to z; this proves surjectivity on cocycles and preserves the degreewise map. Step 3 identifies Q' with all upper terms and cocycle shifts and Q'' with all lower terms. The identity differentials land in Q', both subquotient differentials vanish, and the direct-sum decomposition gives degreewise splittings and the asserted short exact sequence. No step cites a node, so `citations.json` is empty and there are no C1/C4 quote obligations.

I tested the construction on the zero complex and on the one-term complex M=A[0]. In the latter case the lower generator gives degreewise surjectivity and the added A[0] cocycle summand gives the nonzero cocycle; this rules out the previously rejected construction using only contractible pieces. The Mathlib searches used LeanFinder, Loogle, grep, and LeanSearch (the latter unavailable); they found only general homological declarations and no matching cover theorem. The item carries the required blueprint ancestor and proof-place reference.

## Second reading by H1

- Item statement: checked against `dga.tex`, Tag 09KN (`lemma-good-quotient`); hypotheses and all three properties agree, including the zero complex and $A[0]$ cases.
- Step 1: checked against the Tag 09KN construction of the two-term $P_k$ summands; $d_M^2=0$ gives a complex map and lower generators give degreewise surjectivity; elementary is appropriate.
- Step 2: checked against the Tag 09KN cocycle-shift construction; each cocycle receives a zero-differential shift and degreewise surjectivity is preserved; elementary is appropriate.
- Step 3: checked against the Tag 09KN admissible short exact sequence property; the direct-sum decomposition gives the degreewise split sequence and zero differentials on both factors; elementary is appropriate.
- New node `lem-pc-derived-free-complex-cover`: statement-only split item, self-contained definition citation, TeX, source tag/label, blueprint search, and Mathlib search records checked; no duplicate found.
- Changed `created.item` from the dependent item `lem-pc-derived-filtered-free-resolution` to this delivered item, as required for a new node.
- No proof citations or auxiliary nodes were needed; the repository lacks the source file, so the local review checkout was used for the Tag 09KN comparison.
