1. Files written:
   - `dag/nodes/sec-picard-framework/lem-pc-derived-filtered-free-resolution.json`: statement split with four proof steps.
   - `dag/nodes/sec-picard-framework/lem-pc-derived-free-complex-cover.json`: statement-only auxiliary node, no Mathlib match.
   - `dag/nodes/sec-picard-framework/lem-pc-derived-total-resolution-quasi-iso.json`: statement-only auxiliary node, no Mathlib match.
   - `citations.json` and this report.
2. Attachments: none.
3. WANTED: `literature/stacks-project/dga.tex`, Differential Graded Algebra Lemma 15.60.9 (Tag 09KP), for the item and its filtration construction.
   WANTED: `literature/stacks-project/dga.tex`, Differential Graded Algebra Lemma 15.60.8 (Tag 09KN), for `lem-pc-derived-free-complex-cover`.
   WANTED: `literature/stacks-project/homology.tex`, Homology Lemma 12.19.4 (Tag 09IZ), for `lem-pc-derived-total-resolution-quasi-iso`.
4. No statement error was found. The imported item had no proof; its source route was the explicit total-complex construction in Tag 09KP. I searched the DAG and blueprint for the item, Tags 09KN/09IZ, free two-term covers, and total-resolution quasi-isomorphisms; no duplicate nodes existed. Mathlib searches were run for the item and each new node with LeanFinder, Loogle, and grep; only general homological declarations appeared.

## Review by J1

I read the item against the local Stacks review checkout's proof of Tag 09KP and checked the ordinary-ring specialization: the iterated kernels form the exact resolution, the total complex has the stated signed differential, and the alternating two-step filtration has split inclusions and shift-of-A quotients. Step 1 cites the exact statement of `lem-pc-derived-free-complex-cover`, including degree and cocycle surjectivity. Step 4 cites the exact hypotheses and conclusion of `lem-pc-derived-total-resolution-quasi-iso`, which is the Tag 09IZ result used by 09KP. Steps 2 and 3 are the explicit two-line totalization and filtration checks from 09KP; their uses are elementary algebra once the construction is fixed. I tested the zero complex and a one-shift free module: the construction gives the zero filtration and a single shift quotient respectively. The source TeX files are not present in this repository, so the report records all three WANTED paths.
5. Nothing remains unfinished beyond the requested second-worker reading and delivery.

## Second reading by J1

- Item statement: checked against Differential Graded Algebra Lemma 15.60.9 (Tag 09KP) and its ordinary-ring specialization in Remark 15.60.11 (Tag 09PB); the ring, complex, quasi-isomorphism, exhaustive filtration, split inclusions, and shifted-summand clauses agree.
- Step 1: checked against the construction in Tag 09KP and the exact statement of `lem-pc-derived-free-complex-cover`; the kernel resolution and cocycle-surjectivity hypotheses are used as stated.
- Step 2: checked the signed total differential directly; the two components square to zero and anticommute, while the resolution composites vanish, so this is elementary after Step 1.
- Step 3: checked against the two-term summand construction in Tag 09KP; the repaired step explicitly orders the summands, verifies subcomplex closure, identifies both quotient types, and proves exhaustiveness. It cites `lem-pc-derived-free-complex-cover`.
- Step 4: checked against Homology Lemma 12.19.4 (Tag 09IZ) as used by Tag 09KP; its exact-complex and exact-cycles hypotheses now match the A-module resolution and yield the augmentation quasi-isomorphism.
- `lem-pc-derived-free-complex-cover`: statement-only, self-contained over a ring and A-module complex; the returned fault was reproduced on $M=A[0]$: a cover made only from contractible two-term pieces cannot surject onto the nonzero cocycle of $A[0]$. I corrected the statement to include the degreewise split sequence with $Q'$ and $Q''$ direct sums of zero-differential shifts, and retested $M=A[0]$ using the extra $A[0]$ summand in $Q'$; the cocycle map is then surjective. The zero complex and a one-term free module also pass, with no Mathlib declaration matching the corrected cover.
- `lem-pc-derived-total-resolution-quasi-iso`: statement-only, self-contained over the same ring and module category as the item; tested on the zero resolution and a split one-term resolution, with no Mathlib declaration matching the total-resolution theorem.

Changes made: corrected the returned false cover statement; updated Step 3 so all extra zero-differential shift summands are placed in $P_i'$ as cocycles; converted arrows, complexes, and kernels in the item and new-node statements to TeX; synchronized both citation quotes and this review. The total-resolution node remains aligned to A-modules with degreewise exactness.
