Files written:

- `dag/nodes/sec-abelian-varieties/pqf-lem-serre-criterion.json` (statement, split; no Mathlib match)
- `dag/nodes/sec-abelian-varieties/lem-pqf-qcoherent-ideal-colimit.json` (statement-only child; no Mathlib match)
- `dag/nodes/sec-abelian-varieties/lem-pqf-quasicompact-h1-zero.json` (statement-only child; no Mathlib match)
- `citations.json`

Attachments: none.

WANTED: none.

## Not duplicates

lem-pqf-qcoherent-ideal-colimit vs pqf-lem-serre-criterion: the new node states the Tag 01PG directed-colimit decomposition of an arbitrary quasi-coherent ideal; the item states the Tag 01XG affineness criterion assuming vanishing only for finite-type ideals.

lem-pqf-quasicompact-h1-zero vs lem-weil-pbc-finite-surjective-affine-target-noetherian: the new node states Tag 01XF for an arbitrary quasi-compact scheme with H^1 vanishing for every quasi-coherent ideal; the existing node is a finite-surjective morphism theorem that only cites 01XF in its proof and does not state the criterion.

The imported item had only a one-line restatement of Tag 01XG, which was a D1/D2 split defect. I replaced it with the actual two-part proof in Tag 01XG: first pass from finite-type ideal sheaves to arbitrary quasi-coherent ideal sheaves by the Tag 01PG directed-colimit result and cohomology commuting with filtered colimits; then apply Tag 01XF. The two missing classical inputs are separate statement-only children rather than hidden clauses of the item. No sorry-free declaration in either Lean source checkout states the item or either child. The existing `lem-weil-pbc-qs-scheme-cohomology-directed-colimit` node is a general module-cohomology result and is cited as a cross-unit tool use.

## Review by E1

I read the item source in the blueprint and the full Stacks proof in `coherent.tex`: Tag 01XG at the lemma and proof around lines 391-417, including its references to Tag 01PG and Tag 01XF. I also read the existing `lem-weil-pbc-qs-scheme-cohomology-directed-colimit` statement and verified that it applies to a quasi-compact open `U = X` of a quasi-compact, quasi-separated scheme and to the directed system of quasi-coherent ideal sheaves. Its statement explicitly supplies the canonical filtered-colimit comparison in every degree, so step 1 uses exactly what it says; the hypothesis makes each finite-type term's `H^1` zero, hence the colimit group is zero. The new 01PG child states precisely the ideal-sheaf directed-colimit fact used there, and the new 01XF child states precisely the final quasi-compact criterion used in step 2. I checked the hypotheses in both steps: quasi-compactness and quasi-separatedness are item assumptions, and the family in step 1 consists of quasi-coherent finite-type ideal subsheaves. I searched the whole DAG and blueprint for both facts and found no duplicate nodes or blueprint statements. I ran LeanFinder, Loogle, and Mathlib grep searches for the item and each new child; the results contain only generic affine/quasi-coherent declarations and no matching theorem. I checked small edge cases conceptually (the empty scheme and an affine scheme satisfy the criterion trivially). The citations file quotes the exact statements used by each proof step.
I read the item source in the blueprint and the full Stacks proof in `coherent.tex`: Tag 01XG at the lemma and proof around lines 391-417, including its references to Tag 01PG and Tag 01XF. I also read the existing `lem-weil-pbc-qs-scheme-cohomology-directed-colimit` statement and verified that it applies to a quasi-compact open `U = X` of a quasi-compact, quasi-separated scheme and to the directed system of quasi-coherent ideal sheaves. Its statement explicitly supplies the canonical filtered-colimit comparison in every degree, so step 1 uses exactly what it says; the hypothesis makes each finite-type term's `H^1` zero, hence the colimit group is zero. The new 01PG child states precisely the ideal-sheaf directed-colimit fact used there, and the new 01XF child states precisely the final quasi-compact criterion used in step 2. I checked the hypotheses in both steps: quasi-compactness and quasi-separatedness are item assumptions, and the family in step 1 consists of quasi-coherent finite-type ideal subsheaves. I searched the whole DAG and blueprint for both facts and found no duplicate nodes or blueprint statements. I ran LeanFinder, Loogle, and Mathlib grep searches for the item and each new child; the results contain only generic affine/quasi-coherent declarations and no matching theorem. I checked small edge cases conceptually (the empty scheme and an affine scheme satisfy the criterion trivially). The citations file quotes the exact statements used by each proof step.

## Second reading by E1

- Item statement: checked against Cohomology Tag 01XG (`lemma-quasi-separated-h1-zero-covering`), hypothesis by hypothesis; verdict: agrees.
- Step 1: checked against Tags 01PG and 01FF and the cited node statements; verdict: agrees.
- Step 2: checked against Tag 01XF (`lemma-quasi-compact-h1-zero-covering`); verdict: agrees.
- `lem-pqf-qcoherent-ideal-colimit`: checked against Tag 01PG; verdict: repaired with its required quasi-compact and quasi-separated hypotheses.
- `lem-pqf-quasicompact-h1-zero`: checked against Tag 01XF, including empty and affine cases; verdict: agrees.
- Searches and duplicate checks: checked the recorded msearch logs and whole DAG; verdict: no matching declaration or duplicate.

Changes made: narrowed the 01PG child, added its quasi-compact definition dependency and the item's scheme dependency, and updated the citation quote.
