# Stage 1 report

1. Files written: item `lem-pc-noetherian-perfect-direct-image` (split); new statement-only node `lem-pc-noetherian-perfect-direct-image-finite-tor` (no Mathlib match).
2. Attachments: none.
3. WANTED: `literature/stacks-project/perfect.tex`, Lemma 36.27.2 / Tag 0DJQ and Lemma 36.27.1 / Tag 08EV, for the item and its prerequisite (the local repository has only the citation index).
4. The item had no sorry-free Lean declaration. I checked the source text available in the Stacks review checkout: Tag 0DJQ proves the tensor theorem by verifying the hypotheses of Tag 08EV for `E tensor^L G`. The new node records precisely that smaller criterion and is strictly below the item.

## Review by K1

I read the existing item, its parent `lem-pc-rf-perfect-base-change`, the unit record, and the source proof around `lemma-perfect-direct-image` and `lemma-tensor-perfect` in `perfect.tex`. Step 1 checks each hypothesis of Tag 08EV: a local bounded finite-free model for the perfect complex makes the tensor bounded with coherent cohomology; the support lies in the finite union of the proper supports of the terms; and termwise base-flatness gives finite Tor dimension over `f^{-1} O_S`. Step 2 cites the new node verbatim and applies its conclusion. The Noetherian and finite-presentation hypotheses are retained from the item, and the support argument is valid for the empty-support and degree-zero cases. I searched the full DAG and blueprint for the new criterion and found no existing node with that statement; Mathlib searches were run with LeanFinder, Loogle, grep, and unavailable LeanSearch and found no direct theorem. `citations.json` quotes the exact new-node statement used by step 2.

## Not duplicates

`lem-pc-noetherian-perfect-direct-image-finite-tor` vs `lem-pc-noetherian-perfect-direct-image`: the new node assumes bounded coherent cohomology, proper cohomological supports, and finite Tor dimension for an arbitrary derived object, while the item constructs these properties for a tensor of a perfect complex with a bounded flat finitely presented complex and concludes perfectness of its direct image.

5. What remains: the prerequisite is intentionally unsplit as a classical Stacks input; no Lean implementation is attempted at stage 1.

## Second reading by K1

- Item statement: checked against Stacks perfect.tex, Lemma 36.27.2, Tag 0DJQ; the stated Noetherian, finite-presentation, perfect, bounded finitely-presented flat, and proper-support hypotheses are retained, and the conclusion is the stated perfect derived direct image.
- Step 1: checked against the proof of Tag 0DJQ and the hypotheses of Tag 08EV; bounded finite-free local models give bounded coherent cohomology, tensor support is contained in the proper support of G, and termwise S-flatness gives finite Tor dimension. Verdict: passed after repairing the support justification.
- Step 2: checked against Tag 08EV; the cited prerequisite states exactly the criterion applied to E tensor^L G. Verdict: passed.
- New node `lem-pc-noetherian-perfect-direct-image-finite-tor`: checked hypothesis by hypothesis against Tag 08EV; it is statement-only, self-contained, cites definition nodes, uses the Stacks tag and label, and has no Mathlib match after the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches. Verdict: passed.
- Small cases checked: the zero complex and empty scheme satisfy the criterion vacuously; over a field, finite Tor dimension is automatic for bounded complexes, and degree-zero E or G reduces to the usual coherent proper-support direct-image criterion.

Changes: repaired step 1 so properness follows from support containment in G rather than an unstated claim about term supports; added this second-reading audit and edge-case record. No nodes were removed or added.
