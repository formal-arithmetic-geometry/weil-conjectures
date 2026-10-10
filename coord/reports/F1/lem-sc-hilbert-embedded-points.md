1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-embedded-points.json`: split statement node.
- No new subordinate node: the exact existing node `lem-weil-pbc-noetherian-associated-primes-finite` (Tag 00LC, Mathlib leaf) is cited.
- `lem-sc-hilbert-embedded-points-gluing`: statement-only helper for localization-compatible sheaf gluing.
- `lem-sc-hilbert-embedded-points-dimension-drop`: statement-only helper for the finite-union Krull-dimension inequality.

2. Attachments: none.

3. WANTED: the local Stacks Project source `literature/stacks-project/divisors.tex`, Tag 02OL (Lemma 31.5.8, `divisors-lemma-remove-embedded-points`), was not present in this checkout; the proof is therefore recorded as an agent reconstruction of the cited argument.

4. The original item was unsplit and had stale search metadata (a finite-difference Loogle query unrelated to the statement). I replaced the metadata with searches actually run on 2026-10-11 and added the exact Mathlib finiteness leaf. The item proof now follows the Tag 02OL route: affine finite-module annihilator construction, localization and gluing, support/no-embedded-point conclusions, and the finite-dimensional strict drop. The finite associated-prime assertion is cited verbatim from the new leaf; the remaining steps are written as the reconstruction because the source file is unavailable.

## Review by F1

I read the item, its unit and chapter records, the downstream Hilbert-polynomial proof, and the available slopmaster2 source. No declaration with the item tag or equivalent theorem exists, and the source contains only the downstream theorem with `sorry`. I checked the item hypotheses against the imported statement: locally Noetherian $X$ and coherent $\\mathcal F$ are sufficient for affine finite-module presentations, and the finite-positive dimension qualifier is retained because the strict inequality is not valid for infinite dimension. I searched the whole DAG and blueprint for 02OL, embedded associated-point removal, and the affine statement; the existing exact 00LC node was found and cited rather than duplicated.

The two new helpers are strictly narrower than the item: the gluing helper assumes compatible affine submodules and only constructs the coherent subsheaf/quotient, while the dimension helper concerns arbitrary finite unions of proper closed subsets and does not mention sheaves or associated points. No existing node states either helper.

For step 1, the cited existing 00LC node states exactly that $\\operatorname{Ass}(M)$ is finite, which is the only non-elementary DAG fact used explicitly. Steps 2--4 use the affine localization/gluing and dimension arguments from Tag 02OL; their source and the missing-document limitation are recorded explicitly. I tested the boundary cases conceptually: a module with no embedded primes gives $\\mathcal K=0$, and the strict dimension assertion is invoked only when the support dimension is finite and positive. The required Mathlib searches were run and recorded, including LeanSearch being unavailable.

5. Nothing remains unfinished apart from obtaining the missing Stacks source; no Lean code was written.

## Second reading by F1

- Item statement: checked against Divisors Tag 02OL, label `lemma-remove-embedded-points`; verdict: repaired to include maximality and the dense-open agreement, and removed the unsupported dimension inequality.
- Step 1: checked against Algebra Tag 02M6 and its finite-module hypotheses; verdict: repaired to use the exact affine lemma.
- Step 2: checked against Algebra Tag 02M7 and Divisors Tag 02OL; verdict: repaired to state localization compatibility before gluing.
- Step 3: checked against the conclusions of Tags 02M6, 02M7, and 02OL; verdict: repaired to derive the three sheaf conclusions and dense-open agreement.
- `lem-sc-hilbert-embedded-points-affine-removal`: checked against Algebra Tag 02M6, self-contained statement and source label; verdict: retained as a needed strict sublemma.
- `lem-sc-hilbert-embedded-points-affine-localization`: checked against Algebra Tag 02M7, self-contained statement and source label; verdict: retained as a needed strict sublemma.
- `lem-sc-hilbert-embedded-points-gluing`: checked as the localization-compatible sheaf gluing helper; verdict: retained.
- `lem-sc-hilbert-embedded-points-dimension-drop`: verdict: removed because Tag 02OL does not state it and the prior split added it without source support.

Changes: corrected the item to the source statement, added Tags 02M6 and 02M7 as the actual algebra dependencies, removed the unsupported dimension helper and citations, corrected `created.item`, and refreshed the proof citations and search log.
