# Stage-1 report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-brauer-algebraic-function-field-zero.json`: item, split; Mathlib no match.
- `dag/nodes/sec-curve-estimates/lem-sc-brauer-class-finite-descent.json`: statement-only dependency; Mathlib no match.

2. Attachments: none.

3. WANTED: none.

4. The item source is the blueprint proof for `lem-sc-function-field-cd-one`, third paragraph. The imported item had no proof; I supplied the paragraph's descent, C₁, and splitting route. The whole-blueprint search found no existing node for finite descent of central simple algebras, and DAG keyword searches found no duplicate. The new dependency is statement-only as required. The target hypotheses imply E is algebraic over k(C), since L is algebraic over k(C) and E is finite over L.

## Review by H1

I read the item JSON, the neighboring `lem-sc-tsen`, `lem-sc-c1-finite-extension`, and `lem-sc-c1-brauer-trivial` node statements, and the source module `WeilConjectures/AlgebraicGeometry/Curve/Brauer.lean`. No exact sorry-free declaration states this item; the source theorem there only treats the original function field and is not an attachment. Step 1 uses the new descent statement exactly: it supplies a finite intermediate field and a descended central simple algebra. Step 2 uses the cited statements exactly: Tsen supplies that k(C) is C₁, finite extension stability supplies C₁ for K', and the C₁ Brauer lemma supplies splitting. Step 3 uses the descent statement's explicit scalar-extension equivalence; the matrix splitting remains split after scalar extension, which is an elementary base-change observation. I checked the hypotheses in the small case E = L = k(C), and the argument reduces to Tsen's theorem. The Mathlib searches were run for both nodes with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. `citations.json` quotes the exact portions of each cited statement used by each step.

5. Nothing remains unfinished.
