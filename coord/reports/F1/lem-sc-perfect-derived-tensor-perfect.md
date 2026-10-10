Files written:

- `dag/nodes/sec-picard-framework/lem-sc-perfect-derived-tensor-perfect.json`: statement node, split, no new nodes, Mathlib searches found no match.

Attachments: none.

WANTED: `literature/stacks-project/cohomology.tex`, Lemma `lemma-tensor-perfect` (Tag 09J5), for the source proof text; the repository contains only the citation index.

What was checked or corrected: the imported node had the correct statement and dependencies but no proof. I retained its scheme, perfect-complex, and derived-category hypotheses, and did not introduce a duplicate lemma. The proof is local on affine opens. Step 1 cites `lem-pc-perfect-affine-bounded-projective`, whose statement exactly supplies bounded complexes of finite projective modules representing each perfect restriction. Step 2 cites `lem-pc-bounded-above-flat-kflat`, whose statement exactly gives K-flatness for bounded-above termwise-flat sheaf complexes, and `def-pc-kflat-complex` for the K-flat-resolution meaning. Step 3 is elementary: finite projectives are direct summands of finite free modules, tensoring such summands gives a summand of a finite free tensor, and bounded totalization has finite-projective terms. I checked the zero complex and degree-zero cases, and the argument works on every affine member of the cover.

## Not duplicates

`lem-sc-perfect-derived-tensor-perfect` vs `lem-pc-perfect-affine-bounded-projective`: the former proves closure of perfect objects under derived tensor on arbitrary schemes; the latter only characterizes one perfect object on an affine scheme by a bounded finite-projective model.

## Review by F1

I read the target node, its imported source citation, the definitions `def-pc-perfect-complex`, `def-pc-derived-category`, `def-pc-kflat-complex`, and the full statements of both cited lemmas. The affine-model hypothesis in Step 1 is exactly what the cited affine lemma states. In Step 2, finite projective terms are flat and bounded, so the cited K-flat lemma applies; the K-flat definition confirms that the chosen model computes derived tensor. Step 3 uses no unstated theorem beyond the direct-summand calculation written in the step. I searched the whole DAG and blueprint for an existing tensor-perfect statement, found no duplicate, and ran LeanFinder, Loogle, grep, and LeanSearch searches; LeanSearch was unavailable and recorded as such. No new node was created, so there are no additional source or Mathlib leaf reviews.

What could not be finished: the Stacks TeX source itself is absent from this checkout, so the report records it as WANTED; the imported Tag 09J5 citation and standard proof route were used.

## Second reading by F1

- Item statement: checked against the imported Stacks citation for `cohomology.tex`, Lemma `lemma-tensor-perfect` (Tag 09J5); the source TeX is absent in this checkout, so the statement was checked against the citation record and the definition dependencies. Verdict: hypotheses and conclusion are retained exactly.
- Step 1: checked `def-pc-perfect-complex` for locality of perfectness and `lem-pc-perfect-affine-bounded-projective` for affine bounded finite-projective models. Verdict: correct; added the previously implicit definition citation.
- Step 2: checked `lem-pc-bounded-above-flat-kflat` and `def-pc-kflat-complex`; finite projectives are flat by the direct-summand-of-free argument stated in the step. Verdict: correct.
- Step 3: checked bounded totalization, tensoring finite direct summands, and the definition of strictly perfect. Verdict: elementary and correct; it handles the zero complex and degree-zero cases.
- New nodes: none; duplicate and Mathlib searches were reviewed in the worker record, with LeanSearch correctly marked unavailable.
- Small cases: the zero complex gives the zero tensor, a field gives bounded finite-dimensional complexes, the empty scheme is covered vacuously, and degrees 0 or 1 reduce to ordinary tensor products of finite projectives.
- Changes: cited `def-pc-perfect-complex` in Step 1 and added its verbatim citation entry; added this second-reading audit. The imported source remains unavailable locally, so no source text was fabricated.
