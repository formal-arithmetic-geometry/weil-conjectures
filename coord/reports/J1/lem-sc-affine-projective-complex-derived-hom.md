1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-projective-complex-derived-hom.json`: statement, kind `statement`, no new Mathlib leaf; split with two proof steps.
- `citations.json`: four verbatim step-to-node quotations.

2. Attachments: none.

3. WANTED: none. The relevant Stacks source is available in the review checkout at `/home/ubuntu/c1-stacks-review/cohomology.tex`; the repository's literature mirror does not contain the generated `.tex` files.

4. The item was unsplit and had no Lean declaration with its blueprint tag. I checked the whole DAG and found `lem-sc-derived-hom-projective-resolution`, but that statement only treats a module in degree zero and is therefore a specialization, not a duplicate. The existing `lem-sc-bounded-above-projective-kprojective` is a Mathlib leaf and supplies exactly the K-projectivity assertion used here. The item's existing Mathlib searches were rerun through `msearch.py`; LeanFinder returned K-projectivity/projective-resolution generalizations, Loogle found no `HomComplex` match, grep found no exact theorem, and LeanSearch was unavailable.

## Review by J1

I read Stacks Tag 0GM8, `lemma-stalk-internal-hom`, case (2), and used the project’s existing derived-Hom construction together with the K-projective construction cited by Tag 06XR. Step 1 takes from `def-pur-derived-internal-hom` its Hom-complex representative after a K-injective resolution, and takes from `lem-sc-bounded-above-projective-kprojective` precisely that Hom from the bounded-above projective complex sends acyclic complexes to acyclic complexes; the mapping-cone argument then gives the needed quasi-isomorphism. Step 2 uses only the Hom-complex product formula from the definition: with `P^p=0` above `b` and `L^q=0` below `a`, a degree-`n` factor requires `p≤b` and `p+n≥a`, so the complex is zero for `n<a-b`. I verified that all hypotheses in the item are used at those steps and that the cited node statements say exactly what each step takes. I also checked the small edge cases of a zero complex and complexes concentrated in a single degree: the degree bound and representative assertion reduce to the expected zero or ordinary Hom statement. No statement or source route was changed, and no subordinate node was created because the only non-elementary dependency already exists as a Mathlib leaf.

5. Nothing remains unfinished.

## Second reading by J1

- Item statement: checked against Stacks Tag 0GM8, `lemma-stalk-internal-hom`, case (2), and the ring-valued one-point specialization; the bounded-above projective and bounded-below hypotheses and the negative-degree bound agree.
- Step 1: checked against the statements of `def-pur-derived-internal-hom` and `lem-sc-bounded-above-projective-kprojective`; the mapping-cone quasi-isomorphism argument uses exactly the cited K-projectivity assertion.
- Step 2: checked against the Hom-complex product formula in `def-pur-derived-internal-hom`; the inequalities force degree `n` to vanish for `n<a-b`, including zero and one-degree complexes.
- Existing dependency `lem-sc-bounded-above-projective-kprojective`: checked as the exact Mathlib specialization `CochainComplex.isKProjective_of_projective` (KProjective.lean:113); no duplicate node is needed.
- Existing dependency `def-pur-derived-internal-hom`: checked as the source of the K-injective representative and Hom-complex formula; the ring interpretation is now stated explicitly as the one-point ringed-site specialization.
- Mathlib searches: reran grep, Loogle, and LeanFinder searches recorded in the node; no exact arbitrary-complex derived-Hom declaration was found, while the K-projective declaration was confirmed.
- Small cases: tested the zero complex and complexes concentrated in one degree; the representative and lower-degree vanishing reduce to the ordinary Hom complex and the expected zero range.
- Changes: added the explicit one-point ringed-site and `D(R)` interpretation plus the degree-term formula, added `def-weil-abstract-derived-category` to `stmt_deps`, corrected the proof wording to identify the specialization, and fixed `created.item` to this delivered item. These changes close the implicit ring/sheaf interface and provenance faults without weakening the claim.
