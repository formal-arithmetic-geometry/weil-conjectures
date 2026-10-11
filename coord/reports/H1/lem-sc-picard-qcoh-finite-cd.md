Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-picard-qcoh-finite-cd.json` (split statement; Mathlib searches found no match)
- `citations.json` (verbatim quotes for steps 1 and 3)

Attachments: none. No sorry-free declaration tagged `lem-sc-picard-qcoh-finite-cd` or stating this result was found under `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2`.

WANTED: none.

The item statement is the finite cohomological-dimension assertion of Stacks Tag 01XI (`literature/stacks-project/coherent.tex`), for a quasi-compact scheme over a field with affine diagonal and all quasi-coherent modules. It is a leaf input at this stage: the imported split carries only its statement, with no hidden proof sketch or new child. I searched the DAG and project source for the item, for Tag 01XI, and for the finite-cohomological-dimension and affine-diagonal terminology; no existing node states this result. The nearby `pqf-lem-serre-criterion` is different: it is a converse affineness criterion using only H^1 of finite-type ideals.

## Review by H1

I read Tag 01XI and checked the item hypotheses and conclusion. Step 1 uses the existing affine-diagonal-intersection statement exactly to make all finite intersections affine; Step 2 is elementary finite-complex bookkeeping; Step 3 uses the existing Cech comparison statement exactly as quoted in `citations.json`. The cover is finite by quasi-compactness, and choosing d_X=N-1 handles N=1 as well as higher degrees. I searched the Lean source for the blueprint tag, likely declaration names, and the mathematical terms; no project declaration exists. I ran the required `leanfinder`, `loogle`, `grep`, and `leansearch` searches for this node. LeanFinder returned only unrelated limit and injective-dimension declarations; Loogle and grep found no matching scheme cohomology theorem; LeanSearch was unavailable and is recorded as such. The nearby `pqf-lem-serre-criterion` is not a duplicate, since it has a different hypothesis and conclusion.

## Not duplicates

lem-sc-picard-qcoh-finite-cd vs pqf-lem-serre-criterion: the existing node assumes H^1 vanishing for finite-type ideal sheaves and concludes affineness, while this node gives a uniform higher-cohomology bound for every quasi-coherent module under an affine-diagonal hypothesis.

## Second reading by H1

- Item statement: checked against Stacks Tag 01XI, label `coherent-lemma-vanishing-nr-affines`; the quasi-compact affine-diagonal hypotheses and uniform vanishing conclusion agree (the field hypothesis is a permitted specialization in this unit).
- Step 1: checked against the finite affine-cover and affine-intersection paragraphs of Tag 01XI and against `lem-sc-picard-affine-diagonal-intersections`; finite intersections follow by induction from the cited pairwise result.
- Step 2: checked against the alternating/normalized Cech-complex paragraph of Tag 01XI; with N cover members, repeated indices are removed and the degree-p terms vanish for p >= N. This is elementary finite-complex bookkeeping.
- Step 3: checked against Tag 01XI and the statement of `lem-pc-cech-computes`; its hypotheses hold because every finite intersection from Step 1 is affine, and the conclusion gives the claimed bound with d_X = N - 1.
- New nodes: no additional nodes were introduced; the existing cited nodes were searched in `dag/nodes` and their statements provide exactly the facts used.
- Edge cases: N = 1 gives d_X = 0 and the affine vanishing case; the zero module and a field-valued affine scheme satisfy the statement; the empty scheme is covered by the vacuous finite cover convention in the source.
- Mathlib searches: the recorded leanfinder, Loogle, grep, and unavailable LeanSearch searches were checked against `searches.jsonl`; none states this scheme-cohomology result.

No file or node changes were required after this reading. The proof steps, citations, source tag, dependencies, and blueprint reference were all retained because they pass the statement and route checks.
