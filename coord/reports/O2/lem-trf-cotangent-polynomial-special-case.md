# Stage 1 report: lem-trf-cotangent-polynomial-special-case

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-cotangent-polynomial-special-case.json`: item split into five proof steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node at every proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, its blueprint tag, and the cotangent-polynomial terminology; no sorry-free declaration states the item.

## WANTED

None.

## What was checked and corrected

The imported item statement agrees with Stacks Project, cotangent.tex Tag 08SI (lemma-special-case): $P=\mathbf Z[x_1,\ldots,x_n]$, the augmentation to $B=\mathbf Z$, the ideal $J=(x_1,\ldots,x_n)$, and the shifted conormal complex are all present, including $n=0$. I searched the whole DAG and the current blueprint for the Tag 08SI statement and for the phrases “polynomial cotangent”, “conormal basis”, and “$J/J^2$”; no duplicate node exists. The existing dependencies are the transitivity triangle, polynomial cotangent identification, arbitrary-variable polynomial differential basis, and regular-sequence conormal basis. Mathlib searches for the item were run with LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; the returned APIs concern presentation cotangent maps and H1, but no derived special-case theorem, so the item remains a non-Mathlib statement.

## Review by N2

I read the full Stacks proof of Tag 08SI at `literature/stacks-project/cotangent.tex` lines 2673--2699, together with Tag 08QX (transitivity triangle), Tag 08QH (polynomial cotangent complex), and Tag 08SI’s cited surjection lemma at lines 1897--1905. I also opened every existing node cited by the five steps. Step 1 uses exactly the distinguished triangle stated by `lem-trf-cotangent-transitivity-triangle`, with the triple $\mathbf Z\to P\to\mathbf Z$. Step 2 uses the polynomial augmentation isomorphism stated by `lem-trf-smooth-cotangent-identification` and the free differential basis stated by `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`; the finite basis is a specialization of the arbitrary-set statement. Step 3 uses only the standard-resolution definition in `lem-trf-cotangent-resolution-coherence`; the identity resolution contracts in two-term identity pairs, so $L_{\mathbf Z/\mathbf Z}=0$. Step 4 is the elementary rotation of the cited distinguished triangle after the zero middle term. Step 5 uses the existing conormal-basis statement `lem-weil-pbc-regular-sequence-conormal-free` after checking directly that $x_1,\ldots,x_n$ is regular in the polynomial ring, and the differential basis from Step 2; it constructs the canonical basis-to-basis isomorphism and checks the empty-basis case $n=0$. I checked that each citation quote in `citations.json` is a verbatim part of the cited node’s statement, that every proof dependency is listed, and that no new node was created merely for an elementary specialization or for a clause of the item.
