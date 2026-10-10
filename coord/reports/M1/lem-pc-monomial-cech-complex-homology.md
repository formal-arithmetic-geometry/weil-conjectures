Files written:

- `dag/nodes/sec-picard-framework/lem-pc-monomial-cech-complex-homology.json` (item, split; no Mathlib match).

Attachments: none.

WANTED: `literature/stacks-project/coherent.tex`, Tag 01XS, for the item; the checked-out literature bundle on this machine contains only citation indexes.

The Lean source was searched by item id and by monomial-Cech terminology. It contains related declarations in `WeilConjectures/AlgebraicGeometry/ProjectiveSpace/MonomialCech.lean`, including `subsingleton_monomialCechComplex_homology_zero` and top-homology equivalences, but no declaration for the exponent-vector subcomplex statement, so this is not an attachment. The DAG and blueprint were searched for the item and for simplex/contracting-homotopy statements; no duplicate statement was found. The required Mathlib searches were run for the item; LeanSearch was unavailable, Loogle returned the recorded unknown-identifier result, and the other searches found only general homotopy APIs.

## Not duplicates

lem-pc-monomial-cech-complex-homology vs lem-pc-twist-cech-monomial-decomposition: both cite Tag 01XS, but the existing node decomposes the projective-space Cech complex into exponent-vector summands, whereas this item computes the cohomology of one summand.
lem-pc-monomial-cech-complex-homology vs lem-pc-projective-space-twist-cohomology: both cite Tag 01XS, but the existing node is the global projective-space twist cohomology statement and this item is its combinatorial exponent-vector subcomplex calculation.

## Review by M1

I checked the item statement against the imported citation entry for Stacks Tag 01XS and the corresponding blueprint clause in `lem-pc-projective-space-twist-cohomology`. The three proof steps follow the source's three cases for `N_e`: the empty case is the standard augmented simplex calculation, the nonempty proper case chooses an index outside `N_e` and uses the explicit homotopy identity, and the full case is the one-term complex. The first and third steps are marked elementary because they are direct basis calculations from the displayed differential and definitions.

The middle step writes the supporting algebraic identity directly: deleting a chosen index outside `N` gives a degree-lowering homotopy, and the terms in `d h+h d` cancel pairwise except for the identity term. I checked that deleting `r` preserves the condition `N subseteq J`, and that the endpoint convention gives vanishing degree-zero cohomology in the star case. Small cases `I={0,1}`, `N={0}` and `I={0,1,2}`, `N={0,1}` were checked directly: the alternating signs cancel in `d h+h d`. The full and empty cases were checked for `n=1` and `n=2` by listing the allowed subsets.

No source error or Lean attachment was found. The source file itself was unavailable locally, so the report records the requested `WANTED` entry rather than claiming a local file review.

## Second reading by M1

- Item statement: checked against Stacks Tag 01XS, Lemma 30.8.1, especially the graded Cech terms (lines 50--61), and the three NEG cases (lines 62--98); the hypotheses `A` a ring, `n >= 1`, and the subset containment condition agree. Verdict: correct.
- Node `lem-pc-monomial-cech-complex-homology`: B1 statement-only form, B2 self-contained notation, B3 definition coverage for `N_e`, free modules, subsets, and cohomology, B4 TeX formatting, B5 tag/label source, B6 not a Mathlib leaf, and B7 no tag-only meaning; all checked. The node's `created.item` metadata is retained by `deliver.py` from the repository maintainer fields; the split file itself is otherwise consistent.
- Step 1: checked against the empty-NEG discussion in Tag 01XS (lines 70--84), including the all-subsets ordered Cech complex and its degree-zero cohomology. Verdict: elementary and sufficient.
- Step 2: checked against Tag 01XS (lines 85--98). The chosen `r` is outside `N_e`, so deleting `r` preserves `N_e subseteq J`; the displayed sign is the ordered insertion/deletion sign, and the pairwise cancellation gives `dh + hd = id`, including degree zero because `C^{-1}=0`. Verdict: correct and elementary after expansion.
- Step 3: checked against Tag 01XS (lines 62--69); the only allowed subset is the full index set in degree `n`, so the stated cohomology follows. Verdict: elementary and sufficient.
- Small cases checked: `n=1` and `n=2`, with `N_e` empty, singleton proper, and full; the differential and the contraction give the stated groups over a field and over the zero ring.
- Duplicate/Mathlib audit: searched the DAG and blueprint for the item and the exponent-vector simplex calculation; no duplicate or blueprint node was found. The recorded leanfinder, loogle, grep, and unavailable leansearch searches were matched against `searches.jsonl`; no Mathlib declaration gives this exact statement.

Changes made in this second reading: replaced the stale local-source caveat with the online Tag 01XS verification and recorded the per-step and B1--B7 checks. No mathematical node or proof step required alteration.
