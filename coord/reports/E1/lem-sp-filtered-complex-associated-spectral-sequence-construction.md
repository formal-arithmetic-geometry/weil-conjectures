# Stage 1 report

1. Files written: the item node `lem-sp-filtered-complex-associated-spectral-sequence-construction` (statement, no new nodes), and `citations.json`. The item is marked `split`; it has no Mathlib leaf.
2. Attachments: none.
3. WANTED: none.
4. I found no Lean declaration carrying the blueprint tag or the filtered-complex construction. I read the source proof of Stacks Homology Definition 12.18.1, Remark 12.18.2, and Lemma 12.19.2 (Tag 012K) in `/home/ubuntu/c1-stacks-review/homology.tex`; the imported statement agrees with the source. The required Mathlib searches were run with `msearch.py`: LeanFinder returned differential-object infrastructure but no filtered spectral sequence, Loogle returned no hits, grep returned no hits in `Mathlib/Algebra/Homology`, and LeanSearch was unavailable. No new node was needed because the proof is the direct construction and calculation in the source.

## Review by E1

I checked the item statement against the Tag 012K construction, including the shifted component $F^{p+1}K^{p+1+q}$, the inclusion into $F^pK^{p+1+q}$, page differential bidegree $(r,1-r)$, and the $E_0$ graded quotient. Step 1 uses the abelian-category and filtration definitions to verify that the differential preserves each filtered subcomplex and squares to zero. Step 2 uses those same hypotheses and the spectral-sequence definition to verify that the filtration inclusions form an injective differential-object morphism and invoke the self-map construction from Remark 12.18.2. Step 3 computes $T^rS=[r,1-r]$ and the page-zero cokernel, then identifies that cokernel with the graded piece using the filtration definition. I checked the hypotheses at every step and tested the quotient calculation on a zero differential and on a two-term complex; the formulas reduce to the expected graded complex in both cases. Every cited-node quote in `citations.json` was copied from the cited node statement.

## Second reading by E1

- Item statement: checked hypothesis by hypothesis against Stacks Homology Definition 12.18.1, Remark 12.18.2, and Lemma 12.19.2 (Tag 012K); the shifted component, inclusion, page bidegree, and page-zero graded quotient agree.
- Step 1: checked against the filtered-complex definition and [def-sp-filtration]; preservation by the differential and $d^2=0$ are elementary.
- Step 2: checked the componentwise inclusion and commutation with $d$ against the proof of Tag 012K at homology.tex lines 6065--6082 and the self-map construction of Remark 12.18.2; monomorphism and shift bidegree are the stated construction facts.
- Step 3: checked $T^rS=[r,1-r]$ and the cokernel calculation against Tag 012K lines 6083--6103; the quotient is $F^pK^{p+q}/F^{p+1}K^{p+q}$ and the induced differential is correct.
- New nodes: none; no new node was required, and the existing cited definitions [def-sp-abelian], [def-sp-filtration], and [def-sp-spectral-sequence] were checked for the facts used by the steps.
- Edge cases: the zero complex gives zero pages; a zero differential gives the graded quotient with zero differential; a two-term complex gives the expected degree shift; $r=0$ and $r=1$ give the stated initial bidegrees.
- Changes: none. The split is mathematically consistent with Tag 012K, and the delivery preflight and citation checks pass.
