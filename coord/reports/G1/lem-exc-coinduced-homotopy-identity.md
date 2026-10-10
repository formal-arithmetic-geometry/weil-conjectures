1. Files written:

- `dag/nodes/sec-curve-estimates/lem-exc-coinduced-homotopy-identity.json` (item; split; no new nodes).

2. Attachments: none.

3. WANTED: none.

4. Nothing in the item statement was changed. The proof is split into the pointwise expansion of `d^{n-1} h_n`, the pointwise expansion of `h_{n+1} d^n`, and the sign cancellation. I found no matching declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `Comparator` and no existing blueprint node stating this identity. The item remains agent-proven from the direct calculation associated with Stacks Tag 0DVG.

5. What I could not finish: no Lean implementation is required at stage 1.

## Review by G1

I read the item source reference `literature/stacks-project/etale-cohomology.tex`, Tag 0DVG, and checked the imported statement against its displayed definitions. I also read the complete statements of `lem-exc-coinduced-homotopy-continuous` and `lem-exc-coinduced-discrete-embedding`. Step 1 uses exactly the former's assertion that the formula for `h_n` gives a continuous cochain and the latter's stated right-translation action; these are the only cited non-elementary facts. Steps 2 and 3 use only substitution of the differential and cancellation of adjacent alternating terms, so they are marked elementary and cite no hidden lemma. I checked the endpoint signs separately for `n=1` (where `d^0 h_1` contributes the two endpoint terms) and for general `n`; the remaining terms cancel pairwise, leaving `F(g_1,...,g_n)(x)`. I checked the hypotheses `n>=1`, `F in C^n`, and arbitrary `x in G` before concluding equality of cochains. The citation quotes were copied verbatim from the two cited node statements. No new node was needed, and no source or Lean attachment was found.
