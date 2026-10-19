Files written:

- `lem-trf-curve-section-degree-positivity.json` — statement, split proof, no new nodes; Mathlib searches found no match.
- `citations.json` — verbatim citations for every proof-step dependency.

Attachments:

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-conjectures-slopmaster2/WeilConjectures` by the item id, the Stacks tag 0B40, and the degree/section terminology; no sorry-free declaration states this item exactly.

WANTED:

None. The proof follows the local Stacks copy `literature/stacks-project/varieties.tex`.

What was checked or corrected:

The imported statement agrees with Stacks Tag 0B40 for a field, proper integral one-dimensional scheme, invertible module, and nonzero section. I kept the topological Krull dimension wording and made the dimension-convention transfer explicit in the proof through `lem-pc-scheme-dimension-local-rings` and `def-pc-dimension`. No statement correction was needed.

## Review by Q77

I read the item node, the chapter `dag/chapters/sec-trace-formula.json`, the unit `dag/units/sk-i-curve-zero.json`, the blueprint ancestor `lem-trf-local-term-locality`, and the source passage at `literature/stacks-project/varieties.tex` lines 9934–9995. The source proves the nonnegative and strict degree clauses by identifying a nonzero section with the canonical section of an effective Cartier divisor and using the effective-divisor degree formula. I also read the complete statements of every cited node.

Step 1 uses `def-pc-zero-scheme` for the construction of $D$, `lem-pc-nonzero-section-integral-cartier` for effectiveness on an integral scheme, and `def-weil-pbc-ample-invertible-module` for the meaning of the nonvanishing locus; the vanishing hypothesis makes $D$ nonempty. Step 2 uses `lem-pc-zero-scheme-divisor-iso`, whose final sentence gives $\mathcal L\cong\mathcal O_C(Z(s))$, and `def-pc-degree-line-bundle` to justify invariance of degree under this isomorphism through Euler characteristic. Step 3 uses `lem-pc-scheme-dimension-local-rings` to match the item’s topological dimension with the local-ring dimension in `def-pc-dimension`, then applies the effective-divisor clause of `lem-pc-degree-base-change`, which states both finite-dimensionality and $\deg\mathcal O_C(D)=\dim_k\Gamma(D,\mathcal O_D)$. Step 4 uses `lem-pc-cartier-divisor-finite-over-field` for affineness and finiteness; a nonempty affine scheme has a nonzero coordinate ring, so its finite-dimensional coordinate algebra has positive dimension. I checked empty and nonempty divisors, the zero section versus a section with a zero, and the degree-zero case $\mathcal O_C$ on a proper integral curve. All citations are verbatim in `citations.json`; the proof dependency union matches the step uses. The Mathlib searches were rerun with two semantic phrasings and recorded as no matches.

What could not be finished:

Nothing.
