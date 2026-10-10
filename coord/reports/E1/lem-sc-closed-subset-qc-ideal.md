1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-closed-subset-qc-ideal.json`: item split in one step; no new nodes; Mathlib remains no match.

2. Attachments:

- No Lean declaration attachment. The item has no sorry-free declaration in `WeilConjectures`.

3. WANTED:

- None. The cited Stacks source is present in `literature/stacks-project/schemes.tex`.

4. What was checked and corrected:

- The source and item were checked against Stacks Schemes Lemma 01J3. The whole DAG was searched for the construction before adding anything; `lem-weil-pbc-reduced-induced-closed-subscheme` already states the stronger result, including quasi-coherence and the affine identity $V(I)=T\\cap U$, so no duplicate node was created.
- The single proof step applies that existing node with $X=Y$ and $T=Z$. Its cited statement explicitly supplies the quasi-coherent ideal and affine zero loci; the passage from affine zero loci to the stalk vanishing set is the standard affine-local interpretation already built into the construction. The citation quote in `citations.json` is copied verbatim from the cited node's statement.
- I verified the item hypotheses (scheme and closed subset), retained the original statement and statement dependencies, filled the split metadata, and recorded the existing Mathlib searches. A small sanity check is the affine case: for $Y=\\operatorname{Spec}R$ and $Z=V(I)$, the cited node gives the radical ideal $I$ and hence the expected stalk vanishing locus.

5. What could not be finished:

- Nothing. No Lean code or `sorry` was introduced.

## Review by E1

I read the item node, its chapter and unit records, the Stacks `schemes.tex` source at Lemma 01J3, and the existing cited node `lem-weil-pbc-reduced-induced-closed-subscheme` in full. I checked that the cited node's statement really says that the vanishing ideal is quasi-coherent and that on affine opens its radical ideal has zero locus equal to the prescribed closed subset. The sole proof step uses exactly that statement, with $X=Y$ and $T=Z$; its hypotheses match the item, and the affine-to-stalk conclusion is the defining local description of the cited construction. I searched the DAG and blueprint for duplicates, found the existing stronger node, and corrected the item from empty proof/status `unsplit` to a one-step `split` proof with the appropriate source, dependencies, blueprint, and citations. No new node or unsupported fact remains.
