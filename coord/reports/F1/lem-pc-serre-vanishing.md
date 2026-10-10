# Stage 1 report: lem-pc-serre-vanishing

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-serre-vanishing.json` — item split into two proof steps; no new child nodes; Mathlib searches recorded.
- `citations.json` — verbatim statement excerpts for every cited node in each step.

## Attachments

The declaration `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist` in `WeilConjectures/AlgebraicGeometry/Cohomology/Serre.lean:418` is not an attachment: its local body is sorry-free, but the transitive sorry map marks dependencies below it as open. The declaration also formalizes the closed-immersion presentation rather than the imported proper-over-a-field statement exactly.

## WANTED

None. The proof follows the available Stacks Project source (Tag 0B5U) and the imported projective-space nodes.

## What I checked and corrected

The source for the item is Stacks, Cohomology of Schemes, Lemma 30.17.1, Tag 0B5U (with the EGA III$_1$, Proposition 2.6.1 reference in the node). The unit route is `sk-thm-picard-serre-b`: reduce to projective space using a very-ample tensor power, then use projective-space Serre vanishing on each residue class. I checked the imported node against the source and the slopmaster2 docstring around lines 504–517 and 519–555. The imported proof had the right route but understated the tensor/coherence and projection-formula details, and its statement dependencies omitted the definition of ampleness. I added `def-sc-ample`, the missing proof dependencies for invertibility and coherence, and changed the cohomology equality to a canonical isomorphism.

## Review by F1

Step 1 uses `def-sc-ample` for the positive tensor power and projective closed immersion; its statement explicitly says that an ample module has a positive very-ample tensor power. It uses `def-sc-invertible-module` and `pqf-def-coherent` for the local rank-one and coherent-module meanings needed to preserve coherence after tensoring by a tensor power. It uses `lem-pc-closed-immersion-coherent-cohomology`, whose statement supplies coherence of the pushforward, the cohomology isomorphism, and the projection-formula isomorphism. The hypotheses checked are that $X$ is proper over the field, $\mathcal L$ is ample and invertible, and $\mathcal F$ is coherent; these are exactly the item hypotheses.

Step 2 uses `def-pc-projective-space-twist` for the twisting sheaf and its tensor interpretation, and `lem-pc-projective-space-serre-vanishing` for eventual vanishing on projective space. The finite set of residues $0\le r<m$ permits a maximum of the bounds $t_r$; Euclidean division of $n\ge mT$ gives $n=mt+r$ with $t\ge T$, so the isomorphism from step 1 transfers vanishing to the original cohomology. This arithmetic and the finite maximum are elementary once the cited bounds are available.

I searched the whole DAG and blueprint for duplicate statements and for the Stacks tag before retaining the existing four dependencies; no new node was needed. The Mathlib searches were run through `msearch.py`: LeanFinder returned only unrelated localization/derived-category declarations, Loogle returned no matching declaration and an unknown project-specific identifier, the Mathlib grep returned no hits, and LeanSearch was unavailable with an internal-server error. A small edge case check is $m=1$, where the residue set has only $r=0$ and the argument reduces directly to projective-space vanishing; for $n=0$, the same division argument gives $t=0$ and the chosen bound handles the conclusion.

## Second reading by F1

- Statement: checked against Stacks Tag 0B5U, Lemma 30.17.1, including the field specialization of its Noetherian-base hypotheses; proper, ample invertible, coherent, and all quantifiers agree.
- Step 1: checked the very-ample-power reduction against `def-sc-ample`; checked coherence and the locally free rank-one tensor argument against `def-sc-invertible-module` and `pqf-def-coherent`; checked the closed-immersion cohomology, projection formula, and locally Noetherian hypotheses against `lem-pc-closed-immersion-coherent-cohomology`. Verdict: sound.
- Step 2: checked the twist notation against `def-pc-projective-space-twist`, eventual projective-space vanishing against `lem-pc-projective-space-serre-vanishing`, and the finite residue/max argument directly. Verdict: sound, including $m=1$, empty/zero sheaves, and $n=0$.
- New nodes: none; no duplicate, restatement, or Mathlib leaf was introduced. Existing dependency statements were read in full and their cited quotations match `citations.json`.
- Confirmed the imported item's blueprint metadata remains `from = null`, as required by B9; no metadata change was made.
- No mathematical statement or proof step required repair; the delivery dry run passes with the imported-item metadata intact.

