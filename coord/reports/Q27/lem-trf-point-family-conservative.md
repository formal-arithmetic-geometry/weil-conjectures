## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-point-family-conservative.json`: item, split into four proof steps; no new nodes and hence no Mathlib leaves.
- `citations.json`: exact quotations for the three cited node statements.

Attachments: none.

WANTED: none.

The Lean source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` has no declaration tagged `(blueprint: lem-trf-point-family-conservative)` and no declaration stating this item, so this is a split rather than an attachment. The DAG search found no duplicate criterion node; `lem-trf-site-point-reconstruction-sets` and `lem-trf-site-point-fibre` concern explicit stalk-colimit reconstruction under additional smallness/finite-limit hypotheses and do not state this arbitrary-site conservativity implication. The blueprint search found no separate node stating the criterion. The required Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch, each with a second phrasing) are recorded in `searches.jsonl`; they found only general separated-sheaf or balanced-category results, not this arbitrary-site section criterion, so `mathlib_match` remains null.

No statement or hypothesis was changed. The imported statement is the sufficient section-separation implication from Stacks Tag 00YM; its title says “characterizes,” but the written conclusion requires only the converse direction and I preserved that exact strength. No source error was found.

## Not duplicates

No new node was created, so there are no new-node duplicate pairs. The existing reconstruction nodes named above are strictly different: they construct a stalk as a filtered colimit (and impose small finite-limit hypotheses), whereas this item proves joint reflection from a separation condition for arbitrary sites.

## Review by Q27

I read `literature/stacks-project/sites.tex` at Tags 00YK and 00YM, including the full converse proof of `lemma-enough`, and checked the item statement against that text. The item’s point data, $u_i(U)=p_i^{-1}(h_U^\#)$, stalk-colimit notation, quantified section-separation hypothesis, and conclusion about all sheaf morphisms with bijective inverse images agree with the cited Stacks criterion; no site-size or finite-limit hypothesis was added.

Step 1 uses only the item’s own stalk identification and separation hypothesis: unequal sections whose images under $a$ agree would be separated in one stalk, but their images there are equal, so every section map is injective. Step 2 uses the adjunction clause of `def-trf-geometric-morphism` (quoted in `citations.json`) to preserve the pushout $\mathcal G\amalg_{\mathcal F}\mathcal G$; bijectivity of each inverse-image map makes the two pushout coprojections equal after every $p_i^{-1}$. Applying the item’s section-separation condition to a hypothetical unequal pair of coprojection sections gives the contradiction. Step 3 uses exactly the statement of `lem-galois-epi-iff-cokernel-pair`, which identifies epimorphisms with equality of the two pushout coprojections. Step 4 uses exactly the statement of `lem-weil-pbc-sheaf-sets-mono-epi-iso` to conclude that the already established monomorphism and epimorphism is an isomorphism.

I checked the hypotheses at each use: the pushout is the sheaf pushout in the category in which $a$ lives; every $p_i^{-1}$ is a left adjoint by the geometric-morphism datum; the cokernel-pair criterion is applied to this same pushout; and the final balancedness result is for sheaves of sets. The empty family is harmless (the section-separation premise then forces every sheaf’s sections to have no unequal pair), and the identity morphism and a one-object site satisfy the argument directly. No long proof step hides a separate lemma, no SGA source is cited, and no coefficient category is changed.
