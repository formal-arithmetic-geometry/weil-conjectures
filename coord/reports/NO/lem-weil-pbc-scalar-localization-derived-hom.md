# Worker report: lem-weil-pbc-scalar-localization-derived-hom

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-scalar-localization-derived-hom.json`: item, statement unchanged, split with five proof steps, no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-scalar-localization-underlying-telescope.json`: new statement-only node, no Mathlib match.
- `citations.json`: verbatim citations for every non-elementary node use in every item step.

Attachments: none. I searched the slopmaster2 source for the item id, its blueprint tag, and its scalar-localization/derived-Hom terminology; no sorry-free project declaration states this item exactly.

WANTED: none.

The imported item had an empty proof even though its statement is the abstract telescope calculation used by Bhatt–Scholze Lemma 6.8.12 and Proposition 6.8.14(2). I kept every hypothesis, including the countable-family coproduct condition and the bounded-below condition, and did not add constructibility or essential-surjectivity assumptions. The only new node records the underlying object-level scalar-extension telescope; it is strictly smaller than the Hom isomorphism and carries no proof sketch because it is intentionally unsplit. The existing reviewed node `lem-weil-pbc-sequence-relative-hom-telescope` supplies the Hom calculation from the telescope. The generic derived extension/restriction adjunction is an off-unit categorical tool, declared in `split_report.tool_uses`.

## Not duplicates

`lem-weil-pbc-scalar-localization-underlying-telescope` vs `def-weil-pbc-integral-localization-telescope`: the existing definition is specialized to integral condensed coefficients and multiplication by a uniformizer; the new node is the general sheaf-of-commutative-algebras statement for arbitrary $A,t,R$ and includes the derived restriction object and leg normalization.

`lem-weil-pbc-scalar-localization-underlying-telescope` vs `lem-weil-pbc-integral-localization-complex-model`: the existing lemma concerns strictly bounded-below integral complexes and good truncation models; the new node identifies arbitrary bounded-below objects after generic scalar localization with a telescope and makes no condensed/integral or truncation claim.

`lem-weil-pbc-scalar-localization-derived-hom` vs `lem-weil-pbc-sequence-relative-hom-telescope`: the existing node is a categorical telescope-to-colimit Hom lemma with a distinguished triangle and two explicit coproduct comparisons; this item adds the scalar-extension/restriction adjunction, the localization telescope, bounded-below families, and the fraction formula.

## Review by NO

I read the item node, its chapter `sec-proper-base-change`, and unit `sk-thm-properbasechange`. I also read the complete statements of every node cited by the five proof steps: the generic derived extension/restriction adjunction, exact-functor derived construction, the new scalar-localization telescope node, the reviewed sequence-relative Hom telescope node, and module localization away from a scalar. Step 1 uses exactly the adjunction and exact termwise derived identification those statements provide. Step 2 uses the new node's canonical telescope isomorphism and its normalized $t^{-n}$ legs. Step 3 applies the reviewed telescope lemma with $X_n=L[q]$ and checks both required coproduct comparisons against the item's hypothesis for the two families $L[q]$ and $L[q+1]$; bounded-below $L$ gives their common lower bounds. Step 4 composes the telescope bijection with the derived adjunction and uses the new node's leg normalization to obtain $u\mapsto t^{-n}F(u)$. Step 5 checks the direct-limit transition is multiplication by $t$, then uses the cited fraction relation to identify the colimit with the localized Hom module and preserve identities, composition, shifts, and naturality.

I ran LeanSearch, LeanFinder, Loogle, and Mathlib-source grep searches for the new telescope node, and LeanFinder, Loogle, and grep searches recorded on the item. They found no Mathlib theorem at the required sheaf-derived generality. I checked the Stacks source `derived.tex` at Lemmas `lemma-compute-colimit`, `lemma-colim-hocolim`, `lemma-cohomology-of-hocolim`, and `lemma-commutes-with-countable-sums`, and the Bhatt–Scholze PDF at Lemma 6.8.12 and Proposition 6.8.14(2). All five item proof steps are below the 2000-character long-step threshold and contain no hidden sublemma beyond the cited telescope and adjunction statements. I tested the formula conceptually at $K=0$, $L=0$, $t$ a unit, $t=0$, and identity transitions; the fraction relation and stage maps have the stated behavior in each case.

`lem-weil-pbc-scalar-localization-underlying-telescope` vs `lem-pc-telescope-shift-mono`: the existing node proves monomorphism of the shift-minus-transition map on a coproduct of cochain complexes, while the new node identifies the scalar-extension derived object with the resulting telescope and specifies its inverse-scalar leg maps.

`lem-weil-pbc-scalar-localization-underlying-telescope` vs `lem-weil-pbc-sequence-relative-hom-telescope`: the existing node computes Hom from a telescope after assuming two coproduct comparison isomorphisms; the new node constructs the particular scalar-localization telescope and identifies it with restriction of scalars before any Hom comparison.
