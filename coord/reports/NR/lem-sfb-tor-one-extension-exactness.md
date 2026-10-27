# Stage-1 split: lem-sfb-tor-one-extension-exactness

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-tor-one-extension-exactness.json`: statement item, now split in four steps; not a Mathlib leaf.
- `citations.json`: six verbatim statement citations, covering every use in all four steps.
- `report.md`: this report. `searches.jsonl` is the unmodified output log of the required search wrapper.

New nodes: 0. New Mathlib leaves: 0. No Lean, compiler, Lake, repository writes, or direct git commands were used.

## Attachments

None. I searched `lean/WeilConjectures/` for the item ID and Tor/exactness terminology and read `WeilConjectures/AlgebraicGeometry/TorLongExactFirstVariable.lean`, especially `CategoryTheory.tor_long_exact_first_variable` at line 252. Its conclusion starts at Tor-one of the middle module followed by Tor-one of the quotient and a connecting map. It does not assert exactness at Tor-one of the middle module, which is this item. Its private compatible-resolution construction is an ingredient, not an attachment of the item. The existing node `lem-weil-pbc-free-resolution-ses-split` already records the closed declaration `Module.exists_free_resolution_ses_split`; no attachment record needs changing.

## WANTED

None.

## Corrections and choices

The original statement is correct and unchanged. Its source is Stacks Tag 00M0, with the module arguments exchanged. I give the first-variable proof directly using the existing compatible free resolutions, so no symmetry identification is needed. The inherited `source` and `blueprint.from` records are preserved. The ancestor command prints null for this new-target route; there is no invented blueprint ancestor. The supporting place is already specified in the inherited record.

The existing `lem-weil-pbc-tor-long-exact-first-variable` has the same Stacks source but omits the preceding term needed here, so citing its statement alone would be insufficient. Rather than create a stronger long-exact-Tor node that simply includes the item, the proof assembles existing resolution and homology facts. Blueprint searches `Tor_1` and `00M0` returned no matching imported blueprint node; the broader Tor search and DAG keyword/tag search were also inspected for the relevant existing ingredients.

All inherited searches are retained. The required wrapper was run for this item with LeanSearch, two LeanFinder phrasings, Loogle, and three grep searches. The general homological-functor and snake-lemma hits are ingredients, not one-line specializations to the specified Tor maps. The flat tensor exactness hits impose flatness and do not imply the item. I read the local Mathlib `CategoryTheory/Monoidal/Tor.lean`: it defines Tor and Tor-prime and gives projective-argument vanishing, but has no exact-segment declaration. The broad grep result was capped and mostly unrelated; its verdict explicitly says it was inconclusive and records the narrower follow-ups. Each appended search record has the exact tool, query, and subdirectory from `searches.jsonl`.

## Not duplicates

No new nodes were created. The existing resolution, homology, and Tor-map nodes are reused unchanged. In particular no new clause of this item or generalized Tor exact-sequence restatement was introduced.

## Review by NR

I read the stage-1 brief, the three levels of the SETUP route contract, GOAL, the item's chapter and unit, and both copies of delivery-errors B through E. The unit's stability route is preserved: this is its previously requested auxiliary module-theoretic input, not a replacement of a geometric step.

For the item I read Stacks `algebra.tex`, Tag 00M0 (`lemma-long-exact-sequence-tor`) and its reference back to the Ext argument. I also read the free-resolution construction in Tag 065P (`lemma-reverse-long-exact-seq-ext`), the Tor definition and Tag 00LZ (`lemma-tor-welldefined`) with the following functoriality paragraph, and `homology.tex`, Tag 0117 (`lemma-long-exact-sequence-cochain`). The tag-to-label entries were checked in `tags/tags`. No SGA source is used. The proof is honestly marked agent-written because it assembles these inputs into the first-variable proof rather than claiming that the printed second-variable proof says this verbatim. There are no new nodes requiring separate source review.

Step 1 uses the statement of `lem-weil-pbc-free-resolution-ses-split`, which I opened in full. It supplies all three free resolutions, both chain maps, both augmentation squares, and all four splitting identities. Its hypothesis is exactly the given short exact sequence over a commutative ring. I do not take any additional choice or construction from its proof.

Step 2 uses those splitting identities from the same cited statement. Tensor composition and additivity are checked on pure tensors. The retained left inverse proves injectivity, the retained right inverse proves surjectivity, and the retained sum identity proves kernel equals image explicitly. Thus tensoring the resolution sequence requires no flatness of M. This is the one elementary step, not a separate node and not an uncited appeal to exactness of tensor products.

Step 3 uses `lem-weil-pbc-ring-modules-grothendieck-abelian` for the abelian module category and `lem-weil-pbc-complex-ses-homology-long-exact` for exactness at the middle cohomology object. I read both statements. The latter is stated for cochain complexes, so I explicitly reindex the chain complexes into nonpositive integer degrees, extend by zero, and apply it at degree -1. The displayed kernel/quotient formula checks that this really is first homology and that the maps are the required homology maps. This corrects the potential chain/cochain mismatch rather than assuming the citation covers a different indexing convention.

Step 4 cites `def-weil-pbc-tor-modules` for the actual resolution-computation isomorphisms and clause (1) of `lem-weil-pbc-tor-map-via-resolution-lift` for both map-identification equations. Both statements were opened and quoted in `citations.json`. The resolutions are free, hence allowed by the definition's explicit “projective (for instance free)” wording, and the lift hypothesis holds by step 1's augmentation squares. The proof writes an element preimage under the first Tor map and separately checks the reverse inclusion by the zero composite and injectivity of the last isomorphism. No unspecified “transport” or connecting-map naturality is left to the reader.

For B: all objects and hypotheses remain self-contained in the item; no new notions or definitions were introduced, TeX is escaped once, and searches and blueprint metadata are retained. For C: each non-elementary fact is one of the statements just checked; no node proof is used as an interface. The horseshoe node is an existing closed tool, and its off-unit use is explicitly described in `split_report.tool_uses`; the other tools are existing Mathlib leaves. No new backward dependencies are introduced into the cited nodes. For D: the four steps contain the actual construction, tensor calculation, homology application, and identification, with no new node restating the conclusion. For E: no flatness, finiteness, Noetherianity, or bounded resolution length enters any step.

I checked zero ring and zero-module cases, split sequences with arbitrary nonflat M, and the nonsplit sequence Z --2--> Z --> Z/2 with M=Z/2. In the last example both middle and first Tor terms vanish while the last Tor term is nonzero, which confirms that neither endpoint injectivity nor surjectivity has accidentally been asserted. For a nonzero middle Tor term, take the split sequence Z/2 --> (Z/2)^2 --> Z/2 over Z with M=Z/2: the first-Tor maps are inclusion and projection, with exactly the stated image/kernel equality. All four proof steps are under 900 characters; no step crosses the 2000-character long-step threshold or hides a new comparison lemma.

## Unfinished work

None in this stage-1 split. The server dry run and delivery are the remaining validation actions; their outcomes are recorded below when complete.
