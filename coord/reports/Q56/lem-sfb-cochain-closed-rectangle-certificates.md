# Stage-1 report: lem-sfb-cochain-closed-rectangle-certificates

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cochain-closed-rectangle-certificates.json: item, statement unchanged, four proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-compact-metrizable-second-countable.json: statement, Mathlib leaf; TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetrizableSpace, Mathlib/Topology/Metrizable/Basic.lean:164, with compact-to-Lindelöf instance Mathlib/Topology/Compactness/Lindelof.lean:529.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-countable-clopens.json: statement, Mathlib leaf; TopologicalSpace.Clopens.countable_iff_secondCountable, Mathlib/Topology/ClopenBox.lean:85.
- citations.json: verbatim statement quotations for all four proof-step citations.
- searches.jsonl: actual search-tool output log. The node records preserve the exact queries and logged results used for the two leaves and the item.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, closed rectangles, rectangle certificates, Baire, clopen countability and open normal subgroups found no declaration stating this item. Related integral-model and locally constant cochain arguments do not give its full parameterized certificate statement.

## Wanted literature

WANTED: a published reference for the parameterized algebraic-p-adic closed rectangle certificate assertion, for lem-sfb-cochain-closed-rectangle-certificates. The inherited source explicitly requests this reference. The proof here is marked agent-written; the current blueprint paragraph (3) is the motivation, not a claim that this analytic assertion is proved there. The mathematical ingredients are the available Stacks Baire theorem and verified pinned Mathlib results; no unavailable document is cited as a theorem.

## Audit and changes

The input was statement-only. I read the current blueprint direct-images proof, paragraph (3), the chapter and unit records, and the parent boundary-descent assembly. The task is exactly the parent's countable closed certificate input. It does not claim that continuous algebraic-p-adic functions globally have finite-field image. It needs no cocycle condition and yields closed, potentially non-open parameter sets. No statement dispute or change to hypotheses was necessary. Finite dimensionality and increasingness of the fields are stronger than the topological proof requires; I preserved them.

The elementary coset proof supplies finite indices directly by a finite subcover, rather than a new subgroup-index node. The existing lem-sfb-baire-closed-cover-interior supplies the non-elementary Baire assertion, and lem-weil-pbc-tychonoff-product-quasi-compact supplies compactness of the group power. I initially considered a product-compactness leaf but the Stacks-tag search found the existing one, so no duplicate was written. The two new leaves isolate general topology results already in Mathlib; neither hides the cochain argument or restates the certificate assertion.

The proof has four steps of lengths below 1000 characters each (2699 characters total). No non-elementary step exceeds 2000 characters. It contains no appeal to an unspecified standard lemma, no derived-category identification, and no SGA source. All files were written only in the sandbox. No Lean, compiler, Lake or local DAG-validation command was run.

## Unfinished work

None in the mathematical split. The two new nodes are verified Mathlib leaves and therefore intentionally have no proof steps. The final dry run and push are performed after this report is written.

## Not duplicates

The two new nodes have no Stacks tags; there are no new-node/existing-node same-tag pairs. Whole-DAG statement and declaration searches for second countability, Lindelöf spaces, countable clopens and the two matched declarations found no preexisting nodes for either new leaf. Whole-blueprint searches for countable clopen, second countable, metrizable, Lindelof and countable found no equivalent blueprint statement. The isolated hits concern countable algebraic constructions or clopen quotients, not these general topology implications. The product theorem with Tag 08ZU is reused, as is the Baire theorem with Tag 0CQN; neither was recreated.

## Review by Q56

I checked the item against its explicitly agent-formulated source and its parent's step 3. Reading the actual direct-image paragraph confirmed that it only motivates the analytic input and contains no proof of it; the item's proof_origin therefore remains agent rather than document. I read Stacks topology.tex, theorem-tychonov (Tag 08ZU, line 2446) and lemma-baire-category-locally-compact (Tag 0CQN, line 2044), and opened the statements of both existing cited nodes. The Tychonoff node grants compactness for arbitrary products with the product topology, so it applies to the finite power in step 3. The Baire node grants nonempty interior for a countable closed cover of a nonempty locally compact Hausdorff subspace, not just density of an intersection. I verified all those assumptions for the entire space G^(n+1): the identity tuple witnesses nonemptiness, coordinate separation gives Hausdorffness, and the compact whole space is a compact neighbourhood at every point. No completeness of the algebraic closure is used.

For step 1, I verified that right translations are homeomorphisms, cosets of an open subgroup partition G into opens, and compactness gives finitely many such cosets. Thus the complement of the subgroup is open. The assumed normal-subgroup basis can be translated to separate any two distinct points of the Hausdorff group, which establishes total disconnectedness before the next step invokes it. These are written elementary arguments, not uncited uses of a profinite-group structure theorem.

For step 2, I read Mathlib/Topology/Metrizable/Basic.lean:164–178 and the compact-space Lindelöf instance at Topology/Compactness/Lindelof.lean:529. The automatically named instance returned by Loogle accepts any Lindelöf pseudometrizable space; compact metrizable G meets both hypotheses without an extra theorem beyond these instances. This supports the first new leaf. I also read Mathlib/Topology/ClopenBox.lean:85–100, including the surrounding CompactSpace X variable at line 54, for the second new leaf. This compactness hypothesis is essential and is present in the node; the source additionally requires Hausdorffness and total disconnectedness, both verified for G. The node states the exact equivalence, and step 2 uses its second-countable-to-countable-clopens direction. Every open subgroup is one of those clopen subsets, and for each normal subgroup only finitely many tuples of cosets occur; representatives in G need not themselves range over a countable set. Choosing presentations after counting the subsets avoids incorrectly counting tuples of arbitrary group elements.

For step 3, I checked the preimages E_N use the specified continuous homogeneous function and precisely the assumed closed subfields. Their union is the entire power by the assumed union of fields, even though no field contains the entire image. Baire yields one open patch for each fixed parameter. Taking a basic product in that patch and intersecting the finitely many open normal subgroups inside U_i a_i^(-1) proves the required common-H right-coset rectangle, with the multiplication order matching the item. Step 4 writes the closed parameter set as an arbitrary intersection of closed evaluation preimages, so no invalid projection-closedness argument or openness claim is involved. Nonempty S makes the surviving collection nonempty, and countability permits enumeration with repetitions, including the finite case. Together these steps establish every clause rather than moving clauses into new unsplit tasks.

I tested the statements on the empty space for each new leaf, a singleton or finite G, a singleton S, constant zero z, and n=1. Empty compact spaces satisfy both countability statements. Finite G admits H={1}; constant zero permits the full parameter set. If only finitely many certificates survive, repetition supplies all positive indices. The proof uses neither a primitive nor dz=0, so the n=1 and arbitrary noncocycle cases cause no change. Every quoted citation in citations.json was compared verbatim with its node statement; the four proof citations are exactly the four entries of proof_deps. I corrected the surrounding-variable source line for the clopen leaf from 50 to 54 and extended the metrizable source span to the actual end at 178 before delivery. No other statement or hypothesis repair was needed.
