# Q100: lem-trf-proj-localized-graded-comparison

## Files written

- dag/nodes/sec-trace-formula/lem-trf-proj-localized-graded-comparison.json: item, statement; six proof steps, unchanged statement, status split. Mathlib verdict: no match for the full comparison.
- citations.json: exact statement excerpts for every node used in every proof step.
- No new nodes, Mathlib leaves, unit changes, or Lean files.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for invertible section rings, localized graded comparisons, Proj comparisons and pulled-back twists. The section-ring definitions, twist charts and scalar fraction-relation theorems do not state this item's comparison family. Existing upstream declarations with sorry are not treated as attachments.

## WANTED

None. All sources used are present in literature/stacks-project/.

## What was wrong or missing

The imported item had no proof. Its statement is retained: it is the nonnegative-degree part of the comparison in Stacks 01NK, with the canonical scheme morphism already fixed. There is no need to assume degree-one generation or invertibility of O_P(m), and neither is inserted. The proof now constructs the maps from fractions instead of moving the comparison into a new clause-sized node.

Read the chapter and unit records, SETUP's three levels, GOAL.md, the worker and stage-1 contracts, and delivery-errors B through E in full. This is a descendant algebraic tool within the existing Proj/ampleness/descent chain, not the key trace-locality node. The inherited blueprint ancestor and via list are retained. Blueprint searches for graded comparison, 01NK, localization and twisting found no blueprint node stating the item. The broad localization/twisting hits concern different assertions. The current ancestor text contains the local-term theorem; the detailed Proj comparison is the existing descendant route recorded in from.place, rather than a literal clause in that theorem.

## Searches and reuse

The item's inherited searches were retained. Actual searches this session are in searches.jsonl and appended verbatim by tool/query to mathlib_searches. They include LeanFinder twice with different formulations, LeanSearch, Loogle, and the required Mathlib grep. All services answered. Read Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:440-460: fromOfGlobalSections supplies a scheme morphism from a map into ordinary functions. awayToSection and awayMap supply structure-sheaf/degree-zero comparisons, not maps from arbitrary twists to powers of an arbitrary line bundle. Neither semantic phrasing found the full assertion.

Searched DAG titles and statements for graded localization, twist charts, module-map gluing, basis morphisms, localization universal properties and pullback adjunctions, and searched the blueprint with tools/blueprint_refs.py. Opened the relevant node statements before choosing citations. In particular lem-sc-p1-invertible-section-localization requires qcqs and quasi-coherence and is not used: T in the item is arbitrary. The field/polynomial-specific lem-sc-proj-graded-chart-comparison is also not used. No new lemma was needed.

## Not duplicates

No new nodes. Existing arbitrary-module Proj restriction, basis morphism and tensor pullback adjunction nodes supply the non-elementary facts directly.

## Review by Q100

I read Stacks constructions.tex, lemma-invertible-map-into-proj (01NK), in full, including its localization uniqueness, Laurent-polynomial local construction and final generated-open clause. I also read lemma-converse-construction (01N8), its local division construction and overlap calculation, and lemma-proj-sheaves (01M7). For extension and transposition I read sheaves.tex, lemma-restrict-basis-equivalence (009O), the module version lemma-restrict-basis-equivalence-modules (009U), and lemma-adjoint-pullback-pushforward-modules (0096). I checked the tag-to-label mapping in tags/tags. The source proof's claim of a localized extension has been expanded into fractions, and its local gluing has been expressed using maps to r_* followed by the tensor adjunction. This avoids asserting that sections of a pullback over a nonaffine open are a tensor product of global sections.

Step 1 uses def-weil-pbc-proj-twisting-sheaf exactly for all degree-m fraction sections, and def-sc-section-generating-locus exactly for a generating section's invertible multiplication. Trivialize L locally only to see the powers of a generating section act invertibly; no global frame is chosen. The explicit equality f^k(f^{q'}b-f^qb')=0 is taken in the localization before applying psi. Cancelling is performed only on line-bundle multiplication maps, never in A. Thus zero divisors and torsion do not invalidate it. This is the elementary representative calculation, not an extra localization lemma.

Step 2 uses the multiplication specified by def-sc-invertible-section-ring. I checked both the common-denominator addition formula and the scalar fraction formula supplied in the item's hypothesis. The latter proves linearity over A_(f); it does not presume the desired sheaf comparison.

Step 3 uses clause (a) of lem-weil-pbc-proj-graded-module-sheaf-exists for the relation g^k=af and restriction b/f^q to a^qb/g^(kq). Its statement allows an arbitrary graded module, so A(m), any commutative graded A, and every standard-open inclusion are allowed. The displayed psi(g)^k=psi(a)psi(f) proves compatibility explicitly, including different positive degrees and empty intersections. I checked that this node supplies the relation and restriction, not merely a definition of the sheaf.

Step 4 uses def-pc-proj for standard opens and their graded-localization charts, lem-weil-pbc-sheaf-morphism-on-basis for compatible maps of the underlying sheaves, and lem-pc-module-pullback-adjunction for the actual direct-image sheaf and Hom bijection. Both inputs to the basis theorem are sheaves; its overly general presheaf wording is not needed. Scalar linearity is checked on the basis and then glued. The tensor definition in def-pc-module-pullback gives the normalized transpose t tensor u to t alpha(u). The standard opens are a basis because complements of homogeneous vanishing sets are unions of them. Nothing requires r's preimage opens to form a basis of U: extension occurs on P with target r_*L^m.

Step 5 uses the twist definition's b/1 global-section description, section-ring tensor multiplication, and the actual sheaf tensor/pullback definitions. I checked the equality on two fraction generators, then on scalar multiples and sums of these local generators. Pulled-back fraction germs generate because the inverse image is generated locally by source sections and source standard opens are a basis. Thus the tensor multiplication equation is a sheaf-map equation, not merely an equation on global sections. The canonical tensor identification sends the written pure tensors to uv tensor (x tensor y), so there is no unproved compatibility hidden in the word transport. The q=0 specialization gives global homogeneous sections, and degree zero gives 1 to 1.

Step 6 uses the adjunction's injective Hom bijection, the twist definition's complete chart description and the basis theorem's uniqueness. Another normalized family has the same transpose on every fraction, hence the same sheaf map and the same transpose back. The hypotheses are those already verified in Step 4. This proves uniqueness without assuming any twist is invertible.

The three off-unit statements are declared in split_report.tool_uses: arbitrary Proj module restrictions, sheaf maps from a basis, and tensor pullback adjunction. Each is used as a generic tool with its actual statement; none changes the unit route. Definition citations have no proof-route restriction.

I tested m=0, q=0, m=n=0 in the multiplication equation, an empty T, an empty generating open U, nilpotent f (its nonvanishing open is empty), zero divisors, and rings with no degree-one generators, for example k[x] with degree(x)=2. The latter has vanishing odd-degree chart modules and the formulas remain meaningful; no invertibility claim is made about O_P(1). I checked arbitrary non-qc T: no section-localization theorem requiring qcqs was used. Every non-elementary fact has a node whose statement was read, all citations have verbatim quotes, and all six proof steps are shorter than 2000 characters. There is no new node to audit for elementary restatement, duplicates or source-tag overlap. Nothing was weakened and no statement dispute arose.

## What remains unfinished

No part of this one-level split. The existing dependency nodes retain their own stage states; this delivery claims neither Lean formalization nor completion of their proofs. The required server dry run and delivery are the final validation steps.
