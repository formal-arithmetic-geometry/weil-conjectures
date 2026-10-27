# Stage-1 report: lem-trf-rank-partition-cartier-charts

## Files written

- dag/nodes/sec-trace-formula/lem-trf-rank-partition-cartier-charts.json: item, statement unchanged, complete five-step assembly proof; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for each of the 14 step/node uses.
- searches.jsonl: actual Mathlib queries run by the required search command; prepare.py: sandbox-only JSON preparation helper.

No new nodes; no Mathlib leaves. No unit or chapter record changed: this created node is not a unit key statement.

## Attachments

None. Searched the project source for the item tag and the notions. The existing `AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures` in WeilConjectures/Compactification/BoundaryPreparation.lean:139 proves the two-subset separation tool, not the item's finite partition and Cartier affine-chart assertion, so it is not an attachment for this item. Its existing DAG statement is reused.

## WANTED

None.

## Problems and changes

The imported item has no proof. Its statement is valid without density of U in S: blowing up its entire complement first removes components invisible from U. I retained the statement and all original source/search/created/blueprint data. The proof is marked agent-written because it assembles existing tools, while following flat.tex Tags 0811 and 080Y; all step sources name those places. The current blueprint ancestor lem-trf-local-term-locality proof (1)–(2) was read in literature/blueprint/latest. This node is a lower refinement in the already-existing flattening chain, not a change of the unit route.

The two-open lemma used directly by Stacks 0811 is Tag 080P. I did not create a new node for it or a restatement of a clause of the item. Instead I used the existing, more general, constructible-subset closure-separation node, kept density by the existing Cartier-boundary theorem, and wrote the finite closure argument explicitly. No hypothesis of Noetherianity, separatedness, irreducibility or pre-existing density was added. The typo in 080Y that calls the boundary support X rather than S is not used.

Mathlib searches: two different LeanFinder phrasings, Loogle, source grep and LeanSearch all ran and their actual results were read. They give affine refinements, coproduct clopens, idempotents, and compact Hausdorff totally disconnected clopen partition results. `exists_clopen_partition_of_clopen_cover` was read at Mathlib/Topology/Separation/Profinite.lean:147; its Hausdorff/totally disconnected hypotheses do not hold for general scheme spaces and it does not construct blowups or Cartier boundaries. No result states this item. Original recorded searches were retained, with the new logged searches appended.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for clopen, 080P, and affine cover were run; the existing boundary and separation statements were read and reused rather than duplicated.

## Review by Q131

I read the whole B–E return checklist, the stage-1 brief, the three-level route rule, the chapter and unit records, GOAL.md, flat.tex Tag 0811 (lemma-flatten-module-pre, proof's rank separation and Cartier reduction), Tag 080Y (remark-successive-blowups, boundary and composition paragraphs), and divisors.tex Tags 080P, 01WS and 07ZU. I also read the current blueprint Cartier-boundary node and locality ancestor. There are no new-node sources to review.

For step 1 I opened the statements of lemma-nagata-qc-open-complement-ideal-exists, det-nagata-boundary-divisor-cartier, lemma-nagata-admissible-blowup-over-open, def-weil-constructible-subset, and lem-trf-module-admissible-blowup-calculus. Respectively they supply exactly the finite-type ideal, its principalization and density, the isomorphism over U, the retrocompact-open definition, and preservation of qcqs. S is qcqs and U is quasi-compact as required. A clopen subset of U is retrocompact because its intersection with any quasi-compact open is closed in that open; this verifies constructibility, not merely local closedness.

For step 2 I read lemma-nagata-separate-constructible-closed together with its defining datum def-nagata-separate-constructible-closed, and also read its current blueprint_update and the live Lean signature in BoundaryPreparation.lean:139. Our clopen pieces are closed with quasi-compact complements, so both the stored constructible version and current complement version apply. I read the over-open, calculus and composition node statements again: the induction retains the open as U and the ambient as qcqs, and composition gives one admissible blowup. The proof does not assume inverse image commutes with closure: it uses only closure of inverse image being contained in inverse image of closure, and writes the argument. This is a finite induction over pairs, with the empty list as base, and it preserves every previous separation. No use is made of an uncited stronger partition lemma.

For step 3 I checked the further-blowup clause of the boundary node, which explicitly guarantees the extended ideal is still invertible, has the prescribed support, and has scheme-theoretically dense complement. I read def-nagata-invertible-ideal and def-nagata-effective-cartier-ideal. Rank-one freeness alone is not treated as regularity: the ideal inclusion composed with a free generator is injective, which is the written argument that multiplication by its image is injective.

Step 4 cites no theorem because it proves the needed topology directly: the density injection excludes a nonempty disjoint open using the nonzero local ring at any scheme point; finite union commutes with closure; pairwise disjoint closed covering subsets are clopen; and intersection with the preserved open recovers exactly the original closed piece. Empty U is handled by choosing the zero ideal and using the same density conclusion to force an empty blowup, not by assuming a nonempty ambient or surjectivity of a blowup. With empty index set the input partition forces U empty. With empty pieces their closures remain empty. With one nonempty piece no separating blowup is needed. If U=S, its unit boundary ideal is already principal with generator 1; the construction still works.

For step 5 I read def-pc-scheme and def-weil-affine-spectrum. The affine neighbourhood refinement is within both a generator neighbourhood and a clopen piece. Multiplication remains injective after restriction and after taking sections. The zero set is V(h), so its complement is D(h). Quasi-compactness selects finitely many such opens. The local equations are explicitly restrictions of the same global ideal; no gluing of unrelated equations is asserted. This is a routine refinement of an existing local trivialization, not a hidden Cartier comparison lemma.

I checked C1/C4 for every node use, recorded verbatim quotes, and checked that the reused proof dependencies do not reach this item. I checked B1–B10 (no new nodes, no fabricated searches), C1–C8 (all non-elementary tools stated, no proof-only extra conclusions), D1–D5 (the proof carries the finite induction and assembly), and E1–E7 (qcqs rather than Noetherian/separated assumptions, empty and nilpotent cases, no unjustified equality of closures). All steps are below 2000 characters. Generic off-unit Nagata tools are declared in split_report.tool_uses; they do not replace any trace-formula unit step. Nothing mathematical remains unfinished.
