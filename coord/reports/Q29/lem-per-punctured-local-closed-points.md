# Stage-1 delivery: lem-per-punctured-local-closed-points

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-punctured-local-closed-points.json`: item, statement unchanged, split in six steps; no exact Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-local-domain-open-infinite.json`: one new statement-only node, Stacks 02IG, unsplit; no exact Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `citations.json`: verbatim statement quotations for every step citation.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item tag and punctured/Jacobson/closed-point terminology found no project declaration proving the item. Mathlib's Jacobson-space characterization assumes the missing Jacobson property; the prime-chain insertion theorem is an ingredient, not a one-line proof of infinitude of arbitrary nonempty opens. No upstream master sorry is treated as proved.

## WANTED

None. The source files are available in `literature/stacks-project/`.

## Corrections and route

The item statement is correct and unchanged. Morphisms 02J6(4) refers to Properties 02IM(1); I expanded the latter's direct proof. Instead of making a new Jacobson-space lemma equivalent to the item, I choose a point closed in W and use the same quotient-domain contradiction as 02IM. This expands the closed-point choice inside Topology 02I7 using existing 005E and compactness leaves. No claim of closedness in Spec A is made. The new node is the strictly smaller algebraic input 02IG, not a relabeling of the item or one of its clauses.

The current `main-20261015` blueprint `lem-per-artin-gabber-affine-curve.md`, its DAG step 1, the unit `sk-p-dl-a1-perverse`, and its chapter were read. This is a local-algebra tool below the potential-dualizing/complete-local-connectedness branch, preserving that route. The item is not the unit's key node, so no unit record changes. All cited off-unit statements are already Mathlib leaves; no additional tool-use declaration is needed. No SGA source is used.

## Not duplicates

Whole-DAG source/tag and statement searches for 02IG, `Noetherian-local-domain-dim-2-infinite-opens`, infinite opens, finite nonempty opens and generic open points found no existing statement of 02IG. `tools/blueprint_refs.py search` was run for 02IG, infinite open, local domain, punctured, Jacobson, and nonempty open subset; none states the child or the item. The child has no same-tag pair in the existing DAG. The existing closed-point and compactness nodes are reused rather than duplicated.

## Review by Q29

I read Properties `lemma-complement-closed-point-Jacobson` (02IM), its direct proof of (1), Morphisms `lemma-ubiquity-Jacobson-schemes` (02J6), Topology the remark after `definition-space-jacobson` (005U), `lemma-non-jacobson-Noetherian-characterize` (02I7), `lemma-quasi-compact-closed-point` (005E), and `lemma-Noetherian-quasi-compact` (04ZA). For the one new node I read Algebra `lemma-Noetherian-local-domain-dim-2-infinite-opens` (02IG), including its parameter/dimension proof. I also read the quotient-Noetherian argument in `lemma-Noetherian-permanence` and Mathlib `PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal` and `exist_mem_one_of_mem_two` in LTSeries.lean:32–75 to rule out a direct match. The source of 02IG requires both locality and the domain condition, and its dimension bound is essential; all are retained in the child. Its statement explicitly defines local and integral domain and cites the existing topological dimension definition. No new node contains a proof.

For step 1 I opened the full statements of the spectrum-closures, radical-zero-locus and Noetherian-ring nodes: they give exactly V(I) as closed sets, radical as intersection of containing primes, and finite generation of every ideal. I wrote the ascending-union argument, and the closure-inclusion argument gives T0 without an uncited sobriety theorem. Step 2's compact-subsets node applies to the scheme X, whose topological descending-chain condition was proved, and gives compactness of W. The 005E leaf explicitly quantifies over arbitrary compact Kolmogorov topological spaces: applying it to all of W gives a point closed in W; no scheme structure on W is required.

Step 3's maximal-ideal leaf says every prime lies in a maximal ideal, so uniqueness makes m contain every prime. The spectrum closure statement then shows {m} is closed and U is open. The rest is the elementary subspace calculation: a singleton closed in the locally closed W is locally closed in U; taking its closure makes it open in V(p). I checked the key ambient issue: U itself is open in X, so this gives openness in all of V(p), including its closed point, rather than only in its puncture.

In step 4, failure of closedness provides a distinct q in V(p) intersect U. The cited closure formula yields p strictly inside q; q is strictly inside m by step 3. The quotient-local leaf explicitly gives nonzero and the maximal ideal of A/p. Primality gives the domain property by multiplication of residue classes. Noetherianity follows by lifting each ideal and its finite generators; it is not taken from the local-ring definition. Step 5 cites the quotient-homeomorphism leaf, whose statement includes both the image V(p) and the inverse prime map. The closure formula gives a strict length-two chain of irreducible closed subsets in Spec B, so the cited definition of dimension gives at least two. It also carries the open singleton from step 3 to the zero prime. Step 6 uses exactly 02IG, now with every hypothesis verified. The zero prime singleton is nonempty and finite, contradicting its conclusion. The chosen point therefore is closed in U as required.

Small cases checked: a field and an Artinian local ring have empty puncture, so there is no nonempty W; a DVR has a one-point puncture closed in that puncture, and no intermediate q for the contradictory branch; in k[x,y]_(x,y), p=0 is not locally closed in the puncture, while height-one points can be closed there. For the child, dimension-one DVRs have finite nonempty opens, showing why the at-least-two bound cannot be dropped. Reducible/nonreduced A is allowed: the domain argument is applied only to A/p, never to A. I checked B is nonzero because p is proper. No finite-dimension, normality, excellence or catenarity hypothesis is silently imposed.

I checked delivery-errors B–E: self-contained statement-only child, correctly spelled source tag and label, genuine searches with their responses, no duplicate, no item-clause replacement, every substantive input cited by statement rather than proof, all citations quoted verbatim, and no cycle back to the item. Each step is under 2000 characters. The longer elementary steps contain only the explicitly written finite-generator, subspace, or quotient calculations from the cited statements. Two tentative extra topological nodes were removed before delivery because the compactness and 005E leaves already supply their needed content in a few lines. The final split has one new node and no new Mathlib leaves.

## Unfinished work

No missing argument in the item. The statement-only 02IG child remains for a later one-level split, as required.
