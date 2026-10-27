# Stage-1 delivery: lem-sfb-curve-closed-point-affine-local-model

## 1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-curve-closed-point-affine-local-model.json`: statement item, now split into seven steps. Mathlib verdict: no match for the whole statement. The existing Mathlib leaves supply the affine chart, finite type, localization and elementary dimension comparisons; two existing split dimension theorems supply the remaining non-elementary inputs.
- `citations.json`: 22 entries, one for each use in each numbered step. Each quote is the entire verbatim statement of the cited live node, retaining its hypotheses.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: **0**. New Mathlib leaves: **0**.

## 2. Attachments

None. Searched the upstream project under `lean/WeilConjectures/` for the exact blueprint tag and for curve closed-point dimension, affine localization and stalk terminology. There is no declaration stating this entire item. The smooth-curve statements in `Curve/ClosedPoint.lean` and `Curve/SerreDuality.lean` impose smoothness and do not attach this item, which explicitly needs no smoothness or normality. `DimensionLocallyAlgebraic.lean` covers an existing dimension node, rather than the whole item.

## 3. WANTED

None. All sources used for this split are present in `literature/stacks-project/`.

## 4. Findings and changes

The live item was unsplit and the sandbox contained no previous item or report. The mathematical statement is correct. I added definition references for closed points and germs without changing any hypothesis or conclusion. The imported source refers to the opening sentence of Stacks 0B8Y, whose argument invokes 0A21. I expanded that input through already existing DAG nodes instead of moving any clause into a new node.

I read the chapter and unit records, the three blueprint-level rules, GOAL.md, the worker and stage-1 briefs, and both copies of delivery-errors B--E. I read the current blueprint under `literature/blueprint/latest/`, snapshot main-20261023-1620, including the direct-images proof whose header identifies `det-thm-sf-ctf-stability-direct-images`. Its present proof (3) is a compactification assembly and does not spell out the inherited alteration prerequisite. This work supplies only the local curve input already assigned to this item and does not modify the chapter, unit, or surrounding alteration route. The existing `blueprint.from.node` is null, and the required ancestor command also returned None; I retained that inherited metadata and its detailed place/via chain. Blueprint searches for “affine local model”, “localization stalk”, “stalk localization”, “local dimension”, “dimension locally algebraic”, “0B8Y”, and “0A21” found no blueprint node stating the whole item. I also searched affine-neighbourhood terminology and read the relevant candidate statements.

DAG searches located the existing affine basis, affine-pair finite type, affine point/stalk, Noetherian algebra, spectrum topology, and dimension nodes. In particular, `lem-trf-closed-point-affine-dimension-data` gives an existential chart with additional function-field data, rather than all the scalar-compatible localizations on every affine chart; it was not used to hide the proof. `lem-weil-pbc-closed-point-dimension-local-ring` is a useful affine closed-point theorem but is unnecessary on the selected assembly through the maximal-localization clause of the existing finite-type-domain dimension theorem.

The five new Mathlib queries are recorded exactly in the item and in the search-command log: one LeanSearch, one Loogle, one grep, and two distinct LeanFinder phrasings. They all answered successfully. I read the actual hits: affine stalk localization in AffineScheme.lean, stalk domain instances in FunctionField.lean, the Noetherian stalk instance in Noetherian.lean, residue-field definitions, and `ringKrullDim_stalk_eq_coheight` in Properties.lean. They give constituent facts but not dimension one at a closed point of a general integral curve together with every chart and scalar clause in a one-line specialization. Existing search history in the item was retained, including the earlier unavailable LeanSearch result; it was not reclassified as a negative search.

## 5. Unfinished work

None in this one-level split. The cited existing dimension nodes retain their own stage status; they were not changed or resplit. This delivery writes no Lean and runs no compiler, Lake, or build command.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs to distinguish. All reusable statements are cited in place.

## Review by Q33

I read the item's actual source, varieties.tex, Tag 0B8Y (`lemma-regular-point-on-curve`), especially its opening proof sentence, and 0A21 (`lemma-dimension-locally-algebraic`), parts (2),(3) and their proofs. I checked the supporting sources in schemes.tex: 01IT (`lemma-basis-affine-opens`), 01HV (`lemma-spec-sheaves`) parts (1),(6), and the open-subspace interpretation; in morphisms.tex: 01T2 (`lemma-locally-finite-type-characterize`), (1) implies (2); and in algebra.tex: 00FN (`lemma-Noetherian-permanence`), 00OS (`lemma-dimension-spell-it-out`), and the closed-point discussion 00OU. The tags were checked against `stacks-project/tags/tags`. There are no new node sources to review.

For step 1 I opened the statements of `lem-weil-pbc-affine-opens-basis`, `def-pc-integral-scheme`, `lem-weil-pbc-affine-open-spec-points`, `def-pc-curve`, and `lem-weil-pbc-lft-affine-pairs`. The basis lemma really gives an affine neighbourhood inside any prescribed open. The point-chart lemma gives the canonical map, not just an unnamed affine isomorphism. The affine-pair lemma applies to every affine U, which matters because the finite-type definition alone mentions a covering. Here V is the whole affine Spec k and f(U) lies in V. The point x makes U nonempty, so the integral-scheme definition says exactly that its section ring is a domain.

For step 2 the cited Noetherian finite-type algebra leaf really assumes a Noetherian source ring and concludes ring Noetherianity. I supplied that hypothesis for the field by its two ideals; I did not confuse Noetherian topology of a spectrum with a Noetherian ring.

For step 3 I checked `def-weil-open-immersion` and `lem-weil-pbc-spec-irreducible-closed-subsets-primes`. The first gives a homeomorphism onto U; the second explicitly states closure of {q} equals V(q). Pulling back the closed singleton is legitimate for the canonical continuous map. If q were not maximal, a maximal ideal strictly above it would be a different point in V(q), contradicting that singleton closure. This argument does not use an algebraically closed base or assert that the residue field equals k.

For step 4 I checked the complete statement of `lem-weil-pbc-affine-open-stalk-localization`, in particular clause (c) and its fraction formula, rather than borrowing a construction from its proof. Its hypotheses hold for the fixed arbitrary U. I also read `def-weil-locally-ringed-space-morphism`, `def-weil-pbc-module-stalk`, and `def-weil-pbc-localization-at-prime`. The structural stalk scalar sends c to the germ of the structural section of c, and the localization isomorphism sends c/1 to exactly that germ. The isomorphism therefore respects the specified k-actions. Preservation and reflection of units proves the local assertion for the actual map.

For step 5 the two cited definitions identify the residue fields as the actual quotients by the maximal ideals. I wrote the quotient map and its inverse and checked their ideals, then evaluated the scalar maps on an arbitrary c in k. Thus the residue-field clause follows as an elementary consequence of the constructed local k-isomorphism; there is no uncited separate comparison theorem.

For step 6 I checked the Noetherian-ring and prime-localization definition statements. The proof actually shows every ideal in the localization is the extension of its contraction, by multiplying a fraction by its denominator; the finite generators then give Noetherianity. The equality relation for fractions shows that nonzero denominators in the domain do not create zero divisors, including checking 1 is nonzero. Localness was already supplied by the localization definition. Ideal correspondence, zero products and units explain how the actual isomorphism gives these properties to the stalk. These are short elementary arguments, not new nodes.

For step 7 I read the entire statements of `lem-sc-dimension-locally-algebraic`, `def-pc-integral-scheme`, `def-weil-open-immersion`, `lem-weil-pbc-homeomorphism-krull-dimension`, `lem-weil-pbc-spec-topological-krull-dimension-ring`, and `lem-weil-pbc-finite-type-domain-dimension-trdeg`. The locally algebraic theorem requires irreducibility and locally finite type, both supplied by the curve hypothesis, and requires a nonempty U. The dimension comparisons distinguish ring dimension from topological dimension. The final sentence of the finite-type-domain theorem explicitly covers every maximal ideal, so it really gives the dimension of S_q after step 3 proves maximality. The last prime-chain argument proves dimension invariance under the specific ring isomorphism. I declared the two generic off-unit dimension inputs in `split_report.tool_uses`; neither replaces the alteration unit's route.

I tested the hypotheses on an affine line at a closed point defined by an irreducible polynomial, on a singular integral cusp, and on closed points with nontrivial or inseparable residue extensions. The proof never uses regularity, normality, smoothness, or residue separability, so all are permitted. A generic point of the affine line is excluded by closedness and would have a dimension-zero stalk, confirming why that hypothesis is essential. Dimension-zero schemes, empty schemes, and nonintegral reducible schemes do not satisfy the curve definition used here. Every step was audited for C1 and C4 with its cited statements open; all 22 uses have exact quotations. No step exceeds 2,000 characters, and no elementary fact, duplicate, or item clause was promoted to a new node.
