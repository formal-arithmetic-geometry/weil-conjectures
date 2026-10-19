# Worker report: lem-zl-affine-curve-range

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-zl-affine-curve-range.json — statement; split by eight proof steps, using existing nodes; not a Mathlib leaf.
- citations.json — a verbatim statement quote for every step/node pair, retaining the qualifiers as well as the formula used.
- searches.jsonl — actual msearch.py queries and results; report.md — this report.

No new nodes, no Mathlib leaves, no Lean files, and no unit changes. This is a subsidiary range node, not the key statement of sk-l-dl-a1-endpoints.

## Attachments

None. I searched WeilConjectures by the blueprint tag, by compactlySupportedCohomology_of_isAffine, and by the affine-curve notion. WeilConjectures/WeilSheaf/Cohomology.lean:130 states the matching theorem AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine, but its proof ends in sorry at line 136. The current source checkout does not contain the AffineCurveUpper module named in the historical audit, and its listed lisse theorem would in any event cover only a special case. The audit's unassigned finiteLowerStar_singleFunctor_of_isAffine at SixFunctors/ProEtale/Adic/LowerStar.lean:411 is a general finiteness theorem with sorry; it is not the range statement and the proof here does not use it. Its historical source route is excluded by this brief. I did not manufacture an unused node for it.

## Wanted sources

None: the proof follows the current local blueprint and the Stacks sources available in literature/. No prohibited source is used as a proof reference.

## Statement clarified

The source followed is main-20261015/blueprint/sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/lem-zl-affine-curve-range.md and its .proof.md, as required by blueprint_update. The old statement's bare word “constructible” could refer to an object of a derived category. That reading is false: the constant sheaf on the affine line shifted by [1] has nonzero compact cohomology in degree one, and shifting by [3] places its nonzero degree-two compact cohomology in degree minus one. The current blueprint explicitly says constructible Weil **sheaf**, and explicitly rules out arbitrary shifts. I wrote that degree-zero meaning, the global finite-field datum, the geometric curve C, the prime-to-characteristic convention, and relative dimension one into the statement. This restores the supplied source's meaning and does not impose connectedness, lisseness, or a Weil-stable lattice.

## What was repaired

The imported proof was a historical stage-3 negative/positive branch decomposition. Its positive-range helper is an existing clause, not a complete explanation of the current blueprint's finite-level route. I replaced that proof by the finite coefficient completion, finiteness, Milnor and scalar-extension argument. The blueprint_update and all audit/import metadata remain in the sandbox node unchanged.

The current source itself cites lem-sc-cohomological-dimension “(a)”, although the current DAG statement has no labelled (a) and asserts only the upper bound. Step 5 uses precisely that upper bound and separately writes the nonnegative injective-resolution argument for negative vanishing. Likewise the direct-image-limits proposition does not state the displayed Milnor sequence in its statement. Rather than attribute that sequence to it, Steps 6–7 cite the existing ringed-site derived-sections/limit theorem and the existing Milnor sequence. The integral compact-support definition already gives the required inverse limit with its transitions.

The source's shorthand “choose a lattice” also needs more than the definition of the Qbar category: Step 2 cites the existing lem-trf-curve-integral-lattice, which actually supplies a torsion-free degree-zero model with finite-Tor etale-origin reductions. This avoids the false inference that an arbitrary derived reduction of an arbitrary lattice is a degree-zero sheaf. I did not identify completed integral coefficient sheaves with discrete constants.

## Not duplicates

No new nodes. The searches of the full DAG and blueprint located and reused lem-trf-curve-integral-lattice, lem-sc-smooth-curve-connected-coproduct, lem-kun-site-rgamma-derived-limit (Stacks 0D6K), lem-pc-derived-limit-milnor-sequence (07KY), and the existing comparison, finiteness and Mittag--Leffler nodes. The endpoints unit has a range clause for j_* of a lisse sheaf, which is a special input, not a second declaration of the general constructible-sheaf item. lem-zl-affine-curve-range-positive states only the positive-degree branch and was not substituted for the proof.

## Mathlib searches

I ran the recorded msearch commands for the item: two natural-language LeanFinder phrasings, LeanSearch, Loogle for compactlySupportedCohomology, and a source grep for compactlySupportedCohomology and curve/cohomology patterns. LeanFinder returned generic DerivedCategory.isZero_of_isGE/isLE and related support facts; LeanSearch returned support and scheme-etale definitions, not an etale compact-support range theorem. Loogle and source grep returned no hit. These are no-match results for this item, not a claim that the generic homological tools are absent. No search was invented or copied from another group.

## Review by Q11

I read the main-20261015 range statement and all three paragraphs of its proof, the fixed chapter record, and the endpoints unit's final curve-dimension sentence. I also read the current smooth-curve compactification and dimension proof files, and Step 5 of the trace-formula Euler-product proof that is the source of lem-trf-curve-integral-lattice. For the inverse-limit passage I opened sites-cohomology.tex, label lemma-RGamma-commutes-with-Rlim (Stacks 0D6K), and more-algebra.tex, labels lemma-compute-Rlim (07KW) and lemma-break-long-exact-sequence (07KY). The source proof has the finite-group/Milnor route used here. Every new-node check B1–B10 is vacuous because this split creates none; I instead checked each reused statement against the actual place in the proof where it is used.

Step 1 takes finite-stage objects from def-weil-pbc-qbar-category, the underlying degree-zero condition from def-weil-weil-sheaf-complex, and commutation of truncations with coefficient transitions from prop-constructible-truncations. The last one says this in its statement, so replacing the finite-stage object by its zeroth cohomology is justified. The ordinary/compact-cohomology definition explicitly says to forget Weil structure for the underlying coefficient complex.

Step 2 uses the same-objects clause of def-weil-pbc-rational-category only to select an integral representative. The much stronger torsion-free model, its degree-zero finite reductions and their etale-origin witnesses are supplied by the statement of lem-trf-curve-integral-lattice, not by a definition or that lemma's proof. Its dimension-at-most-one hypothesis holds for the smooth relative-dimension-one curve. It makes no assertion that a Weil action preserves this lattice, and none is needed here.

Step 3 uses the fixed-relative-dimension base-change clause of lem-sbc-smooth-relative-dimension-permanence, the quasi-compact separated decomposition in lem-sc-smooth-curve-connected-coproduct, and the algebraically-closed, smooth, separated, connected hypotheses of lem-sc-compactification for each piece. Affineness and finite type of the original curve supply separatedness and quasi-compactness. I wrote the short finite-type/diagonal/universally-closed verification of the finite union directly, using the actual definition in def-weil-proper-morphism; it is not a hidden external compactification lemma. All non-elementary geometry in that step has a cited statement. Empty products are explicitly included by the existing finite-coproduct cohomology statement.

Step 4 uses the cohomological-range and constructibility clauses of lem-trf-open-ctf, and the etale-origin hypothesis of lem-trf-compactification-cohomology is met by Step 2. lem-sf-proetale-constructible-origin supplies a constructible **sheaf**, and sk-prop-sf-comparison supplies the cohomology isomorphism; these are different facts, both cited. I did not use the origin equivalence alone to infer a derived-sections comparison.

Step 5 uses only the upper bound from lem-sc-cohomological-dimension, separately the finite-coproduct assembly, and the explicit nonnegative injective-resolution construction. The existence of successive embeddings is supplied by lem-weil-pbc-module-sheaves-enough-injectives, and the final bounded-below injective complex computes derived sections by prop-weil-pbc-kinjective-resolutions-exist. Applying sections preserves its zero negative terms, which is the elementary remaining calculation. Each completed component is smooth, connected and separated over algebraically closed k. The module/abelian derived evaluation comparison is cited explicitly to apply the abelian torsion theorem to the underlying finite-ring module sheaf. Proper finiteness in sbc-thm-finiteness-finite-type applies to a finite-type map between finite-type k-schemes with prime-to-characteristic finite coefficients. Its constructible cohomology over the point has finite stalks, so the groups needed for Mittag--Leffler really are finite, not merely finitely generated over an infinite ring.

Step 6 uses the displayed inverse-limit definition of integral compact support, with its specified quotient transitions. lem-kun-site-rgamma-derived-limit states exactly that derived sections take its limit triangle to the abelian limit triangle. Its ringed-site hypotheses apply to modules over the completed integral sheaf on the small pro-etale site of s. lem-weil-point-proetale-sections-exact and the ordinary/compact-cohomology definition identify this with the coefficient realization. No weakly-contractible hypothesis on the proper curve is inserted: derived sections are taken at the algebraically closed point after compact-support pushforward.

Step 7 cites the abelian-complex clause of lem-weil-pbc-mittag-leffler and the actual Milnor-sequence statement. The hypotheses are a countable tower and finite degree-(i-1) groups, supplied in Step 5. The i=3 case was checked separately because H^2 may be nonzero: it is finiteness, rather than a claim that H^2 vanishes or that transition maps are surjective, that removes lim^1. Negative i has zero finite-level groups, so is also covered.

Step 8 uses the exact rational cohomology comparison actually displayed in lem-trf-curve-integral-lattice. The Qbar compact-support functor and point realization are stagewise by their cited definitions. lem-weil-cohomology-commutes-scalar-extension is applied only to the resulting ordinary complex of E-vector spaces. The zero coefficient space has a unique Frobenius action; no assertion that arbitrary Weil-complex categories have the ordinary derived-category properties is used.

I checked the zero sheaf, the empty curve, a finite disconnected union, a sheaf supported at finitely many points, and the degree-three Milnor boundary. None requires a new hypothesis. The shifted-constant example explains why the degree-zero wording is essential. I checked C1/C4 by opening the full statement of every cited node and putting verbatim statements, including their hypotheses, into citations.json. I checked that the added dependencies have no path back to this item. All non-elementary steps are under 2000 characters, and none moves the item's conclusion to a new node. The off-unit tool uses are declared in split_report.tool_uses: they implement the source's compactification and coefficient route, rather than replacing the unit route. This is Q11's self-review; independent review belongs to the maintainer.

## Unfinished work

No unresolved mathematical part of this one-level split. The cited unsplit lattice and truncation nodes remain their own future items. The first server dry run passed at 38fcfd0819; the self-review then made the negative-degree injective-resolution argument explicit and added its two existing supporting statements. The revised delivery is checked again by the required server dry run before the direct push. No local checker or compiler was run.
