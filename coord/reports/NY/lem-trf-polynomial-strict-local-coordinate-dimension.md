# Stage-1 delivery: lem-trf-polynomial-strict-local-coordinate-dimension

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-polynomial-strict-local-coordinate-dimension.json`: statement item, now split into six steps using existing nodes; no exact Mathlib match for the whole statement. The statement and its statement dependencies are unchanged.
- `citations.json`: nine verbatim dependency-statement quotations, one for every step/node citation.
- `searches.jsonl`: the four actual NY search-command records; the imported Q17 search records remain in the item as history.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint tag and by strict-henselization, regularity, dimension and coordinate terminology did not locate a declaration giving the entire item. The existing `Algebra.ringKrullDim_eq_of_isStrictHenselization` in `WeilConjectures/RingTheory/StrictHenselizationDimension.lean:206` gives the already represented dimension-invariance ingredient, not polynomial coordinate codimension and regularity.

## Wanted

None. All sources used are available in the shared repository.

## What was wrong or missing

The item was statement-only. No false statement or source error was found. Its quantifier over arbitrary primes matters: Tag 00OP computes dimension at maximal ideals and cannot be applied directly to the given prime. I instead apply 00ON to the coefficient inclusion from the polynomial algebra on the selected coordinates. Its contracted prime is the maximal origin ideal, where 00OP applies. The local fibre is the prime localization of the complementary-coordinate quotient. This follows the sources named by the imported item and supplies the missing calculation.

I kept the imported `blueprint.from` chain, its precise `place`, and `same_as: []`. I read the latest ancestor statement/proof and latest unit/chapter texts under `literature/blueprint/latest/`, snapshot main-20261023-1620. The algebraic lemma is historical auxiliary material below the unit route, not a proposed replacement of that route. The whole-DAG tag/concept searches and whole-blueprint searches for polynomial rings, polynomial dimension, and strict henselization found ingredients but no second statement of the whole item.

## Unfinished

Nothing remains for this one-level stage-1 split. Existing dependencies retain their own current proof/stage states. No Lean was written or compiled.

## Not duplicates

No new nodes were created. In particular, the existing polynomial regularity, origin dimension, flat height, and strict-henselization nodes are cited instead of duplicated.

## Review by NY

I read `algebra.tex`, Tag 00ON (`lemma-dimension-base-fibre-equals-total`, statement and proof at 27421 onward), Tag 00OP (`lemma-dim-affine-space`, 27660 onward), and Tag 00OQ (`proposition-finite-gl-dim-polynomial-ring`, 27723 onward). I also read `morphisms.tex`, Tag 01U5 (`lemma-flat-characterize`, 4694 onward), and `more-algebra.tex`, Tags 06LK (`lemma-henselization-dimension`, 11132 onward) and 06LN (`lemma-henselization-regular`, 11195 onward), including their hypotheses. No new nodes require separate sources.

Step 1 uses exactly the monomial description and universal property in `def-weil-pbc-mv-polynomial-ring`. Grouping monomials proves the iterated-polynomial identification; discarding monomials divisible by a selected variable proves the quotient description. Evaluation gives A/m = k. Since the contraction is proper and contains this maximal ideal, it equals m. These are explicit elementary calculations, not an unrecorded dimension lemma.

Step 2 reads `lem-weil-pbc-polynomial-ring-field-regular-ring` for its assertion of Noetherianity and regularity at **every** prime. This gives the two prime-local regular rings without a maximal-prime assumption. It reads `lem-weil-pbc-polynomial-ring-origin-regular-local` for the full origin-local dimension equality, using a bijection from the finite coordinate set to Fin |K|. The source 00OP is used only at that origin. The cited statement really includes the dimension equality; it is not merely a definition of regularity.

Step 3 reads `lem-nagata-polynomial-projection-flat`, whose statement gives scheme flatness of the coefficient projection, together with `lem-weil-pbc-flat-ring-map-iff-flat-affine`, whose statement gives the needed equivalence with flatness of the ring map. I included the latter precisely because the former alone is not a ring-map-flatness statement. The polynomial description from step 1 makes the projection hypothesis apply for any complement, including an empty complement.

Step 4 reads `def-weil-pbc-localization-at-prime` for the fraction relation and maximal ideal description. It writes both directions of the isomorphism P_q / LP_q = (P/L)_(q/L), checking denominators and lift independence. Thus the fibre used by 00ON is the right ring, not P/pP without localizing. Further quotient by the maximal ideal gives the claimed common residue field. This is the routine two-map fraction argument and is kept in the proof rather than introduced as a new lemma.

Step 5 reads the **dimension-form sentence** in `lem-weil-pbc-flat-height-formula`. Both A and P are Noetherian by step 2; the coefficient inclusion is flat by step 3; its prime contraction is m by step 1. The formula therefore has exactly the local fibre from step 4. Substituting the origin dimension proves the requested difference, without assuming q maximal.

Step 6 reads both `lem-sc-strict-henselization-regular` and `lem-sc-strict-henselization-dimension`. The former applies to each Noetherian local ring from step 2 and asserts that its strict henselization is regular local. By the inline definition in `def-weil-regular-scheme`, this also supplies Noetherianity. The latter has no extra Noetherian hypothesis and gives each dimension equality for the chosen separable residue closure. Substitution yields the last equality. I did not need a new strict-henselization Noetherianity node or any excellence/perfectness hypothesis.

The origin-local lemma and the two strict-henselization lemmas are generic tool uses from other units: the present unit has no statement of these ring-theoretic facts. Please record them as tools at review if the route bookkeeping requires it. All other cited theorem nodes are already Mathlib leaves. I have not assigned maintainer `tool_uses` or `reviewed` fields.

For small cases I checked E empty, K empty, K = E, and E = {x,y}, K = {x}, q = (x): the latter has dimensions 1 and 0 even though q is not maximal, so it tests the specific risk of replacing local dimension with total polynomial dimension. For q = (x,y), the dimensions are 2 and 1. For K = E the quotient is k and any containing prime equals the origin. No argument uses algebraic closedness or perfectness of k, so inseparable residue fields cause no missing hypothesis. Strict henselization of a field is its chosen separable closure, still dimension zero.

I checked delivery-errors B through E, including the merged copy: all objects and notions are present in the unchanged statement; source places use tags and labels; no new nodes, duplicate clauses, unsupported proof relocations or unverified Mathlib leaves were introduced. Every non-elementary step cites the theorem that supplies its assertion, and every `uses` entry has a verbatim quote in `citations.json`. The two elementary steps carry their actual calculations. Every proof step is under 2000 characters. No SGA source is used. I preserved the imported search records and added only the four exact NY queries actually logged by msearch.py; returned candidates were read in the local Mathlib source before the no-match verdict for the whole item.
