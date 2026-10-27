# Q51 — lem-sfb-field-groupoid-perfect-restriction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-field-groupoid-perfect-restriction.json`: statement item split into five complete steps; not a Mathlib leaf. Statement and statement dependencies unchanged. No new nodes, no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every step/node citation.

The sandbox was empty of node files and reports when I started. I copied the current item, retaining its statement, citations, original Mathlib searches and blueprint ancestry. Logged new searches are in `searches.jsonl`. No Lean, compiler, Lake, build, repository write, direct git operation or sub-agent was used.

## Attachments

None for the item. Searching `lean/WeilConjectures/` by the blueprint id and by groupoid, perfect field and restriction found no declaration stating all its clauses. The existing closed node `lem-pc-homeo-pure-insep` already records `AlgebraicGeometry.isHomeomorph_baseChange_of_isPurelyInseparable` in `WeilConjectures/AlgebraicGeometry/HomeomorphPurelyInseparableBaseChange.lean:29`; this is a reused dependency, not an attachment of the item.

## WANTED

None. All sources used are present in the read-only literature tree.

## What needed correction

The item was statement-only, not an existing split. Its statement is correct and unchanged. Stacks `groupoids.tex`, Tag 02VB, label `lemma-restrict-groupoid`, omits its proof; I supplied the morphisms and all laws rather than citing its omission as an argument. The two applications of purely inseparable base change must use different maps to Spec k: first s, then t composed with the first projection. Treating the second pullback as scalar extension for the s-structure would give the wrong fibre-product equations. I spelled out both maps.

The inherited blueprint.from.node is null and its via list is long; `tools/blueprint_refs.py ancestor` returns None for this item. I preserved these live provenance fields and made no invented blueprint id. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-images proof, alongside the recorded unit and chapter. This is a supporting groupoid input in the inherited direct-image chain, not a replacement of the unit's route.

## Not duplicates

No new nodes. Before considering a perfect-closure node I searched the entire DAG for perfect closure, purely inseparable/perfect and Tag 046W, and found `lem-weil-pbc-perfect-purely-inseparable-overfield`, whose statement gives exactly the needed field. I reused it. Before considering a topology node I read and reused `lem-pc-homeo-pure-insep`. Before considering a groupoid-restriction node I searched Tags 02VB, 04LQ and 04Q9 and groupoid/restriction keywords; the general construction is a direct fibre-product calculation, so it is written in steps, not made into a new node. `def-sfb-restricted-groupoid-relation` defines only a relation with a different endpoint order; it is unnecessary here. The existing fppf restriction-quotient lemma requires locally finite presentation and proves sheaf quotient descent; neither its extra hypothesis nor conclusion is appropriate here. Blueprint searches for perfect closure, purely inseparable, restrict groupoid and groupoid found no same-statement blueprint node.

## Review by Q51

I read the whole of delivery-errors B through E (including the isolated-run copy) against the files and sources. For the item I read Stacks more-groupoids.tex, Tag 04Q9, `lemma-locally-closed-image-is-closed`, first proof paragraph, and Tag 04LQ, `lemma-restrict-groupoid-on-field`, statement, diagram and proof. For the field input I read algebra.tex, Tag 046W, `lemma-perfection`, and Tag 046X, `definition-perfection`. For the explicit restriction operations I read groupoids.tex, Tag 02VB, `lemma-restrict-groupoid`, and its preceding set-groupoid explanation. There are no new nodes requiring separate sources. I used no SGA source.

Step 1 cites the statement of `lem-weil-pbc-perfect-purely-inseparable-overfield`, not its proof: its exact power condition and perfection clause supply the field for both groupoids at once, without finite extension or finite-type assumptions. Mathlib searches returned perfectClosure.isPurelyInseparable and perfectClosure.perfectField. I read those declarations in Mathlib/FieldTheory/PurelyInseparable/PerfectClosure.lean:93 and :190, and the algebraic-closure perfection instance at IsAlgClosed/Basic.lean:373; the existing Mathlib leaf already packages them. I did not duplicate it.

Step 2 uses `def-pc-fibre-product` for its stated existence, morphism universal property and uniqueness, and `def-a1-groupoid-scheme` for its stated source/target identities. I opened both node files. The endpoint equations gx=t(r), s(r)=gy agree with the item's target-first product order. Each displayed identity, inverse and composition tuple satisfies them, and its components are actual scheme morphisms; composition first maps into the original composable-pair fibre product. This is an elementary construction from the cited definitions, not an appeal to unrecorded representability or Yoneda lemmas.

Step 3 uses the same two statements for the identity, inverse and associativity equations and uniqueness with prescribed coordinates. I checked both possible inverse composites with the target-first convention. Threefold composites retain the same outer endpoints and reduce precisely to the original associativity equation. Equality of morphisms follows by the fibre-product universal property applied to these component equations. Precomposition commutes with the formulas since each component is a morphism. No new non-elementary assertion is hidden here.

Step 4 uses `def-pc-fibre-product` and the hypotheses on a, which explicitly include all operations and the identity object map. The displayed middle-coordinate equations prove preservation, and the two composites to R2 have the same middle coordinate. This checks morphism equality rather than only a topological square or geometric points. No extra hypothesis on a is used.

Step 5 uses the whole statement of `lem-pc-homeo-pure-insep`, which I opened and compared to its closed project declaration. That statement applies to every k-scheme, not just finite-type or affine schemes. Both Rj via sj and Bj via tj composed with bj are k-schemes; the perfect extension from step 1 is purely inseparable. Thus its two applications have precisely the hypotheses in force. `def-pc-fibre-product` identifies the iterated pullback by the three projections and their equations. Composition of the homeomorphisms has the explicit continuous inverse written in the step. I did not cite the similarly named universalHomeomorphism_composition node: its actual statement concerns etale/cohomological compositor comparisons, not this topological claim.

I tested characteristic zero (the field input forces k'=k, giving identity projections), perfect positive-characteristic fields (one may take the identity), and the imperfect case k=F_p(t) with its perfection (all finite and infinite p-power roots are allowed). For the unit groupoid R=V, the restricted arrow scheme is V' times_V V', not V'; the formulas still give the pair groupoid, including its possible nilpotent thickening, and the two projections remain homeomorphisms. For the pair groupoid and arbitrary non-finite-type arrow schemes the same test-scheme formulas work. No reduction, smoothness, affineness of Rj or finiteness was assumed. These checks also rule out accidentally replacing the double restriction by a single base change.

The elementary steps give their calculations instead of disguising new lemmas. The non-elementary steps cite the two existing lemmas exactly. Every uses entry has a verbatim quote in citations.json. All steps are shorter than 2000 characters. Existing source/search metadata was preserved; newly recorded Mathlib queries are exactly those actually run by msearch.py, and the hits distinguish group objects or open/manifold restriction from the present internal groupoid assertion. There are no unintroduced objects, proof sketches inside new statements, altered hypotheses, dependency cycles introduced by new nodes, or route substitutions.

## Unfinished work

None in the stage-1 split. Validation and direct delivery use the prescribed server dry-run and delivery commands; the independent maintainer review remains the project's normal next step.
