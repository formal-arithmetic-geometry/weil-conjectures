# Q74: lem-sfb-space-coherator-distinguished-square-triangle

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-coherator-distinguished-square-triangle.json`: statement, now split. The statement is unchanged. Added the definition of a triangulated category to statement dependencies, supplied five proof steps, their exact dependency union, document origin, blueprint search result, and the actual additional Mathlib searches. Retained the inherited fields, ancestry and original search records.
- `citations.json`: one entry for every step/node pair, quoting the cited node's statement verbatim.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searching the item tag and coherator/distinguished-square terminology under `lean/WeilConjectures/` found no project declaration for this statement. `DQCoheratorAdjunction.lean` states a coherator adjunction for schemes and `DerivedMayerVietorisTriangle.lean` treats Zariski opens of a scheme; neither states this algebraic-space small-etale assertion. No compiler or Lean build was run.

## WANTED

None. The proof follows local Stacks sources throughout.

## Findings and corrections

The imported item was statement-only. Its statement agrees with Tag 0CR6 and requires no dispute or correction. All four spaces are explicitly qcqs, so the four coherators exist. The open and etale arrows need not be separated. The proof explicitly verifies quasi-compactness and quasi-separatedness of each arrow before using the derived pushforward theorem.

The whole-DAG source/tag and concept searches found existing interfaces sufficient for the argument: `lem-sfb-space-relative-mv-exchange-triangles` specializes at the identity to the uncoherated triangle; `lem-sfb-space-derived-pushforward-coproducts` includes preservation of quasi-coherent cohomology, without using its coproduct clause; `lem-sfb-space-derived-coherator-adjunction` explicitly includes triangulatedness. Thus no new 08GW or 0CR5 wrapper is needed. The 0CR5 identification is the short composition of the already cited Hom bijections and the existing right-adjoint uniqueness theorem. The proof does not replace the item with a restatement in a new node.

Read the current blueprint under `literature/blueprint/latest/`, including the unit and direct-images proof. This coherator fact is an inherited prerequisite through the recorded support/effectivity ancestry, serving the 0CSS bound, rather than a change to the unit's direct-image route. `blueprint_refs.py ancestor` reports `None` for this ancestry; its inherited `from.node` and informative `from.place` were retained. Whole-blueprint searches for `coherator`, `Mayer`, and `quasi-coherent` found no blueprint node stating the item. The only `Mayer` hit was `lem-kun-0f10`, a scheme cohomological-dimension assertion, not this triangle.

The five Mathlib searches run with the mandated wrapper are in `searches.jsonl` and the item. Both semantic phrasings were read. The relevant Mathlib source inspected was `CategoryTheory/Sites/MayerVietorisSquare.lean`, including the structure at line 88, and `CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean`, including the abelian-sheaf cohomology sequence at lines 118–145. These provide ordinary sheaf/cohomology facts, not a derived coherator on algebraic spaces. The second semantic phrasing returned underived sheaf-of-modules adjunctions. Loogle returned zero hits. No search was inferred or fabricated.

## Tool uses

`lem-a1-space-finite-affine-subatlas` is an off-unit generic tool used only for its explicit continuous-surjection consequence: a quasi-compact scheme atlas has quasi-compact target point space. It reconciles the item's atlas formulation with the permanence lemma's topological formulation. No finite-affine refinement or alteration route is used. This tool use is declared in the item's split report. The other off-unit citations, the definition of a triangulated category and `det-sp-unique-right-adjoint`, are Mathlib leaves.

## Not duplicates

No new node was created. Existing stronger nodes were reused rather than specialized into duplicates.

## Review by Q74

I read `spaces-perfect.tex` at `remark-explain-consequence` (0CR6), `lemma-exact-sequence-j-star` (08GW), `lemma-unbounded-relative-mayer-vietoris` (08JK), `lemma-better-coherator` (0CR4), `lemma-pushforward-better-coherator` (0CR5), and `lemma-quasi-coherence-direct-image` (08FA). I also read `spaces-morphisms.tex`, `lemma-quasi-compact-quasi-separated-permanence` (073B). The source's Hom-functor argument for 0CR5 is exactly the comparison used here. There is no new node whose source must be checked.

For step 1, I opened the finite-affine-subatlas, qcqs-permanence and coherator-adjunction node files and read their statements. The first really states that a continuous surjective image of a quasi-compact source is quasi-compact. The second really applies to any morphism from a qcqs source to a quasi-separated target; hence it applies separately to U, V and T mapping to W. The third gives a right adjoint which is explicitly triangulated, not merely an abstract module coherator. These checks avoid inserting separatedness or boundedness.

For step 2, I read the entire statement of `lem-sfb-space-relative-mv-exchange-triangles`. It states the relative triangle for arbitrary morphisms and arbitrary unbounded module complexes, naturally in the complex, with the indicated restriction/difference maps. The specialization at the identity gives precisely what this step needs, not just a long exact sequence of groups. The chart-calculus statement supplies the canonical derived adjunctions and their unital/composition comparisons. Identity pushforward is identified by that adjunction. No restriction of an unbounded complex is being assumed K-injective without justification: this is already part of the cited derived-triangle interface.

For step 3, the coherator-adjunction statement says its source is the full triangulated quasi-coherent subcategory and its right adjoint is triangulated. I checked the definition of exact/triangulated functor and the triangle-isomorphism axiom in `def-weil-triangulated-category`. Applying the functor therefore gives a distinguished triangle in that subcategory and then in the ambient category. The finite biproduct comparison is proved by the additive inclusion/projection identities in the step; it does not require an extra infinite-product or coproduct theorem.

For step 4, I opened `lem-sfb-space-derived-pushforward-coproducts` and used only its explicit sentence that qcqs Rf_* lands in D_QCoh. The qcqs hypothesis was checked in step 1. The chart-calculus statement explicitly says derived pullback preserves quasi-coherent cohomology and supplies Lu* adjoint to Ru_*; for etale j, this Lu* is the exact restriction in the item. I checked both Hom bijections in the coherator-adjunction statement. Fullness then gives the last Hom bijection in the displayed chain. The statement of `det-sp-unique-right-adjoint` supplies the natural inverse isomorphisms compatible with counits for these two right adjoints of the same functor. This proof uses the statements of those nodes, not constructions inside their proofs. It is a short calculation from the cited adjunctions, so a new comparison node would be unnecessary.

For step 5, I checked that all three transported arrows are written with their actual inverse isomorphisms, and that the last arrow includes the exact shift comparison introduced in step 3. The isomorphism of triangles is (1,u,v); cancellation verifies each square, so no unspecified completion or unsupported claim about connecting-map compatibility is used. Naturality follows from the original natural triangle and the natural adjoint comparisons. The cited triangulated-category definition really includes invariance of distinguishedness under isomorphism.

I checked B–E of `coord/delivery-errors.md` against this delivery: no unsupported source-only citation, no new elementary/duplicate/clause node, no unnamed non-elementary input, no boundedness assumption on E, and no SGA citation. All 12 step/node pairs have verbatim quotations in `citations.json`. Every proof step is shorter than 2000 characters. I traversed the cited nodes' statement and proof dependencies and found no dependency path back to the item. On U empty the complement condition forces V to be W and the triangle is DQ_WE -> DQ_WE -> 0; on U=W it is DQ_WE -> DQ_WE plus Rj_*DQ_VE_V -> Rj_*DQ_VE_V; E=0 gives the zero triangle. Nonseparated qcqs etale V is allowed throughout. No finite-dimensional, Noetherian or finite-type assumption has entered.

## Unfinished work

None within the one-level stage-1 split. Server dry run and push results are reported by the delivery tool.
