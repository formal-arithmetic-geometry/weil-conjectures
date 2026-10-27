# Stage-1 report: lem-pur-clopen-common-compact-support

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-clopen-common-compact-support.json`: split into eight explicit steps; statement unchanged; no whole-item Mathlib match.
- `citations.json`: the verbatim statement of every existing node cited in every proof step, with its step number.
- `searches.jsonl`: five searches actually run through the required msearch command. The earlier searches in the live item are retained verbatim; the five new records are appended.

No new nodes or Mathlib leaves. The sandbox initially contained only dispatcher marker files, so the live node was copied before editing. All writes stayed in this sandbox; no git command was run in the read clone, no Lean was written, and no compiler, Lake or build tool was invoked.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for clopen, compactification and extension-by-zero notions. The exact tag had no hit. The project has related partial results, including the clopen idempotent and its finite-partition identity in `SixFunctors/ProEtale/FiniteCoefficient/Derived/ClopenIdempotent.lean`, and the fully faithful open extension in `LowerShriek/Open/FullyFaithful.lean`. I read these: neither states the shared-compactification theorem, its geometry, constructible domain and all natural-isomorphism clauses together. They are not an attachment for this item.

## WANTED

None. All sources used are present.

## What needed repair

The live item was statement-only, extracted from the earlier returned proof of `lem-pur-finite-clopen-exceptional-restriction`. I read its preserved old steps 1–3 in `coord/reports/Q121/lem-pur-finite-clopen-exceptional-restriction.md` and retained every argument: common proper part, geometric finiteness, the two-sided insertion adjunction, normalized extension-by-zero identification, exact derived descent, finite biproduct image, and the constructible compactification comparisons.

I made the auxiliary arguments explicit instead of creating clause nodes. In particular, the closed-subset compactness argument checks quasi-compactness of each component immersion, and the diagonal base-change argument checks separatedness of each restricted map without assuming Y separated over k. Finite-type composition cites the existing general permanence leaf rather than relying on an unstated scheme theorem. The comparison of left adjoints uses the existing unit-equation leaf, rather than citing only the definition of a mate as if it supplied a theorem. Ordinary open composition is constructed from the pro-etale adjunctions directly: the existing `lem-cbc-extension-zero-composition` has etale-origin statement dependencies and was not silently used for a different coefficient/site setting.

Nothing remains unfinished in this one-level split. Its cited open results remain separate DAG work; this delivery does not assert they are already proved in Lean. The statement has not been weakened or corrected, and there is no statement dispute.

## Sources and searches

I read GOAL.md, the three blueprint levels in SETUP.md, the worker role and stage-1 brief, stages/1-dag.md, delivery-errors B–E in both copies, and the tools documentation. The chapter is sec-smooth-purity; the conventions unit sk-def-purity-conv has no proof steps, so there are no realization bindings for this subordinate node to change. Its nearest blueprint ancestor is def-pur-section-invariant. I read its current main-20261015 file: the final invertibility sentence is the ancestor place served by these finite-clopen compact-support arguments. This remains an agent-written supplement, not a claim that the ancestor supplies an unwritten proof. No SGA source is used.

For the geometry I read the Nagata blueprint theorem, the finite-dimension blueprint node, Stacks morphisms.tex `lemma-finite-type-noetherian` (01T6), `lemma-composition-finite-type` (01T3), `lemma-base-change-closed-immersion` (01QR), and properties.tex `lemma-locally-Noetherian-quasi-separated` (01OY). For sheaves I read sites.tex `lemma-mapping-property-glue` (04TS), sites-modules.tex `lemma-extension-by-zero` (03DI) and `lemma-extension-by-zero-exact` (03DJ). For normalization and descent I read categories.tex `lemma-transformation-between-functors-and-adjoints` (0B65), `lemma-compose-counits` (0DV0), and derived.tex `lemma-right-derived-exact-functor` (015F). Finally I read the compactification-coherence blueprint statement and proof, and opened the existing constructible-origin statement to check its bounded-domain conclusion. Every existing node cited in the proof was opened and its statement read; citations.json includes the complete literal statement to preserve the domain conditions, not just a suggestive phrase.

The whole-DAG search was by id, finite-clopen/extension-by-zero/compactification/finite-dimension concepts and the relevant Stacks tags. `tools/blueprint_refs.py ancestor` identifies def-pur-section-invariant. Blueprint searches on clopen, extension by zero, finite type, common compactification and clopen compact found reusable supporting nodes but no blueprint duplicate of this whole assertion. No new id was created. Existing Mathlib-related leaves supply finite-type permanence, Noetherian facts, adjunction normalization, and localization. The actual msearch calls were:

- leanfinder: `For finite clopen components of a scheme a common compactification gives a direct sum decomposition of derived compact support pushforward`
- leansearch: `Extension by zero from disjoint open closed subschemes splits compactly supported derived direct image`
- loogle: `"lowerShriek"`
- grep, in CategoryTheory: `compactSupport|lowerShriek|extensionByZero`
- leanfinder: `The derived direct image with proper support of a finite disjoint union is the biproduct of its component functors`

All services answered. I read the actual hits: the first semantic query gave scheme affine-transition limits, complements in a coproduct of schemes and locally constant fibers; LeanSearch gave compactly supported functions and a zero-section cover lemma. The second phrasing found abstract preservation of biproducts and finite coproducts, not a scheme compactification or a pro-etale compact-support functor. The Loogle and CategoryTheory grep searches had zero hits. Abstract finite-product preservation is written as the elementary adjunction Hom calculation in step 7, so it is not a new node and the existence of those general Mathlib results is not overlooked.

## Not duplicates

No new nodes. In particular I reused `lem-pur-finite-clopen-derived-decomposition` for the module and derived product equivalences, rather than introducing another clopen equivalence or a node restating the summand clause. I reused existing geometric and categorical lemmas instead of adding special cases.

## Review by N9

I checked the eight steps against their cited statements, the old retained proof and the sources just listed. This is the required direct-delivery worker review, not an independent-reader claim.

Step 1 uses precisely the finite-type-over-Noetherian conclusion, local-Noetherian quasi-separatedness, and Nagata's explicit qcqs-target compactifiability clause. A field is Noetherian and Y is quasi-compact by the stated Noetherian convention; no separatedness of its structure map is needed. The compactification definition says open factor and proper factor with the required equality, which is all the step takes from it.

Step 2 uses the existing open-subscheme Noetherian statement, the quasi-compact-open-immersion finite-type statement, the general finite-type composition clause, and the closed-immersion base-change statement. All their inputs are available. Quasi-compactness is checked on affine opens by closed-subset compactness, not by an unjustified affine-intersection claim. The restriction of the diagonal of g is its base change to the open product of components; it is the diagonal of g_i. The final compactification follows simply by composing open-subscheme identifications. The same p is retained, not a second compactification selected separately for each i.

Step 3 uses proper => finite type from the hypotheses, the cited finite-type composition theorem, finite-type-over-Noetherian, and exactly the finite-dimension conclusion of the dimension node. Finite dimension bounds a nonnegative integer, and the empty case is treated separately. This works for every compactification even if it contains a component disjoint from X.

Step 4 uses only the actual equivalence stated by the clopen-derived-decomposition node, which explicitly includes the module category, termwise derived equivalence, bounded constructible restriction and empty-family convention. I wrote the two Hom formulas, why the other components contribute singleton sets, their naturality, and the biproduct inclusions/projections. Thus this is an elementary finite-product calculation from a cited equivalence, not a new lemma hidden as 'standard'. Exactness means exact insertion in the abelian category and its induced derived operation; constructibility follows from the cited restricted equivalence, not a stalk-conservativity assertion.

Step 5 uses the pro-etale extension adjunction, the unit-compatible uniqueness theorem for two left adjoints, and the actual extension-presheaf definition to check the identity normalization after restricting to X_i. It uses the exactness theorem with the finite commutative coefficient A_n, and the exact-functor-derived and localization statements to descend the comparison, its inverse and the unit equation. Both functors invert quasi-isomorphisms because they are exact; no boundedness condition is introduced into this ambient comparison.

Step 6 composes the ordinary pro-etale adjunctions via the composite-adjunction formula and again applies the unit-equation theorem. Evaluation of the restricted sheaf on the same object gives the identification of right adjoints. Exactness and localization apply on the unbounded derived category. Applying the same Rp_* to the descended isomorphism is ordinary functoriality, and the compact-support definition identifies precisely its source and target. This produces the required normalized b rather than an arbitrary isomorphism of objects.

Step 7 is the elementary Hom calculation for finite sums under a left adjoint and finite products under the derived right adjoint Lp^* ⊣ Rp_*. The operations node explicitly asserts that unbounded adjunction, so I have not cited a definition that only introduces underived direct image. Finite products in these additive categories are finite biproducts. The displayed image uses exactly the inclusions and projections from step 4 and b from step 6. The zero object is both initial and terminal, checking preservation in the empty-index case without needing preservation of arbitrary direct sums.

Step 8 checks the compactification-coherence domain: bounded constructible K and inserted components have bounded etale origins by the explicitly cited constructible-origin equivalence. The comparison maps are written as theta_i b (theta_g inverse E_i), and the direct sum uses the corresponding direct sum of thetas. This is the asserted interpretation through canonical comparisons; the coherence proposition supplies naturality and cocycle of those thetas only on its declared domain. The statement asserts no choice-free compact support on arbitrary ambient pro-etale inputs, and the proof does not use one.

For the delivery-errors checks: the statement remains self-contained with its notion dependencies, no new statement-only node contains a proof, no new clause node or duplicate exists, and no mathematical claim is taken from a cited node's proof instead of its statement. Proof dependencies are exactly the union of uses. Generic off-unit tools are declared in split_report.tool_uses with the precise role of each; no purity route is replaced. All eight steps are shorter than 2000 characters, and I checked each for hidden lemmas: the geometric, exactness, adjunction and descent facts all have existing citations, while the residual tuple Hom and finite-(co)product arguments are explicitly elementary. Edge cases tested were I empty/X empty, one identity component, an empty component in a nonempty cover, nonseparated finite-type Y, and an arbitrary extra proper boundary component. None requires a new hypothesis.

## Validation

The preliminary required server `review_split` check passed, with zero new nodes and declared tool uses accepted. The full dry run and delivery follow this report; any diagnostic will be repaired before pushing.
