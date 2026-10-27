## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-completed-augmentation-adjunct.json`: split statement, unchanged statement and statement dependencies; four proof steps using existing nodes.
- `citations.json`: exact statement quotations for every node cited in each proof step.
- `searches.jsonl`: actual Q129 search-command records, supplementing the inherited Q79 searches retained in the item.
- `report.md`: this report. No new nodes and no Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id, completed augmentation/adjunct, constantRlim, and completed pullback. Read `SixFunctors/ProEtale/FiniteCoefficient/Derived/CompletedExchange.lean:96–118`: its `completionUnit` and `completedUpperStar` are definitions for constant coefficients and principal regular completion, not a proof identifying the specified completed-coefficient strict-tower augmentation with the normalized adjunct. No exact project theorem was found. No compiler was run.

## WANTED

None. All sources needed for the argument are present.

## What needed repair

The imported item was statement-only, not false. Its statement is retained verbatim. In particular its ambient construction applies to arbitrary unbounded K, including non-complete objects. The definition of completed pullback itself restricts the completed-category functor to complete inputs; `lem-sf-exact-pullback-counit-normalization` explicitly supplies the ambient augmented construction for every unbounded K. The proof invokes that clause instead of imposing an extra completeness hypothesis.

The substantive missing identification was that the projection-defined map into the derived limit of the constant tower is the canonical derived adjunction unit. Merely citing an adjunction existence theorem or merely comparing finite derived projections would not prove this. Step 2 uses the explicit chain-transpose formula in an existing general exact-square theorem, specialized with both comparison functors and their comparison isomorphism equal to identities. No new lemma restating a clause of the item is needed.

## Source and searches

Read `literature/stacks-project/derived.tex`, Tag 0FND, label `lemma-pre-derived-adjoint-functors-general`, especially the ordinary-adjunction passage in its Hom calculation, and Tag 09T5, label `lemma-derived-adjoint-functors`. Read `sites-cohomology.tex`, Tag 0941, label `lemma-derived-limit-is-ok`, where the unbounded derived limit is computed as the termwise limit of a K-injective tower. The ringed module specialization is already the statement of `lem-weil-pbc-ringed-strict-tower-homotopy-limit`. The current blueprint `main-20261015/.../prop-sf-localization-all-stages.md`, the chapter, unit, parent factorization split and its review were also read. The equality proved here refines the returned localization comparison, rather than replacing the unit's route. Proof origin is agent: the explicit normalization calculation is a refinement of these sources, not a verbatim theorem of the blueprint. No SGA source was used.

Ran the required msearch command for leanfinder with two distinct phrasings, loogle `CategoryTheory.Adjunction.derived_unit`, grep `derived_unit|derivedη` restricted to CategoryTheory, and leansearch for the K-injective augmented tower adjunct. All services returned results. Read `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:35–156`, in particular `derivedη_fac_app` at line 103: it is the general universal comparison formula and does not identify this sheaf-theoretic augmented construction without the argument in the item. The second leanfinder query also returns exact-localization comparisons. The first finds unrelated Cech/pullback cone results. The LeanSearch results give ordinary constant/limit adjunctions and bounded-below resolution tools. None is an exact or one-line Mathlib proof of the item. Inherited Q79 search records were retained; Q129 records describe only searches actually run.

## Not duplicates

No new nodes were created. Whole-DAG keywords and Stacks-tag searches, plus whole-blueprint searches for `derived adjunction` and `augmentation`, were used to find the existing tools. In particular:

- `lem-weil-pbc-exact-square-derived-counit` already supplies the general chain-level transpose formula, so no new resolution-adjunct lemma was created.
- `lem-cbc-constant-derived-limit-resolution-unit` states descent and naturality of the projection-defined constant-tower map, but does not assert in its statement that this map equals the specified canonical adjunction unit. Its proof was not used as a black box.
- `lem-coef-derived-tower-counit-projections` fixes the canonical derived adjunction and its counit projections; it does not itself give the chain-transpose normalization required here.
- `lem-weil-pbc-tower-derived-evaluation-normalization` concerns evaluation of a tower of derived right-adjoint operations, rather than identifying this augmented map.
- `lem-weil-pbc-completed-quotient-unit-normalization` concerns the unpulled quotient reduction counit. The present calculation is for the actual pulled strict augmentation and gives its resolution representative.
- The exact-pullback normalization and the cochain-augmentation-descent nodes address other comparisons; neither was replaced or duplicated.

## Review by Q129

I checked the item against the returned localization comparison and the Stacks derived-adjunction construction above. There is no statement correction and no new statement to test. I opened the statement of every proof citation, rather than taking information from its proof. In Step 1, the exact-pullback normalization gives the original universal-counit comparison both on towers and on constant towers, and explicitly the ambient construction for arbitrary unbounded inputs. The completed-pullback definition gives the strict quotient augmentation followed by its projection-defined constant-tower map. Thus the cochain map u represents the actual a_K, with the correct direction j_K inverse; this is not an unspecified isomorphism between functors. Although the normalization node distinguishes tensor pullback G from scalar-transport pullback F, its specified ordinary module isomorphism identifies them because c_g is an isomorphism; exactness transfers along that isomorphism.

In Step 2 I checked all hypotheses of the exact-square theorem after specialization. Both abelian A categories are the target tower category and both B categories the target module-sheaf category. The left adjoints are constant towers, which are additive and exact levelwise; the right adjoints are ordinary limits. The identity r and s are exact and preserve K-injectives. The beta comparison is identity between the same derived-limit pair, so its normalization is tautological. Small ringed sites and module sheaves fall under the cited tower homotopy-limit theorem, which supplies unbounded resolutions, without requiring exact products. The coefficient-tower counit theorem selects the canonical adjunction induced by the same ordinary adjunction. The exact-square statement explicitly gives the transpose of a chain map as the universal right-derived comparison composed with its ordinary transpose. Applying it to q:Delta C→I identifies v with the resolution-defined z; all inverses used here are inverses of Qq. This directly addresses C4: the formula is in the cited statement, not just its proof.

Step 3 applies that same explicit formula to r u:Delta C→J. Its ordinary transpose has components r_n u_n by the inverse-limit universal property, in the category of complexes. Equality is established there before localization, so it never infers equality of arbitrary derived maps from equal projections. The K-injective computation identifies the codomain with Q lim J, and every resolution gives the fixed adjunct. This gives both the representative and independence clauses. No assertion that the exact pullback preserves K-injectives enters: the only K-injective complexes are chosen after pullback.

For Step 4 the adic datum states that the quotient-tower construction is a derived functor. The augmentation is natural on K-flat representatives by the displayed tensor formula; its equality descends through that same localization. Then naturality of j and of the adjunction unit gives the written equation for every derived morphism. These are a few elementary naturality substitutions, so that step is marked elementary; Steps 1–3 are marked non-elementary and cite their inputs. Every step is shorter than 2000 characters. Definitions, ordinary limit uniqueness, and naturality account for the remaining elementary operations; there is no uncited lifting or K-injective comparison lemma hidden inside them.

I tested the formulas with K=0 (both maps zero), g the identity (the usual quotient completion map), a zero augmentation (zero adjunct), and a constant strict augmentation (the unit identity). For a non-complete object such as a complex with the adic generator inverted, the formula still gives the augmented limit map even if the reduction tower vanishes; it does not assert that K is its own completion. Indexing starts at n=1, and the cochain limit calculation is degreewise, so no boundedness assumption is used. I also checked that the new proof edges do not lead back to this item, including the general exact-square tool. Citations are quoted verbatim in citations.json. B–E checks introduced no extra node or stronger hypothesis. The generic off-unit tools are declared in split_report.tool_uses for maintainer review, not installed as maintainer-owned tool_uses.

## Unfinished work

None in the stage-1 argument. Server dry run and delivery follow this report; their results are recorded below when complete.
