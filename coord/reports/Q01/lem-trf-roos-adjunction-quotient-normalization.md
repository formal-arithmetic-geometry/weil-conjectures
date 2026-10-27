# lem-trf-roos-adjunction-quotient-normalization — Q01 stage 1

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-roos-adjunction-quotient-normalization.json`: existing statement node, now split into five steps. The statement is unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: nine verbatim statement excerpts, one for each node used in each proof step.
- `searches.jsonl`: actual searches recorded by the required msearch command; inherited item searches remain in the node as historical records.
- `report.md`: this report.

## Attachments

None. Searches under the live `lean/WeilConjectures/` for the exact blueprint tag and for Roos, strictRoos, completionUnit, coefficientSequenceLimit and TrfCompletionRoosNormalized found no declaration stating all the item. `AlgebraicGeometry.ProEtale.completionUnit` in `SixFunctors/ProEtale/FiniteCoefficient/Derived/CompletedExchange.lean:103` defines a completion unit, but does not prove the simultaneous cone/resolution/counit/augmentation assertion. General Roos constructions in CategoryTheory also do not state that assertion. No sorry-bearing project declaration is treated as a completed proof.

## WANTED

None. The item's source, Stacks `sites-cohomology.tex`, Tag 0941 (`lemma-derived-limit-is-ok`), is present and was read, including the preceding sequence-site/constant-sequence adjunction construction and the entire proof of the tag. The normalized quotient-system adjunction refinements are agent-formulated statements already in the DAG, not assertions falsely attributed to Tag 0941.

## Audit and changes

The imported item was a statement-only subproblem of the parent's human-ordered re-split. Its `split_report.retained_arguments` were retained verbatim. Their suggestions are useful source material, but the new proof cites the actual statements of the dependencies rather than relying on their old proof steps. The statement needs no correction and has no disputed assertion.

The only ordinary calculation that needed to be made explicit is the constant-tower counit: on a K-injective tower it is the ordinary limit cone, because that is the ordinary-adjunction transpose of the identity. Transport by the inverse resolution gives one derived tower morphism. Merely specifying all its evaluated maps would not establish this identification. The new Step 2 gives this full argument and Step 3 separately identifies the evaluated scalar-extension adjuncts with the already specified whole-system counit.

The unit equality is already the statement of `lem-trf-completion-unit-strict-quotient-model`, including independence and naturality. It would be a duplicate to introduce a new node for it. The normalized Roos comparison is already the statement of `lem-weil-strict-roos-comparison`. Both are reused. The augmentation's differential is calculated directly as an elementary step.

## Blueprint and route

Read the chapter and unit records and SETUP's three-level rule. Also searched the whole imported blueprint with `tools/blueprint_refs.py search 'Roos'` and `search 'completion unit'`, and searched the DAG for Tag 0941 and the relevant notion names. These found generic existing nodes, not a blueprint node stating this entire simultaneous normalization. Thus `same_as` is empty.

The nearest ancestor is `prop-trf-karoubi-independence`, as confirmed by `blueprint_refs.py ancestor`. It has been removed from the latest blueprint. Its existing provenance and `via` list are preserved. I read `literature/blueprint/latest/blueprint/sec-trace-formula/sk-thm-trace-transport/sk-thm-trace-transport.proof.md` and `thm-trf-l-function-euler-product.proof.md` (current main-20261024 snapshot named in COMMITS.txt), especially Step 1's global/local powers. The item remains the normalization prerequisite extracted from the older common-stage transport argument. This split does not assert that the removed ancestor is still current or alter a chapter or unit route. Off-unit dependencies are generic sheaf/tower/adjunction tools; their purposes are declared in `split_report.tool_uses`.

## Mathlib searches

Ran all four prescribed kinds with the item's id through msearch, then a second conceptual phrasing plus a more focused Loogle query and another grep. All services returned results normally. The first LeanFinder query returned ordinary right-derived functor constructions. The second returned mapping-cone/homotopy constructions. LeanSearch returned `CategoryTheory.Adjunction.derivedη`, cone shifts, and short-exact-sequence triangles. Loogle's combined counit/projection query returned nothing; the focused derived-unit query returned the general derived-unit declarations. Grep located K-injective and general derived-adjunction source. I read `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean`, including `derivedη` and `derivedη_fac_app`, and the definitions and derived mapping property in `Algebra/Homology/HomotopyCategory/KInjective.lean` and `Algebra/Homology/DerivedCategory/KInjective.lean`. These provide ingredients, not a one-line specialization proving this item for strict varying-quotient systems with the specified Roos comparison. No leaf is claimed. Exact query text and actual hit summaries are appended to the item, while msearch's unmodified records are in searches.jsonl.

## Not duplicates

No new nodes. Existing `lem-weil-strict-roos-comparison`, `lem-coef-derived-tower-counit-projections`, `lem-weil-pbc-kinjective-hom-derived`, `lem-coef-derived-system-evaluation-calculus`, and `lem-trf-completion-unit-strict-quotient-model` supply the needed statements. In particular neither the unit clause nor the cone normalization is repackaged as a new lemma.

## Review by Q01

I reviewed B–E of delivery-errors in full against the actual node statements and the Stacks source, not just the inherited retained arguments. There are no statement-only children to audit for self-containment or source tags (B1–B9), no attachment claim (B10), no new elementary or duplicate node (C5, D1–D2), and no inline non-elementary lemma hidden in a long step: the longest step is 1118 characters, below the 2000-character review threshold. TeX is written once. Existing metadata and retained arguments were preserved.

For Step 1 I read the statements of both `lem-weil-proetale-countable-products-exact` and `lem-weil-strict-roos-comparison`. The former applies to any sheaf of commutative rings on a small pro-etale site, hence to the completed coefficient ring here, without a constructibility assumption. The latter explicitly states functorial descent, the zero-shifted-coordinate inclusion, its quasi-isomorphism, the comparison formula, projection compatibility and resolution independence. This verifies the exact-products hypothesis before using the theorem; it is not an unsupported appeal to general homotopy-limit existence. Stacks 0941's short exact sequence on an injective tower is the source model underlying this comparison.

For Step 2 I read `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, `lem-coef-derived-tower-counit-projections`, and `lem-weil-pbc-kinjective-hom-derived`. The first really states computation by a K-injective tower resolution; the second really states the canonical derived constant/limit adjunction with its counit and independence; the third computes maps into a K-injective target for arbitrary complexes, not merely bounded-below ones. I used its unbounded clause. With the model Rlim(D) = lim(I), the identity transposes to the ordinary cone, whose transition equation is written explicitly. The inverse [q] is taken in the derived tower category; its evaluation is [q_n] inverse. Thus a single counit map, rather than unrelated levelwise choices, is calculated. Smallness is the item's fixed module-universe small skeleton; the tower index is countable. No assumption that restriction carries K-injectives to K-injectives is used.

For Step 3 I read the full statement of `lem-coef-derived-system-evaluation-calculus`, in particular its unqualified whole-system adjunction and counit paragraph. It asserts the actual counit's scalar-extension-adjunct formula even for systems that are not normalized. The later internal-Hom and enriched clauses, which have normalization hypotheses, are not used. This matters because C here is arbitrary. The source of this simultaneous system assertion is the existing agent-formulated calculus; it is not claimed as the text of Stacks 0941.

For Step 4 I read `def-weil-strict-roos-model`. Its shifted-first differential agrees with the sign convention in `lem-trf-completion-unit-strict-quotient-model`. I calculated the two coordinates of d v explicitly using the actual quotient maps. This is a chain identity from a definition, so it is marked elementary and creates no node. It makes sense for arbitrary unbounded P: the differential involves no sum over degrees.

For Step 5 I read the entire statement of `lem-trf-completion-unit-strict-quotient-model`, not just its title or proof. It states the equality of entire derived morphisms and the two-resolution description, naturality and independence, for every flat-term K-flat representative and without completeness or boundedness. I checked the variable substitution F for its E and p for its q, and that its normalized rho is exactly the Step 1 comparison. Thus the equality is not inferred merely from its projections (C4, E5). These existing nodes have no dependency path back to this item in the read DAG; the server dry run checks cycles again (C6).

Small cases were checked at the statement level: the empty scheme and the zero complex give zero maps; E=L=M simply repeats the same construction; n starts at 1 so there is no nonexistent level-zero quotient; a degree-zero flat complex has the same zero shifted coordinate and its quotient tuple is killed by 1-s. The unit is not asserted invertible for arbitrary K. No completeness, normalization of C, finite Tor amplitude, or boundedness was introduced. All cited statements' used passages occur verbatim in citations.json. No SGA source is used.

## Unfinished work

None for this stage-1 split. Existing dependency nodes remain responsible for their own later Lean proofs; this delivery adds no Lean and claims no compiler validation. The required server dry run and delivery are performed after this report is written.
