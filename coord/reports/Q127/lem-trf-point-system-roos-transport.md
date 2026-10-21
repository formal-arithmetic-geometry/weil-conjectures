# Q127 — lem-trf-point-system-roos-transport

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-point-system-roos-transport.json`: statement, now split into eight proof steps; no Mathlib match for the whole assertion.
- `citations.json`: one verbatim statement quotation for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's unedited log; `write_split.py` is sandbox-only preparation code.

No new DAG nodes, no new Mathlib leaves, no unit edits. The statement, original source, original search records, provenance and blueprint ancestry are retained. The added proof references the existing homological tools; the remaining argument is explicit section and coordinate computation.

## Attachments

None. Searches of the live project source under `lean/WeilConjectures/` for the exact blueprint tag, point-system and Frobenius-point-transport names, and the Roos/point-transport notions did not find a declaration stating the item. The existing `CategoryTheory.roosComplex_quasiIso` in `Algebra/Homology/RoosComplex.lean` supplies a general normalization ingredient; it does not supply semilinear point-system transport, either comparison in this item, or their displayed compatibility. Its statement and docstring were read. No proof was inferred from a declaration containing sorry.

## Literature wanted

None. The argument is marked agent-written: the blueprint motivates it but does not contain the explicit whole-cone calculation.

## What needed attention

The imported item was statement-only. I read the current blueprint's `prop-trf-rational-frobenius-integral-model.proof.md`, especially (3), and `thm-trf-l-function-euler-product.proof.md`, Step 1 / Global powers. The former defines the integral maps as derived limits of levelwise composites; the latter uses their naturality and composition. This item supplies the whole-tower point comparison below that route, without altering the unit or introducing a different route.

I also read `lem-cbc-completed-extension-zero-comparison.proof.md` for the provenance of the generic exact-product-functor tool and the actual Stacks source `sites-cohomology.tex`, Tag **0941**, `lemma-derived-limit-is-ok`. The latter explains total derived limit via a simultaneous K-injective tower and the inverse-limit/product short exact sequence. It does not state the point comparison or its normalization: those are supplied by the existing explicitly formulated DAG tools and the calculation here. The generic tool's source mentions 0940, the section tag; the specific lemma read here is 0941. No SGA source is used.

There is no statement correction or dispute. In particular the assertion remains on all of the ordinary unbounded derived SYSTEM category. The restriction/colimit-insertion recipe in `def-weil-frobenius-point-transport` is normally introduced there on bounded constructible objects; Step 6 checks its same termwise formula and naturality on arbitrary completed-module complexes, as this item's statement requires. It does not invoke any constructibility-dependent assertion of that definition.

The sign convention of the generic comparison is not literally the item's order of summands. The proof includes the chain isomorphism `(b,a) -> (a,-b)`, checks its differential, and checks that it preserves the normalization and diagonal comparisons. This prevents a hidden sign or extra off-diagonal map.

## Unfinished work

None for this split. Existing unsplit dependencies remain their owners' items, notably `lem-trf-point-system-transport-descent`; only their statements are used here.

## Not duplicates

No new nodes. Whole-blueprint searches for `Roos` and `point transport`, and the existing item ancestry, revealed generic limit and transport ingredients, not a blueprint statement equal to this whole-system assertion. The existing generic exact-product-functor comparison is reused instead of creating a point-specific instance. Consequently there are no new/existing same-tag pairs to distinguish.

## Mathlib searches

The search command ran LeanFinder twice with different formulations, Loogle, LeanSearch and source grep. All succeeded; none was recorded as unavailable. Their exact query strings and returned names are appended to `mathlib_searches` and are recorded by `searches.jsonl`. The Loogle hit `CochainComplex.mappingCone.mapHomologicalComplexXIso` and its equational variant were read in `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`, lines 580–637: these are the ordinary additive-functor cone comparison, not this point-system theorem. The other returned hits concern product comparisons, exact functors, derived transformations, compatible sheafification and topological-sheaf product diagrams. None identifies the specified maps on strict semilinear systems with their point restriction on both Roos coordinates. No additional Mathlib-only node was needed.

## Review by Q127

I checked the chapter record `sec-trace-formula` and the unit `sk-thm-trace-transport`, including its finite-level-to-integral route. The split realizes the already assigned prerequisite of the Global powers argument, not the statement of the unit itself, so its realization fields were not edited. The sources actually read for the item are identified above; there are no new nodes whose source needs a separate review.

For Step 1 I opened the statements of `lem-coef-derived-system-evaluation-calculus`, `def-weil-inverse-image-pullback-comparison`, and `lem-weil-proetale-isomorphism-inverse-image`. They give respectively exact scalar restriction and the actual realization functor, the completed scalar identity and exact transported module action, and the site equivalence/reindexing formula. The completed coefficient is not incorrectly treated as a constant sheaf: its compatibility is checked by its limit projections. The canonical finite-level insertion maps are retained through the prescribed j identifications. The small-site hypothesis is the fixed small-skeleton convention in the system-calculus statement.

For Step 2 I checked `lem-weil-point-proetale-sections-exact` on all module sheaves and arbitrary complexes, not just constructible objects; `lem-weil-proetale-countable-products-exact` states both exactness and sectionwise computation; and `def-trf-coefficient-tower-operations` retains the actual transitions and scalar restrictions. Those are exactly the hypotheses needed for sections. For ordinary R-modules the coordinatewise lift verifies exact products, and viewing them as modules on a trivial one-object site meets the general tool's codomain hypothesis.

For Steps 3 and 4 I opened the full statements of `lem-weil-strict-roos-comparison`, `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, and `lem-cbc-exact-product-functor-strict-limit`. The first supplies strict-map descent and the zero-shifted-coordinate normalization; the second identifies total derived limit on strict towers; the third specifies the comparison on both coordinates and identifies it with comparison of the entire resolved ordinary limit cone. I checked the coordinate conversion against both displayed differentials. In particular the argument uses the generic tool's statement, not anything hidden in its proof. Both exactness and invertible canonical product comparison have already been checked before applying it. The formula for zeta is the inverse of the sections comparison, with the displayed source and target.

For Step 5 I read the complete statement of `lem-trf-point-system-transport-descent`: it supplies an actual strict chain map, compatibility with the actual transitions, and its derived localization, not just a list of evaluated maps. Together with strict Roos naturality it justifies the stated identification with Rlim(I). The equation with 1-s and the cone differential are calculated coordinatewise in the proof. This does not appeal to detection of equality by derived evaluations.

For Step 6 I checked the actual restriction/insertion/sheafification formula in `def-weil-frobenius-point-transport`, the reindexing statement, the matching recipe clause of transport descent, the scalar identities in the inverse-image comparison, exact sections, and the localization definition in `def-weil-abstract-derived-category`. The explicit restriction identity for a sheaf morphism proves naturality, also for differentials. Constant R-linearity is checked after all finite coefficient projections. These checks justify applying the formula to the whole cone and to its derived realization, without assuming either object is complete or constructible.

For Step 7 the only inputs beyond the preceding steps are the descent statement's formula for the components and the product theorem's sectionwise assertion. I checked the two actual coordinates: both constructions send them to the tuple of restricted sections, followed by the same finite-level j maps. The result is equality of chain maps into the entire cone. There is no assertion that agreement of derived level projections determines a derived morphism. For Step 8 I checked the directions of theta, eta and both kappa maps; substituting Step 7 cancels the sections comparison and naturality of sigma gives exactly the displayed derived identity. Strict Roos and point transport descend, and naturality extends over formal inverse quasi-isomorphisms by the definition of the derived category. `citations.json` quotes actual statements for every cited step/node pair, checked as literal substrings.

I tested the formulas on the zero tower, on towers with zero transitions (s=0 and Cone(1)[-1] acyclic), and on the constant identity-transition tower with its zero-shifted-coordinate augmentation. The coordinate conversion and the comparison commute in every case. Zero-transition towers also check that cartesianness has not slipped in. Negative and arbitrarily unbounded cohomological degrees cause no extra totalization: every formula is termwise in a fixed degree with the same countable products. No step exceeds 2000 characters and no comparison lemma is hidden in a long step. There is no new node restating a clause of the item: the eight steps carry the compatibility calculation themselves. Off-unit statements are explicitly declared as generic tool uses with their limited purpose in `split_report.tool_uses`.

## Validation

The server `review_split` check passed before this report was finalized. The required delivery dry run and final push are performed after writing the report.
