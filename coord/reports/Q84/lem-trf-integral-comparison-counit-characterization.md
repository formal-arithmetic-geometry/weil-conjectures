# Stage-1 delivery: lem-trf-integral-comparison-counit-characterization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-integral-comparison-counit-characterization.json`: split the item in six steps; no statement changes. Mathlib verdict: no exact or one-line match for the entire item.
- `citations.json`: twelve step/node entries, each with a literal substring of the current node statement.
- `report.md`: this report. The search command maintains `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag, whole-tower terminology and integral comparison/counit names. No project declaration states this item with all of its clauses. The existing abstract Mathlib adjunction is a tool rather than an attachment of the specified integral comparison.

## WANTED

None. The Stacks sources and current blueprint were available locally.

## Corrections and limitations

The imported statement is retained verbatim. Its strict family and counit are morphisms in the derived category of strict towers, and the argument never treats equality of separate derived projections as a test for equality there. No claim of invertibility of the integral comparison, nor independence of the K-flat resolution defining that comparison, is added: the item fixes that resolution. Resolution independence in the first assertion concerns the K-injective realization of total inverse limit.

The exact-product hypothesis of the existing strict Roos comparison must be checked, even though the general derived adjunction needs none. Step 4 supplies it using the existing pro-etale countable-products theorem, for the completed sheaf of rings, before using the product cone.

Nothing is unfinished. No Lean was written, and no compiler or local DAG/preflight tool was run. All writes are confined to the assigned sandbox.

## Sources and searches

Read `literature/stacks-project/derived.tex`, labels `lemma-pre-derived-adjoint-functors-general` (Tag 0FND) and `lemma-pre-derived-adjoint-functors` (Tag 0DVC), including the Hom-colimit proof and the functoriality assertion. Read `literature/stacks-project/sites-cohomology.tex`, `lemma-derived-limit-is-ok` (Tag 0941), including the choice of K-injective tower with injective terms and its ordinary-limit comparison. For the refined normalization use the full statement of the existing `lem-weil-strict-roos-comparison`, not an inference from projections. Read the specified comparison definition (b) in full, including its module action, quotient transitions, differential, and inverse of the resolution map. This is an agent-written specialization and calculation using these sources; `proof_origin.by` is `agent`.

Read the chapter and unit records, and the current main-20261015 blueprint proof of `thm-trf-l-function-euler-product`, Step 1, Global powers. This item serves the parent comparison-composition argument required for those powers. It is not the key statement of the unit, so no realization record is changed.

Whole-DAG and blueprint searches included the exact item id, constant towers, Roos, adjoint functors, inverse-image/pullback terminology, Tags 0FND/0DVC and the derived-adjunction names. Reused the existing general pre-derived adjunction and termwise homotopy adjunction, the ringed strict-tower derived-limit model, the normalized strict Roos comparison, and exact pro-etale products. No new lemma is necessary: constructing the ordinary limit adjunction and computing its counit are elementary steps, while all substantive localization and comparison theorems are existing citations.

Retained all inherited Mathlib search records and read the candidates described there. Ran additional logged LeanFinder, Loogle, LeanSearch and grep searches with the exact queries stored in `searches.jsonl` and copied to `mathlib_searches`. Different natural-language formulations were tried. Read Mathlib `CategoryTheory/Limits/HasLimits.lean:593` (`constLimAdj`) and `CategoryTheory/Functor/Derived/Adjunction.lean:143` (`Adjunction.derived`), including its additional absoluteness assumptions. Neither packages the K-injective tower normalization and the specified integral cone lift, so the item is not a Mathlib leaf. Other returned candidates are ordinary limits or different adjunctions.

## Not duplicates

No new nodes. Existing nodes are cited directly. The general derived-adjunction theorem is not reproduced as a new constant-tower theorem, and neither clause of the item is moved to a new node.

## Review by Q84

I checked the mathematical assertions against the sources and opened every cited node's statement. Step 1 uses the inverse-limit definition's existence and sectionwise compatible-family description; its universal property directly constructs both sides of the ordinary adjunction and the projection counit. The levelwise-abelian theorem explicitly gives levelwise kernels and cokernels, which makes the constant tower functor exact without a separate lemma. These are elementary constructions, not new unsplit nodes.

For Step 2, the termwise-adjunction node explicitly supplies the homotopy-category adjunction and its inherited counit. The ringed strict-tower node explicitly supplies total right derived inverse limit on the unbounded derived category and computes it by taking a K-injective tower resolution and ordinary limit. The pre-derived-adjunction node explicitly supplies the canonical Hom bijection and its functoriality for arbitrary localized morphisms. I verified the reversal of its A/B notation: its source A is our tower category, its B is our module category, F is limit and G is constant tower. Both are additive, the tower category is abelian by the cited levelwise theorem, and the small-site and ring hypotheses hold for R_X. Exactness makes LDelta equal Delta: the quasi-isomorphism diagram becomes a diagram of isomorphisms with the identity representative. This checks the derived-functor hypotheses instead of assuming that any pair of ordinary adjoints automatically derives.

For Step 3, I used the fraction formula actually stated by the pre-derived-adjunction node. At the chosen model RF(T)=lim J, choosing s=j and the identity t and f makes its representing comparison p_j the identity and the ordinary transpose e_J. Thus the image of the identity is [j]^{-1}[e_J]. Its stated naturality in the first derived variable gives the formula for every derived morphism. Its canonical character and representing-cocone functoriality identify the formula after changing resolutions; this is not restricted to strict chain maps.

Step 4 uses precisely what definition (b) specifies: the quotient tower, R_X-linear compatible maps theta_m, exact inverse image making g^{-1}(q) a quasi-isomorphism, and kappa as the cone lift followed by the inverse resolution map. The exact-products node explicitly allows every sheaf of rings on the small pro-etale site, including the completed coefficient sheaf, so the strict Roos comparison's exact-product hypothesis is met. The first, general adjunction assertion has no extra exact-product hypothesis.

Step 5 uses the inverse-limit universal property and the normalized Roos statement, which explicitly says that rho is C(j) followed by the inverse of the zero shifted-product inclusion i_J. The two-coordinate equation C(j) tilde-theta = i_J a is written out, and the subsequent cancellation is an equality in the derived tower category. It uses neither the proof of the cited Roos node nor a componentwise conservativity assertion. No auxiliary comparison theorem is hidden in the step.

Step 6 uses definition (b)'s exact specified kappa, then precomposes the equality with Delta of the inverse of g^{-1}(q). The previously established bijection proves uniqueness. The bounded constructible hypothesis is sufficient because every operation used is already defined in the ambient unbounded categories. No stronger torsion-freeness, exactness of inverse limit, or bound on the complex is assumed.

I checked zero source, zero tower, a constant tower, and g equal to the identity: zero families give zero maps, a constant tower gives the ordinary diagonal cone unit, and the identity scheme map still gives the completion comparison specified by the quotient tower, rather than an unjustified identity on a chosen chain model. The cone sign is checked using d(b,a)=(-db-(1-s)a,da): the zero first component is a chain map exactly because the theta_m commute with actual quotient transitions. A general tower need not have vanishing higher derived limit, which is why only the strict compatible family is lifted and no argument assumes exactness of ordinary limit.

I checked delivery-errors B through E: no new statement-only or notion nodes are needed; no fabricated search records; every proof citation has a verbatim quote; each non-elementary tool is cited for its actual statement; no proof-of-a-cited-node is used; no clause is relabeled as a new node. The off-unit tools are declared with reasons in split_report.tool_uses. Each proof step is under 2000 characters, and the explicit algebraic calculations contain no hidden source-standard lemma. I kept all existing metadata and the statement unchanged.

## Validation

The required server dry run is run after this report is written. Delivery and final validation results are reported by deliver.py.
