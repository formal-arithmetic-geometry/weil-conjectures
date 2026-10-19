# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-sf-etale-generic-direct-image-exchange.json`: statement, split; five proof steps, no Mathlib match.
- `citations.json`: verbatim statements of every cited node, indexed by proof step, so the precise clauses remain visible in context.
- `report.md`: this report and author's mathematical review.

There are zero new nodes and zero Mathlib leaves. `prepare.py` is a sandbox-only preparation script; `searches.jsonl` is the search command's own log. Neither is a DAG delivery file.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` both for the item's blueprint tag/id and the generic/direct-image/exchange notions. No declaration supplies this complete ordinary-etale constant-module statement. The upstream master checkout is not treated as evidence of a finished proof. No Lean was written or compiled.

## WANTED

None. The item follows archived Stacks sources plus the existing DAG's coefficient-comparison and exchange-pasting tools; no SGA source is used.

## Corrections and findings

The item statement is unchanged. Its source correctly points to 0F09 and 0F1C, but neither alone is the geometric-generic, constant-module statement: the generic projection is a limit over affine open neighbourhoods, and the abelian comparison must be transported to the actual unbounded module adjunction mate. The split supplies those steps instead of silently identifying the coefficient categories or endpoint isomorphisms.

The current main-20261015 blueprint puts the ancestor in `sec-six-functors-basics/sk-prop-sf-biduality-general/`, rather than the older `sec-six-functors/` location. I read both the current geometric-biduality proof paragraph 4 and the current geometric-generic-exchange proof's first paragraph. The item realizes that direct-image generic-restriction argument through existing 0F09 and arbitrary-field-extension tools. The unit has no enumerated proof steps and this item is not its key statement, so no unit realization fields are edited. Historical blueprint ancestry is preserved.

The curve need not be separated: smooth integral finite-type curves include the affine line with doubled origin. Step 2 establishes quasi-separatedness from local Noetherianity and uses no separatedness. Similarly, neither h nor its base changes are assumed proper or separated. The fact that finite A is killed by a unit N gives uniform invertible torsion, without requiring constructibility, boundedness above, or finite Tor amplitude of E.

## Unfinished work

None in this one-level split. The cited statements remain independent DAG tasks; their proofs are not replaced or claimed to be complete here.

## Not duplicates

No new node is proposed. Whole-DAG searches by 0F09, 0F1C, generic fibre, function field, local-ring affine-neighbourhood limits, module/abelian exchange and pasting were read. `tools/blueprint_refs.py search` was run for generic direct image exchange, generic direct, generic exchange, fraction field, and limits of affine schemes, and the item's ancestor was checked. The existing `lem-kun-0f1c` is an endpoint assertion; the stronger existing `lem-kun-0f1c-exchange` explicitly identifies the canonical map and is the one cited. `lem-weil-geometric-generic-exchange` assumes a particular base k and bounded constructible inputs and gives additional exceptional/Hom clauses; it does not state this arbitrary-F, arbitrary-D+ item. No new copy of either is made.

## Mathlib searches

Retained the inherited search records and appended the five actual Q144 searches from `searches.jsonl`. Read every hit. The first semantic query returned etale algebra maps and scheme etale stability, the second returned smooth algebra/scheme stability, LeanSearch returned etale algebraic base-change results, Loogle returned ordinary tensor-product scalar extension, and the geometric-generic/baseChange grep found no hits. These are not the derived-etale exchange theorem. Both semantic phrasings were tried before concluding no match. All services returned successfully. No search was invented and no unavailable response was called a negative result.

## Review by Q144

I read Stacks `etale-cohomology.tex`, labels `lemma-smooth-base-change-general` (0F09, lines 17975 onward) and `lemma-base-change-field-extension` (0F1C, lines 18032 onward), including both proofs. The former requires a directed limit of smooth stages, affine transitions, qcqs f, and bounded-below invertible-torsion abelian cohomology. The latter is for an arbitrary field extension and qcqs morphism, with the same torsion/boundedness condition; its perfect-closure reduction handles inseparability. Those hypotheses are retained rather than replaced by algebraic closedness of F or L. There are no new nodes whose sources need separate verification.

Step 1: I read the complete statements of `lem-sc-integral-function-field-affine-fraction` and `lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods`. The former supplies the generic point in every nonempty affine open and the fraction-field identification through the germ map, not just an abstract isomorphism of fields. The latter supplies the nonempty directed set, affine transitions and the limit cone with its maps to B. I also read `morphisms.tex` label `lemma-integral-scheme-rational-functions` (01RV), including its integral-field conclusion, and `limits.tex` label `lemma-morphism-glueing-near-closed-point` (0GWT), whose proof explicitly states the local-ring spectrum limit over affine neighbourhoods, together with the affine limit lemma 01YW. I use the local-ring limit fact, not the closed-point hypothesis of the separate gluing theorem. Identifying Q via its localization map makes the generic projection independent of the chosen affine chart. No extra geometric lemma is hidden in that last identification.

Step 2: I read every cited statement. `lem-weil-pbc-finite-type-over-noetherian` applies to B over the Noetherian field spectrum; a field is Noetherian since it has just the zero and unit ideals. `lem-weil-pbc-locally-noetherian-quasi-separated` supplies exactly quasi-separatedness, with no separatedness. The local-ring-limit node supplies affine qcqs U_i. Clause (1) of `lem-weil-pbc-qcqs-morphism-permanence` makes U_i to B qcqs from their quasi-compactness and B's quasi-separatedness, and clause (3) preserves it under pullback. `lem-pc-open-immersion-smooth-composition` is applied to the identity, which is smooth directly: an identity is finitely presented and a lift across a thickening is the already specified structure morphism. Clause (2) of `lem-pc-proper-base-change` supplies only smooth base-change stability; its proper clause is unused. Finally I checked the exact hypothesis of `lem-weil-pbc-limit-fibre-products`: its three systems are respectively constant Y, constant B, and U_i, all transitions affine. It gives Y_Q as the limit and the affine transition maps. I do not use its additional residue-field clause. This step provides the actual system over Y required by 0F09, rather than applying 0F09 to h as though its target were B.

Step 3: I read the entire statements of `lem-kun-0f09`, `lem-kun-unbounded-exchange-agrees`, and `lem-kun-unbounded-abelian-exchange-comparison`. The first states the canonical bounded-below abelian exchange, with the additional qcqs-stage condition met by step 2. The second explicitly compares that canonical map with the unbounded abelian mate. The third provides exact conservative coefficient forgetting, cohomology comparison, inverse/direct-image endpoint isomorphisms and the equality identifying the actual forgotten module exchange. Thus it is not merely an isomorphism between endpoints. The NA=0 hypothesis makes every cohomology stalk N-torsion; the inverse of N in F maps to all Y section rings. The input remains bounded below after forgetting. No constructibility, finiteness of the module stalks, or boundedness above is used. The argument concludes an isomorphism of the original module arrow by conservativity, exactly what the cited statement says.

Step 4: I checked clause (3) of qcqs permanence on h_Q and the exactness clause (3) of `prop-weil-pbc-inverse-image-modules-exact`. Exact inverse image preserves the lower cohomological bound and the A-module annihilator. I read the canonical-map statement of `lem-kun-0f1c-exchange` and checked each hypothesis with K=Q and the given extension L/Q. N is a unit in Q. Its statement does not assume a separable extension, algebraically closed starting field, or constructible E. The same explicitly cited unbounded-comparison and coefficient-forgetting identities therefore transport this particular exchange map to modules. This uses the statements, not an unpublished construction from their proofs.

Step 5: I read the full typed equality in `lem-fin-module-exchange-composite-base-change`. Its orientations agree with Y_L to Y_Q to Y, and the same on T. It applies to any commutative coefficient ring and unbounded module complexes. Its endpoint composition isomorphisms are exactly those required in the item's compatibility clause. The remaining deduction is elementary: a functor sends an inverse to an inverse, and the composite of two isomorphisms has the reversed composite of their inverses. This establishes both the isomorphism and equality with the stated canonical composite.

I checked small cases: N=1 forces the zero coefficient ring and zero module categories, for which the argument still applies; E=0; T empty; h an identity; h an open immersion; a nonseparated doubled-origin base B; and characteristic p with L/Q containing purely inseparable p-th roots. Nothing in the proof excludes these cases. The source extension theorem is specifically what covers the last case. The finite/algebraically-closed/dimension-one assumptions are allowed to be stronger than the generic tools require; none is added, removed, or altered in the item statement.

Against B--E of delivery-errors: no new statements or elementary/duplicate/clause nodes are created; the item has self-contained existing notion dependencies; each non-elementary step cites statements which explicitly contain what it uses; no SGA route is cited; proof_deps is exactly the union of uses; all off-unit geometric/coefficient/base-change black boxes are declared in split_report.tool_uses. I walked the complete statement/proof dependency closure of each proposed tool and found no path back to the item. Every proof step is shorter than 1,200 characters, so there is no step over the 2,000-character review threshold. The only repairs during drafting were making the base of 0F09 explicitly Y (with pulled-back stages), and selecting the canonical-exchange version of the field-extension node rather than the endpoint-only version. No source or item statement dispute was found.
