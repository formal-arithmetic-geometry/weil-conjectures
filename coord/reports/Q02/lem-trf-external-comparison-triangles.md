# Stage-1 delivery: lem-trf-external-comparison-triangles

Group Q02; 2026-10-17; direct delivery under the dispatched brief.

## Files written

- `dag/nodes/sec-six-functors/lem-trf-external-comparison-triangles.json`: statement, split into eight proof steps; no Mathlib match for the geometric composite.
- `citations.json`: 22 verbatim statement excerpts, one for each step/dependency pair.
- `searches.jsonl`: five actual msearch.py calls, with their returned results inspected. The item's inherited searches are retained and are distinguished from this run's appended searches.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. No unit file changed: this item is an auxiliary child of the unit's key node. The imported statement and its statement dependencies are unchanged.

## Attachments

No attachment for the item. Searches for its exact blueprint tag and for external comparison/projection names in `WeilConjectures/` found no declaration stating all its clauses. In particular, `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`, `SixFunctors/Etale/Derived/Kunneth/Relative.lean:102`, has a sorry proof, requires finite invertible-exponent coefficients and constructible finite-Tor objects, and asserts an object isomorphism. It does not prove this arbitrary-ring triangle/shift compatibility.

I also read `CategoryTheory/Adjunction/ProjectionMapShift.lean`: its generic right-adjoint projection theorem assumes the tensor comparison and tensor-counit shift compatibilities. It is useful implementation material but is neither the item's geometric assertion nor a reason to claim an attachment. `CategoryTheory.NatTrans.mapTriangle` in `Mathlib/CategoryTheory/Triangulated/Functor.lean:36` states the generic construction once shift compatibility is supplied; the proof below supplies that compatibility for the specified map.

## Literature needed

WANTED: none.

## Audit findings and repairs

The item was an unsplit statement with an empty proof and no local Lean audit. I retained the statement, filled its argument, and preserved its original creation/provenance fields. Its blueprint ancestry already identified the precise parent sentence, so that field remains unchanged. The chapter and unit were read, including the unit's displayed exchange/projection route. The proof realizes the parent's assertion of exactness in Q; it does not derive or rely on the parent's coefficient-transport argument or Kunneth invertibility.

The essential distinction is that the exchange is evaluated at the fixed L, so it is a fixed derived morphism e, independent of Q. Shift compatibility in Q therefore needs naturality of second-variable tensor shifts with respect to e, not a theorem about shifting the input L of exchange. The proof retains the final inverse-image composition map rather than suppressing it: its own termwise shift identity is written out in Step 6. Output categories remain unbounded throughout; no unjustified cohomological dimension or boundedness assertion is used.

The DAG and whole blueprint were searched by tensor/shift, external comparison, triangle compatibility and projection wording, and DAG searches by 07A4, 06YU and 0B56 were read. This located the existing general `lem-weil-pbc-ringed-projection-mate-exact`. I reused it instead of creating an etale special-case copy. `lem-sf-finite-exchange-projection-commshift` concerns compact-support functors and finite pro-etale coefficient stages; `lem-sc-projection-comparison-exact` concerns proper Noetherian scheme structure-sheaf categories; neither supplies this item's ordinary etale map with arbitrary A. `lem-etale-projection-formula-triangle-closure` asserts only closure of the isomorphism locus and was not used as a shift theorem. `lem-weil-pbc-derived-exchange-triangulated` is bounded-below abelian-sheaf exchange; it was not silently specialized to the unbounded module setting.

Actual Mathlib searches in this sandbox comprise LeanSearch, Loogle, grep and two differently phrased LeanFinder queries. All returned successfully. LeanSearch returned ordinary linear-map base-change results; the first LeanFinder returned Ext/Tor/localization results, the second triangulated-adjunction and spectral-object APIs; Loogle returned the CommShift unit/counit and constructors. I read the adjunction shift API in Mathlib/CategoryTheory/Shift/Adjunction.lean and the triangulated adjunction API, as well as the project's projection-map theorem. None states this composite as an exact shift-compatible geometric transformation. The grep had zero hits in Mathlib/CategoryTheory. Queries and returned names are recorded exactly; no additional searches are claimed.

## Incomplete work

None within this one-level split. Existing unsplit dependencies remain their owners' work. No Lean files were written and no compiler, Lake, library check or local preflight was run. Server preflight and push results are recorded below after the required delivery commands finish.

## Not duplicates

No new node was created. The generic ringed-topos projection-mate node is cited directly, so no duplicate-pair justification is needed.

## Review by Q02

I read the item's source `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-lem-sf-kunneth-star/lem-trf-ordinary-kunneth.proof.md`, its displayed comparison and Step 2's exactness sentence, against the node. The present assertion is the triangle/shift detail used by that sentence, not the source's stronger invertibility claim. I read the actual Stacks TeX at sites-cohomology.tex labels definition-derived-tor (06YU), lemma-pullback-tensor-product (07A4), lemma-adjoint (07A6), equation-projection-formula-map (0B56), sites-modules.tex lemma-push-pull-composition-modules (03D8), and derived.tex definition-triangle (0144), definition-exact-functor-triangulated-categories (014V), lemma-composition-exact (014Y). The projection-formula paragraph explicitly constructs the map without extra assumptions by adjunction; only its later invertibility lemma requires perfectness. I use the former. There are no new-node source statements to review.

For Step 1 I opened the statements of inverse-image-modules-exact, exact-functor-derived-factorization and exact-functor-derived-functor. The first gives the canonical constant-ring identification and exact module pullback, the second gives a triangulated termwise factorization with the identity shift on complexes, and the third identifies it with derived pullback. Thus the ringed-topos specialization uses the same category, ring and shifts; no coefficient-category identification is merely assumed.

For Step 2 I read the statements of prop-pur-kinjective-resolutions-exist, lem-pc-right-derived-functor-triangulated, lem-kun-derived-tensor-triangulated, lem-weil-pbc-triangulated-functor-composite and def-weil-pbc-derived-categories. Their conclusions respectively supply all-complex resolutions on small sites, unbounded right-derived exactness for additive functors, exactness in either tensor variable, the exact composite with its shift, and D+ as a strictly full triangulated subcategory. Direct image is additive and small representatives are an explicit hypothesis, so the resolution hypotheses hold. The direct-image theorem is general for abelian categories, despite its filing under Picard framework: it does not assume properness or quasi-coherence. Restriction to D+ is in the source only; the target stays unbounded.

For Step 3 I checked the statements of def-kun-unbounded-exchange, def-kun-projection-formula-map and lem-weil-pbc-inverse-image-composition-module-linear. These actually give the exchange arrow U to Rh_*E, the ordinary projection mate, and the natural A-linear composition isomorphism in the needed direction. The factors have codomains H, J and G as displayed. Factoring alpha is a direct reading of the specified composite, not a new lemma or a change of comparison.

For Step 4 I read def-kun-derived-tensor's direct-sum differential and lem-weil-pbc-site-derived-tensor-descent's bifunctor and natural-transformation descent statements. The second-variable shift has sign (-1)^p in first degree p. A degree-zero chain map preserves p, so the two composites agree term by term. Composition and inversion preserve that equality, and the cited equivalence with the localization of K-flat flat-term complexes covers every derived morphism e. This is the elementary sign calculation needed here, rather than an unsupported assertion that the connecting maps commute.

For Step 5 I opened the entire statement and proof of lem-weil-pbc-ringed-projection-mate-exact and the projection-map definition. The former explicitly asserts naturality, exactness and the canonical shift equation for the map adjoint to (epsilon_E tensor 1) mu. The latter uses exactly that adjoint map. The constant A ringed sites of h meet its hypotheses by Step 1. No properness, finite coefficient, perfectness or finite-Tor assumption is needed. I checked that the tensor comparison is in the same direction in both statements. The comp-whisker node's part (iii) gives the exact precomposition with p_Z'^*, including its composite shift, rather than a different shift chosen just to make the map commute.

For Step 6 I reread the module-linear composition node: it gives a natural isomorphism on module sheaves, so the component in degree q after a shift is literally its original degree q+1 component. Exact-functor-derived-factorization supplies the same shifts on localization. The tensor-descent node justifies checking the two signed composites on representatives; the equation applies c only to the second factor, so its degree-zero component commutes with (-1)^p. The comp-whisker node's part (ii) then applies to Rh_*. Naturality follows from the same cited functors. No theorem about comparing arbitrary derived pullbacks is hidden here: both relevant inverse images are exact and termwise.

Step 7 is the written composition of three established equations, using comp-whisker part (i). Step 8 uses the definition of a triangle morphism from def-weil-triangulated-category and explicitly writes the equality for the connecting arrow w. Its first equality is Step 7 and its second is naturality at w. These steps do not invoke TR3 to obtain an unspecified third component.

I checked B--E against these files: no new statements or hollow definitions, no restatement nodes, every non-elementary input has its own cited statement, and the 22 quotes in citations.json are literal substrings of those statements. Each step is under 1,000 characters, so there is no step over the 2,000-character review threshold. The elementary steps are the displayed factorization, the two degreewise sign identities and their cited localization, the composition identity, and the connecting-square identity. Generic tools outside the unit are declared in split_report.tool_uses; none replaces the unit's geometric Kunneth route.

As small-case checks I considered Q=0, L=0, f=id and an empty scheme, for which all constructions and equations remain defined. Taking A=Z and a non-flat Q changes no argument: all tensors are derived and the unbounded projection-mate theorem applies to arbitrary inputs. Taking Q a single sheaf shifted by one makes the (-1)^p sign visible; both sides have that same sign. An identity exchange reduces the first factor to an identity, but the proof does not require exchange or projection components to be invertible. The bounded-flat hypothesis on L is retained although these formal compatibilities work more generally. There is no statement dispute and no source-route correction in this delivery.

## Delivery validation

The first dry run exited before server preflight because six verbatim citation excerpts were shorter than the delivery checker's 40-character minimum. Expanded those excerpts to include the surrounding substantive clauses; the node and proof needed no mathematical change. The next dry run checks these repaired citations.
