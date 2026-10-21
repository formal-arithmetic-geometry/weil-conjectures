# NJ: lem-sfb-supported-finite-stage-topology-defect

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-supported-finite-stage-topology-defect.json`: item split into eight steps; original statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-norm-algcl-internal-hom-base-change.json`: statement-only structural input, unsplit; no Mathlib match. It concerns an isomorphism of derived internal-Hom sheaves, not supported Hom groups or scalar-unit cones.
- `dag/nodes/sec-six-functors-basics/lem-sfb-norm-algcl-cohomology-topology-comparison.json`: statement-only structural input, unsplit; no Mathlib match. It concerns the actual map on derived global sections of finite-field constructible complexes, not a sheaf-level equality or a supported Hom comparison.
- `citations.json`: every step/use pair, quoting the full actual statement of the cited node verbatim. Full statements are retained to show all hypotheses, not merely matching keywords.
- `searches.jsonl`: actual msearch command records, reused without inventing queries or hits. `write_split.py` is the item-local authoring script.

## Attachments

None. Searches of the live project under `lean/WeilConjectures/` for the blueprint tag and coefficient-topology/finite-stage/scalar-unit notions did not reveal a sorry-free project declaration proving all clauses. The parent comparison placeholder is not an attachment. No Lean was changed or compiled.

## Missing literature

WANTED: an exact published proof of derived internal-Hom base change from a finite l-adic field to the norm-continuous, non-completed algebraic-closure coefficient sheaf, for `lem-sfb-norm-algcl-internal-hom-base-change`.

WANTED: an exact published proof of the derived global cohomology comparison from finite-subextension-valued to all norm-continuous algebraic-closure coefficients on finite-field constructible inputs over the stated arbitrary positive-characteristic field, for `lem-sfb-norm-algcl-cohomology-topology-comparison`.

These are explicitly unproved new nodes, not claims that the missing literature was read. Their source fields name the agent-created obligation in paragraph (3) of the current blueprint direct-image proof. I read that paragraph, Hemo–Richarz–Scholbach's coefficient discussion, Lemma 5.6 and Lemma 7.9, and Bhatt–Scholze's continuous coefficient discussion (4.2.12) and finite-subextension passage (6.8.2). HRS gives the colimit-topology algebraic closure, not the norm-topology replacement. Neither paper passage was used as evidence of the new assertions. Generic derived-Hom/global-section constructions were checked in Stacks `sites-cohomology.tex`, Tags 08J9 (`lemma-internal-hom`) and 08JA (`lemma-section-RHom-over-U`). No SGA route is used.

## Problems found and scope

The imported item has no supplied proof, and its source explicitly says the exact topology comparison is wanted. I have not changed its statement. In particular I did not replace B with the completion, identify B with C, assume scalar flatness, restrict the base field's cohomological dimension, or make the two supports or coefficient fields equal. The blueprint ancestor command returns a null ancestor along the inherited agent-created chain; the existing `from.node: null` is retained and each new node prepends the item to `via`. Whole-blueprint keyword searches found no exact equivalent (`same_as: []`).

The split proves the item conditional on the two explicitly open structural inputs and the existing DAG statements. It does not complete those structural inputs or assert an unconditional library proof. Both are statements about derived objects, rather than disconnected degreewise cohomology assertions. No per-degree auxiliary node is introduced: the final Hom groups arise by applying cohomology to the stated derived maps.

## Not duplicates

lem-sfb-norm-algcl-internal-hom-base-change vs lem-sfb-qlbar-internal-hom-coefficient-comparison: the existing coefficient is the finite-subextension colimit C and it assumes filtered-colimit continuity; the new statement concerns the distinct norm-continuous B and finite-field constructible arguments. The existing theorem cannot be applied with B substituted for C.

lem-sfb-norm-algcl-internal-hom-base-change vs lem-sfb-supported-finite-stage-topology-defect: the new statement compares local derived internal-Hom sheaves after E-to-B extension; it contains neither global sections, C-to-B scalar unit, supported generators, nor cone vanishing. The item's proof additionally needs a separate global comparison and the canonical-map argument.

lem-sfb-norm-algcl-cohomology-topology-comparison vs lem-weil-pbc-comparison-global-cohomology: the latter compares etale and pro-etale sites with finite discrete coefficients; the new statement fixes the pro-etale site and changes the algebraic-closure coefficient topology.

lem-sfb-norm-algcl-cohomology-topology-comparison vs sk-prop-sf-comparison: the latter is an etale/pro-etale site comparison, not the map induced by C-to-B.

lem-sfb-norm-algcl-cohomology-topology-comparison vs lem-sfb-supported-finite-stage-topology-defect: the new statement has one finite-field constructible argument V and compares its scalar-extended global cohomology. It has no pair of supported objects or internal Hom. The proof must first establish that V=RHom(K,N) is bounded constructible, compare the two internal Homs using separate inputs, and identify the unit map. Thus it is not the item restated as a cone assertion.

lem-sfb-norm-algcl-cohomology-topology-comparison vs lem-sfb-constructible-algcl-topology-comparison: the parent asserts a categorical comparison and depends on this item. It is not cited, avoiding the circular route through the parent and proper/open scalar-comparison nodes.

The whole DAG and blueprint were searched for both proposed ids, internal-Hom scalar/coefficient comparisons, and global cohomology/topology comparisons before creating either node. No Stacks tag is claimed as a source for either special new assertion; there are therefore no new same-tag duplicate pairs. Generic Stacks facts are cited through existing nodes instead of recreated.

## Review by NJ

I checked B–E against the actual node statements and the literature listed above. Both new nodes introduce ell, k, X, Omega, E, their three coefficient sheaves, the module categories, and the actual maps. They contain no proof or proof dependencies. Their statements distinguish the finite constant local model convention from an undefined general constructibility notion. The new maps are in derived categories, have explicit evaluation or K-flat normalizations, and make no assertion of coefficient flatness or completeness. Mathlib searches were made with the command: each new node has LeanFinder in two phrasings, Loogle, LeanSearch, and source grep. I read the hits: ordinary linear dual base change, LightCondensed internal Hom, discrete representation cohomology and PadicAlgCl normed-field definitions do not state the required pro-etale comparisons. Failed exploratory searches (an unknown Loogle identifier and a redundant Mathlib prefix in a grep subdirectory) were not used as evidence of absence; corrected searches are in the log and node records.

Step 1 uses the actual exact monoidal equivalence statement of `lem-pd-module-ringed-topos-derived-comparison`, and separately the actual scalar-adjunction compatibility in `lem-sfb-internal-section-scalar-adjunction`; the first alone would not justify identifying scalar units. Closed internal Hom follows by uniqueness of right adjoints to the identified tensors. The two Noetherian nodes say precisely that finite type over a Noetherian base is Noetherian and that its opens are quasi-compact. The field and quotient-ring checks are written out. All sites use the standing small coefficient-universe representatives.

Step 2 uses the compositum clause of `det-def-sfb-qlbar-condensed-subextensions`, exactness from `lem-sfb-subfield-flat`, and the inverse-image tensor comparison from `lem-sfb-kflat-scalar-comparison-normalization`. On the trivializing covers the extended modules are finite free of the same ranks, so they meet the lisse hypothesis of `lem-sfb-coefficient-heart-lisse-extension-constructible`. That last node actually asserts bounded constructibility of the locally closed extension; it is not merely a definition of constructibility.

Step 3 reads the normalization clauses of the open tensor comparison and the closed supported scalar comparison. I checked the latter's unbounded-calculus hypothesis instead of citing a bounded-below recollement theorem as if it were unbounded: the exact sheaf functors and the degree-zero recollement triangle supply the required short exact sequence, mixed restrictions vanish by their supports, and then `lem-sfb-exact-open-closed-unbounded-calculus` applies. Quasi-compact complements were established in step 1. The closed comparison retains the new coefficient action, avoiding an unsupported identification merely after forgetting coefficients.

Step 4 uses the actual reassociation and composite-unit formulas in `lem-sfb-successive-derived-quotient-normalization`, not a flatness assumption. This gives the four objects needed later and preserves the scalar-unit normalization even when E and F differ.

Step 5 uses `lem-sfb-dc-hom-preserves` only at the finite field E0, not at B. It provides the bounded constructible D needed by the new global theorem. The continuity node has exactly the common-lower-bound filtered-diagram condition required by the existing E0-to-C internal-Hom comparison. K has the finite constant local model and N is degree zero. B is handled only by the new local comparison node. I did not use the parent's full faithfulness, proper scalar comparison, or an open scalar comparison depending on them: that would create a dependency cycle.

Step 6 applies the new global statement to D, whose hypotheses are now checked. The comparison is the actual c-induced map. The two evaluation transposes give the same scalar-extended evaluation after tensor reassociation; uniqueness of transpose shows the map on morphisms is J(u). The cited derived internal-Hom sections model actually supplies H^n RGamma(RHom)=Hom(-,-[n]), without boundedness or flatness assumptions. It is not an appeal to fully faithful Yoneda in place of the required global-sections formula.

Step 7 uses the normalized unbounded extension/restriction adjunction statement: its unit is the prescribed one, and naturality gives UJ(u) eta_G=eta_H u. Exact termwise restriction and the derived scalar functor commute with shifts, so these are precisely the maps into the shifted second triangle vertex. Step 8 uses the exact Hom assertion on the given shifted and rotated triangle. Injectivity in degree n+1 kills the boundary; exactness lifts to the middle vertex; surjectivity in degree n makes the lift factor through eta; consecutive arrows kill it. This proves zero for every cone triangle, not just for a preferred representative.

For small cases I checked zero complexes, empty X, empty supports and rank-zero modules: all tensors and Homs occurring there are zero and the argument needs no exception. Over a separably closed point with trivial finite-rank local systems, the local map is the finite-free matrix Hom comparison, and the global map on degree zero is the identity on Omega; this does not pretend that C and B are identical sheaves on all profinite sets. In particular norm-continuous maps on a convergent profinite sequence can have image in no single finite subfield, so no argument uses such an identification. Shifts of arbitrary sign are allowed because all ambient categories and the two new inputs are derived statements. These tests are consistency checks, not proofs of the two remaining structural inputs.

All eight steps are below 2000 characters. Their routine local free calculation, adjunction-transpose equality, and exact-sequence argument are written as steps rather than new nodes. Off-unit generic tools are individually declared in `split_report.tool_uses`: they supply coefficient/module models, unbounded scalar adjunctions, support comparisons, Noetherian facts, internal-Hom continuity and global sections, not an alternative direct-image proof route.

## Unfinished work

The two new structural statements remain unsplit by the one-level stage-1 contract. Their exact external references are missing as described above. No claim of Lean completion is made. The required server dry run and delivery are recorded by the delivery command's result.
