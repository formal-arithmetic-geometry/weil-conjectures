# Worker report: lem-sfb-space-etale-pull-push-retract

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-etale-pull-push-retract.json`: statement, source and statement dependencies preserved; five-step split with existing inputs, Mathlib no match.
- `citations.json`: a verbatim statement quotation for every node cited in each numbered proof step.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

New nodes: 0. New Mathlib leaves: 0. There was no earlier sandbox item, proof or report to repair.

## Attachments

None. Searched the actual live `lean/WeilConjectures/` for the item id, `etale-pull-push-split`, `0HAP`, pull-push splitting/retraction and counit-splitting names. No project declaration states this algebraic-space small-etale structural-module result. The scheme or constant-coefficient counit declarations returned by concept searches do not supply it.

## WANTED

None. All sources used are in the read-only repository.

## Findings and proof route

The statement is correct as imported and is unchanged. The proof now uses the existing ordinary etale module restriction/base-change interface, the existing open-and-closed diagonal lemma, and a sectionwise construction. The section is the input section on the graph and zero on its complement. Its restriction to the graph is the given counit, as follows from the adjunction triangle and the normalized chart-unit tensor formula. We do not introduce a node for elementary gluing on two disjoint opens or for linearity/naturality of that explicit map. Nor do we move the conclusion into an auxiliary splitting lemma.

Read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-thm-sf-ctf-stability.json`, and the current blueprint proof at `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/thm-sf-ctf-stability.proof.md`. This item is the Tag 0HAP input to Tag 08IL recorded in the imported helper chain; it is not the unit's key theorem. The ancestor tool returns `None`, so the existing `blueprint.from.node = null` and complete via chain are retained. Searches of the whole DAG and blueprint for `0HAP`, `etale pull`, `direct summand`, `counit`, the base-change, diagonal and clopen-module concepts found reusable inputs but no blueprint statement equivalent to this item. Thus `same_as` remains empty. No chapter/unit file or route is changed.

## Source error

Stacks `spaces-cohomology.tex`, Tag 0HAP (`lemma-etale-pull-push-split`), invokes `lemma-affine-base-change` (Tag 07U8) in its first proof sentence. Its hypothesis only says quasi-compact separated etale, which does not imply affine. For example the quasi-compact open immersion A^2_k minus the origin into A^2_k is separated etale and is not affine. The equalizer computation on D(x), D(y) gives global functions k[x,y], and if the punctured plane were affine its canonical map to Spec of its global functions would be an isomorphism, contradicting the missing origin. This is a proof-reference error, not a false conclusion or a disputed item statement.

The required comparison is exactly the degree-zero etale-base-change statement in Tag 03LX (`spaces-properties-lemma-pushforward-etale-base-change-modules`), together with Tags 03LV/03LW. It applies to arbitrary algebraic-space bases and arbitrary module sheaves. Our cited existing `lem-trf-space-etale-module-pushforward-restriction` says this, including the compatible-section formula. The existing flat-base-change node has scheme bases, and the affine-base-change node assumes an affine direct-image map; neither is silently used outside its hypotheses. The source's final omitted map check is supplied in step 5.

The reused diagonal node's source field lists Tag 03HK for its diagonal assertion. I also read Tag 05W1 (`lemma-diagonal-unramified-morphism`), which is the source explicitly stating openness for unramified maps, and checked that the used node's actual statement explicitly gives both open and closed diagonal for separated etale maps. Tag 03HK by itself lists representability, local finite type, monomorphism, separatedness and local quasi-finiteness, not openness. This source-pointer imprecision in the dependency is reported here; the dependency is not edited.

## Mathlib searches

Retained the item's existing searches and appended exactly the six searches run through the prescribed command in this sandbox: LeanFinder with the quasi-compact separated etale counit formulation and then the open-and-closed-diagonal retract formulation, Loogle `"pullback", "SplitEpi"`, LeanSearch with the direct-summand formulation, and the two grep patterns in the item/log. All services answered successfully.

Read the returned types and Mathlib `CategoryTheory/Limits/Shapes/Diagonal.lean` (the projection-splitting instances at lines 56 and 59), and `AlgebraicGeometry/Modules/Sheaf.lean` (pullback/pushforward adjunction at line 189 and the open-immersion restriction counit around lines 416-435). A splitting of a fibre-product projection is not a splitting of this module counit. The latter file concerns scheme Zariski modules and gives a counit isomorphism for open immersions; it is not the algebraic-space small-etale result for general etale f. The second LeanFinder phrasing yields scheme unramified-diagonal and quasi-separated section lemmas. Neither those nor the quasi-coherence constructors from LeanSearch state the item. No Mathlib leaf is claimed.

## Not duplicates

No new nodes, so no new/existing pairs. In particular we reuse `lem-sfb-space-separated-etale-diagonal-complement` and `lem-trf-space-etale-module-pushforward-restriction`. `lem-pur-clopen-ringed-module-gluing` was read but not cited: it is about schemes on the pro-etale site, and cannot be applied as written to the current etale algebraic spaces. The elementary two-open sheaf construction is written out instead.

## Review by Q62

I read Tag 0HAP in `spaces-cohomology.tex`, its purported affine-base-change input Tag 07U8, and the actual usable source Tags 03LX, 03LV and 03LW in `spaces-properties.tex`. For the diagonal I read Tag 03HK and Tag 05W1 in `spaces-morphisms.tex`. For the map normalization I read `sites-modules.tex` Tag 03D7 (`lemma-adjoint-pullback-pushforward-modules`). There are no new nodes to source-check. I opened and read the statements of every cited existing node, including the full canonical chart-adjunction tensor-realization statement, rather than borrowing anything from their proofs.

Step 1 uses `lem-trf-space-etale-module-pushforward-restriction` for precisely its canonical module comparison and compatible-section formula. Its hypothesis is an etale bottom map; our bottom map is f itself, so this applies with no affine, scheme-base, proper or Noetherian assumption. Its additional assertion that etale tensor pullback is restriction justifies evaluation on T regarded over Y. `lem-trf-space-fibre-products-etale-covers` supplies the self-product and its etale projections, and `lem-trf-space-enlarged-etale-ringed-site-model` supplies the equivalence and gluing of sheaves on space objects. These statements say exactly what step 1 takes from them.

Step 2 takes only the open-and-closed diagonal clause from `lem-sfb-space-separated-etale-diagonal-complement`; it does not use that node's later singleton-fibre assertion. Its hypotheses are separated and etale, both present. The graph is identified by the test-point equation x=u(t), not by an inference from underlying images. Pulling back this partition gives actual complementary open subspaces, not just a set partition.

Step 3 uses the sheaf property in `def-weil-sheaf-of-modules-category`, interpreted on the enlarged etale site as already justified in step 1. On each scheme chart it glues the restricted input and zero on a two-open disjoint cover. Their intersection is empty; uniqueness makes the local outputs a compatible family. This is the explicit elementary construction, not an invocation of a new general extension-by-zero theorem. No quasi-coherence assertion for the complementary module is needed in this construction.

Step 4 uses the same definition's linear-morphism criterion. I checked that the scalar action is via q, which equals the original action along the graph; the action off the graph is harmless because the section is zero. The graph pulls back to the graph for T', so uniqueness of the glued section proves naturality on every arrow, not just on an atlas. This gives a single sheaf morphism s_F.

Step 5 uses `def-trf-space-etale-module-functors` for the specified adjunction, chart projections and chart-unit formula. Applying the right triangle identity to an arbitrary m and then its identity-chart projection proves epsilon(1 tensor m)=that chart projection of m. `lem-trf-space-chart-adjunction-tensor-realization` explicitly states that in the etale case this tensor is identified with m, so we have calculated the original counit, not the counit of an arbitrary isomorphic adjunction. `lem-trf-space-etale-module-pushforward-restriction` identifies its projection with graph restriction. The constructed family has exactly the input section on that graph, proving the identity at every object. The triangle identity is part of the adjunction already cited, not a hidden additional theorem. There is no assumption that a general tensor section is globally pure: after etale restriction every m has the indicated representative 1 tensor m.

Small cases checked: X empty and zero F give the unique maps and the stated identity; for f=id the complement is empty and the section is the identity under the normalized comparison; for a clopen open immersion the same is true; for a finite disjoint-sheet etale cover the counit projects the product of stalks to the chosen sheet and the section inserts zero in the other coordinates. A non-surjective etale f causes no problem because every graph is defined over a chart of X; no chart over a missed point of Y is demanded. The non-affine punctured-plane immersion above is covered by etale base change, confirming the correction does not add an affineness hypothesis. The proof keeps arbitrary modules available in the construction and therefore certainly applies to the stated quasi-coherent F; it adds no coherence, finite presentation, Noetherian or finiteness hypothesis. Quasi-compactness is not needed by the stronger input, but is retained in the statement.

I checked delivery-errors B-E individually: self-contained unchanged statement and notion dependencies; actual logged searches; correct source tags/labels with the noted source-reference repair; no new duplicate, elementary or restatement nodes; no off-unit route replacement; every substantive input is a cited statement; all citations are quoted verbatim in citations.json. The four off-unit statements are declared in split_report.tool_uses as generic fibre-product/site/adjunction tools. No SGA is used. Every proof step is under 2000 characters, and the elementary gluing, scalar and restriction checks are all written explicitly.

## Unfinished work

None in the requested stage-1 split. No Lean was written or compiled. Remote dry-run and delivery results follow below when available.
