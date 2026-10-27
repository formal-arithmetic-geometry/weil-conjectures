# Stage-1 report: lem-route-sp-rational-twist-map-comp

## Files written

- dag/nodes/sec-proetale-coefficients/lem-route-sp-rational-twist-map-comp.json: statement; split into four short composition calculations using existing unique-map interfaces; no Mathlib match.
- citations.json: nine verbatim quotations, one per proof-step/node pair.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item is not the unit statement.

## Attachments

None. The project-source searches for the exact blueprint tag, declaration name, and rational/Tate twist composition gave no matching completed declaration in lean/WeilConjectures/. The actual item is AlgebraicGeometry.ProEtale.spRationalTwistMap_comp in lean/Sheaf/Paper/ProEtaleTateTwists.lean:370; its proof is sorry. The sorry-free coefficient inclusions in WeilConjectures/CategoryTheory/RingObjects/Condensed/FiniteSubextension.lean:101-105 prove a smaller fact already carried by def-sfb-qlbar-subextension-map; they do not prove this item.

## WANTED

None. The proof is explicitly marked agent-written: the latest blueprint gives the construction and the field colimit, while the SHEAF docstring supplies the composition sketch; neither is a human-authored proof of this precise declaration. No SGA source is used.

## Corrections and observations

The imported statement was a provisional signature wrapped with its proof sketch. I replaced that wrapper by a mathematical statement introducing all objects, including the positive indexing n+1 and the coefficient-first unbalanced tensor presenting extension of scalars. The hypotheses remain exactly those of the Lean signature: prime ell, arbitrary scheme X, and finite intermediate fields E <= F <= H. In particular I did not add invertibility of ell on X: local freeness requires it, but this composition argument does not.

The broad definition sk-def-sp-tate-twist currently reaches this item through lem-sp-ell-point-reduction-ring-map, so using it as a dependency would be circular. I instead introduce its finite, integral and rational constructions explicitly and cite the smaller existing definitions and four existing route uniqueness statements. The latter are currently provisional but their statements include the precise Lean existence/uniqueness formulas used here; their proofs are not being assumed finished. Their location in the purity unit is due to the first discovery of these route sorries. Four tool uses are declared for those interfaces, without replacing this unit's route.

A tempting citation lem-sfb-subfield-coefficient-map-comp only compares a finite-field map followed by inclusion into Qbar. I did not cite it for composition through three finite fields. Instead def-sfb-qlbar-subextension-map explicitly states strict functoriality of the condensed inclusions, and sk-def-sfb-pulled-back-coefficients explicitly says their pullback is a functor.

Nothing remains unfinished in this one-level split. The existing unsplit dependencies remain separate stage-1 items.

## Not duplicates

No new nodes were created, so there are no new/existing pairs. I searched dag/nodes for spIntegersMap, spEllMap, spIntegralTwistMap, spRationalTwistMap and the root/finite-twist concepts, and read the four unique-map nodes found in sec-smooth-purity. Whole-blueprint searches with blueprint_refs.py for 'twist', 'field-extension transitions', and 'transition maps' found the construction unit and related comparison nodes, but no separate statement of this composition identity. The ancestor command returns sk-def-sp-tate-twist. The item now has an exact from.place and same_as = [].

All Mathlib searches were run through msearch.py and their actual tools/queries/results are in searches.jsonl and mathlib_searches. Two LeanFinder phrasings, LeanSearch, Loogle and grep found no statement specializing to these specified twists. I read AdicCompletion.map_comp in Mathlib/RingTheory/AdicCompletion/Functoriality.lean:154-157: it concerns the I-adic completion of linear maps over one fixed ring, not these sheaves with changing coefficient rings and a root factor. I also read Cover.Directed.lean:44-54: Cover.trans_comp concerns maps between schemes in a locally directed cover. Neither supplies this item by a one-line specialization. The Loogle query with two comma-separated expected names returned no hits; this is recorded as such, not treated as evidence that the individual general categorical facts do not exist.

## Review by NG

I read the current chapter and unit in literature/blueprint/latest/blueprint/sec-proetale-coefficients/, the DAG unit record, and ProEtaleTateTwists.lean, especially the four unique-map signatures and the definitions immediately following them. The statement matches the module's arbitrary X and [Fact ell.Prime]; n=0 means ell^1, not a zero coefficient level. The integral object is an ordinary inverse limit in modules, and the rational object is ordinary extension of scalars of that integral object, with underlying abelian maps throughout. The blueprint's local-freeness and derived-twist clauses are not used for this map identity.

Step 1 uses the actual strict composition clause of def-sfb-qlbar-subextension-map, the functor stated by sk-def-sfb-pulled-back-coefficients, and the construction of def-sfb-coefficient-map. It then uses both parts of lem-route-sp-integers-map-exists-unique: ring-map structure and the square with a_K. Writing out a_H r_FH r_EF = c_EH a_E verifies the hypothesis of uniqueness for E <= H. The ring-map condition is preserved by substitution in the unit/multiplication equations. It is a short application of the existing interface, not a new lemma.

Step 2 uses the exact reduction square in lem-route-sp-ell-map-exists-unique and its uniqueness quantifier. The displayed three equalities verify the defining square for the composite at each positive exponent. It needs no surjectivity assertion on sections and no injectivity of an induced quotient map. This is why the existing existence/uniqueness interface suffices without adding a theorem about sheaf epimorphisms.

Step 3 uses exactly the all-n projection formula in lem-route-sp-integral-twist-map-exists-unique and its uniqueness. Substitution gives the required projection formula for the composite. The sole tensor operation is checked explicitly on b tensor m and finite sums in the presheaf tensor of def-pur-sheaf-tensor-product; functorial sheafification preserves that equality. There is no hidden limit-preservation or acyclicity assertion. The source docstring argues by joint projections; the existing uniqueness statement packages precisely that argument.

Step 4 uses the tensor normalization and uniqueness in lem-route-sp-rational-twist-map-exists-unique, with the integral identity from step 3 and the coefficient identity from step 1. I checked the order against the Lean formula: e_E followed by j_EF equals (c_EF tensor u_EF) followed by e_F. Substitution twice gives the same equation for j_FH composed with j_EF. Tensor bifunctoriality is again written on generators before sheafification. The proof does not assume every sheaf section is a pure tensor, and it does not invoke flatness, localization exactness, or a rational base-change comparison.

All four steps are elementary relative to their cited nontrivial existence/uniqueness interfaces: each consists of substitution and then the corresponding uniqueness conclusion. Every cited statement was opened and has the part used; citations.json quotes the actual statements including their Lean formulas. All steps are below 2000 characters. No argument has been transferred to a new restatement node.

For small cases, E=F, F=H, and E=F=H leave the same equations valid (no strict-inclusion assumption occurs). For empty X all maps are between zero underlying sheaves and uniqueness still applies. For ell not invertible, the roots can degenerate but the finite tensor and limit normalizations and their composition still make sense; no primitive roots or rank-one basis enters the proof. Ramification causes no problem since the common ideals are ell^(n+1), not unrelated powers of chosen uniformizers. These checks justify retaining all hypotheses and all cases of the Lean statement.

I checked B1-B9: there are no new nodes; the item is self-contained, with definition dependencies, one TeX escaping layer, current blueprint references and actual search results. B10's attachment check fails because the item's own proof is sorry. C1-C4 are discharged by the four exact interfaces and the explicit tensor substitutions; C5-C6 by the existing-node searches and dependency-path inspection; C7-C8 by the stated tool uses. D1-D5 do not apply any relabelling: all work is in four written calculations with no new lemmas. E1-E7 were checked against the hypotheses, the map types and the edge cases above. I corrected the provisional wrapper, the missing statement dependencies and the unspecified blueprint place; I found no mathematical statement dispute.

## Dry-run repairs

The first dry run rejected three quotations as too short to show their use. I expanded every uniqueness quote to its complete existential-uniqueness formula, including its characterizing equations, and quoted the full relevant strict-functoriality and pullback-functor clauses. The cited mathematical statements and the proof are unchanged.
