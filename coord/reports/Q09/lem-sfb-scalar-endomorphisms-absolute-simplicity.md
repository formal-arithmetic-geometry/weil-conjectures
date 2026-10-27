# Q09 stage-1 delivery: lem-sfb-scalar-endomorphisms-absolute-simplicity

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-scalar-endomorphisms-absolute-simplicity.json`: item, statement unchanged, six proof steps, status split; no exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-coalgebra-dual-action-detection.json`: new statement-only prerequisite, status unsplit; no Mathlib match after LeanSearch, Loogle, LeanFinder, grep and a second semantic phrasing.
- `citations.json`: one verbatim cited statement for every step/node pair (11 entries).
- `searches.jsonl`: actual command-generated search log, retained intact. `milne.txt` is a local PDF text extraction for source reading.

One new node, zero new Mathlib leaves. The proof reuses the existing Mathlib leaves for a vector-space basis, the finite double-centralizer theorem, affine fibre products and finite-type base change.

## Attachments

None. Searches in `lean/WeilConjectures/` for the blueprint tag, absolute simplicity, scalar endomorphisms and comodules found no theorem giving the item. The source's `GeneralLinearGroup.RationalHom.IsSimple` tests rational points and assumes algebraic closedness and characteristic zero; it cannot supply this general scheme-theoretic result. I read `GeneralLinear/Representation.lean`. I also searched the new prerequisite's id and concept in WeilConjectures and Sheaf; the existing dictionary and coefficient-coalgebra modules do not assert dual-action detection.

## WANTED

None needed. The local Milne PDF supplies the statement and the coalgebra/algebra route. Proposition 4.19's proof refers to Bourbaki but does not give details; this delivery supplies those details independently and records proof_origin.by = agent, rather than pretending to have read Bourbaki.

## Audit findings and route

Milne, Proposition 4.19(b), printed pp.90–91, states exactly the item, with rational endomorphisms defined in Remark 4.18. There is no statement dispute or hypothesis correction. In particular no perfection, separability, geometric reducedness or connectedness is required. Milne's alternative route using distributions is restricted to perfect fields, so I do not use it.

I read Chapter 9(d), pp.174–175 (the convolution dual and comodule identities), Example 9.36 on p.178 (the finite duality case), and the displayed double-centralizer theorem in Proposition 14.1 on p.279. The general contraction-detection formulation is supplied by Q09 and clearly identified as such in the new node's source. Its prospective proof uses coassociativity for multiplicativity, the counit for the unit, and separation by linear forms for the converse subspace/intertwiner tests: each tensor involves finitely many coefficients, whose independent subfamily admits coordinate functionals. This argument is retained here as work for the next worker, not put into the unsplit statement.

The existing coefficient coalgebra and finite duality nodes were read and could support a finite-coalgebra route. The chosen proof avoids a redundant finite reduction: the full dual already acts on every comodule, and each original functional extends explicitly over K. The new input is a general bridge between comodules and ordinary modules, not a restatement of absolute simplicity.

Whole-DAG statement searches for comodule, dual algebra, convolution actions, subcomodule/submodule detection, and the new id found no duplicate. Existing `lem-sfb-finite-comodule-coefficient-coalgebra` constructs a finite coefficient subcoalgebra; `lem-sfb-finite-coalgebra-dual-base-change` compares dual algebras and group-like characters; `lem-sfb-flat-coalgebra-subcomodule-core` constructs the largest subcomodule inside a submodule. None states dual-action detection. `lem-sfb-convolution-linear-map-algebra` supplies the algebra and is reused as a statement dependency of the new node.

Blueprint searches (blueprint_refs.py) for density, centralizer, coalgebra, comodule, absolute simplicity, scalar endomorphisms, dual algebra, subcomodule and intertwiners found no equivalent node. The broad density/centralizer matches concern unrelated geometric density or group centralizers. I searched the current `literature/blueprint/latest/blueprint/` text too. The ancestor command returns None, as inherited in this deep legacy dependency chain; its via chain and precise inherited place are retained. The new node prefixes the item to that via chain and names the exact dual-action prerequisite before density. The chapter and unit records were read and neither was changed; this is an auxiliary algebra lemma on the inherited constructibility route, not the unit's key node.

## Not duplicates

No Stacks tag is used by the new node. There are consequently no same-tag pairs requiring comparison. Conceptual near matches were read and distinguished above. No duplicate of the finite double-centralizer Mathlib leaf is created.

## Review by Q09

I checked the six steps against the actual cited statements, not just their names.

1. The affine-coordinate Hopf node explicitly gives Delta and epsilon with both coalgebra identities for an arbitrary affine group scheme. The dictionary explicitly gives the coaction/action bijection, the point formula and the intertwiner equivalence. These are exactly the claims used. To apply that dictionary to a stable subspace, the proof explains that inverses also preserve it, so restrictions are automorphisms and form a natural rational action; its inclusion is an intertwiner. The finite-type hypothesis of the dictionary is present for H.
2. The new node gives the algebra map into End_k(V), scalar operators, subspace detection and all k-linear intertwiners. Its statement allows infinite-dimensional C. Passing to the image B makes the action faithful without assuming the dual action itself is faithful. B contains k, so a ring-submodule is automatically a k-subspace and an additive B-linear map automatically k-linear. Thus simplicity and the endomorphism hypothesis transfer under exactly the hypotheses we have. No claim about arbitrary abstract group points is used.
3. The basis leaf says every vector space has a basis. The finite-support argument in the step makes the chosen basis finite from the item's finite-dimensionality. The existing double-centralizer statement gives surjectivity for a nonzero faithful simple module finite over its endomorphism ring. All four hypotheses were verified in Steps 2–3. The endomorphism ring is all scalar maps, so the basis is a generating set for its left action and every k-linear map is linear for that action. I read Mathlib SimpleModule/Basic.lean:559–592 and the declaration at line 581: it is the existing leaf's genuine generalization, not a new leaf needed here.
4. The affine fibre-product statement gives the coordinate algebra C tensor K with the actual projection maps; tensor symmetry gives the displayed K tensor C convention. The dictionary, now over K, supplies the coaction and point formula. Its hypotheses still hold: H_K is affine, and clause (2) of the existing finite-type composition/base-change node explicitly supplies finite type after this arbitrary base change. I added that citation on the final source review, rather than leaving the dictionary hypothesis implicit. The proof pins rho_K on generators and verifies that its evaluated action is the scalar-extended original action, rather than merely asserting an unspecified compatibility.
5. The tensor definition supplies the functional f_K with its balanced formula. The new node applies over the arbitrary field K and detects W as stable under every contraction. The displayed computation identifies T_(f_K) with the scalar extension of T_f. This does not assert that K tensor C* is the full dual of C_K, which would generally be false for infinite-dimensional C.
6. The scalar-extended basis is justified by explicit inverse coordinate maps. For nonzero w one nonzero coordinate a_j is selected; each extended matrix unit sends it to a_j times a basis vector. Division by that coordinate proves that W contains the entire basis. This last step is elementary relative to the cited tensor definition and the preceding results. There is no hidden geometric irreducibility or descent theorem.

I checked delivery-errors B–E in full. The new node is self-contained, defines coalgebra/comodule inline, cites tensor and convolution notions, has no proof or proof dependencies, and uses single TeX backslashes after JSON decoding. All Mathlib search records come from the actual command log; the results I read were coalgebra/comonoid equivalences or convolution structures, not comodule detection. Schur and FDRep results require additional algebraic-closedness/finite-abstract-group hypotheses and do not prove the item. No cited statement is used for a claim absent from its text. Every non-elementary input is a cited node, and all citation quotes are verbatim complete statements. There is no SGA source, route substitution, changed maintainer field, Lean edit or compiler invocation. All six steps are under 2000 characters (largest 949), and I checked them for hidden comparisons despite their length.

Small cases checked: V of dimension one (the argument gives its scalar algebra); H trivial (simplicity forces dimension one); nonreduced finite group schemes in positive characteristic (the universal algebra point, not k-points, detects coactions); imperfect k and purely inseparable K/k (all tensor and contraction formulas still apply); infinite-dimensional coordinate coalgebra C (only individual functionals are extended); K=k; W=0; the zero coalgebra in the new node (its counit identity forces a comodule to be zero); zero comodules and zero-dimensional subspaces. I checked the left/right convention: a right coaction gives T_(f*g)=T_f composed with T_g for the stated convolution, so no opposite algebra is silently substituted.

## Unfinished work

Only the new statement-only dual-action/detection prerequisite remains for its own future split. The present item has a complete assembly proof. No mathematical or tool obstacle is known at this point.
