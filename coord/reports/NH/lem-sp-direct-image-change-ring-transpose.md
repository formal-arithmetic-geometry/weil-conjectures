# lem-sp-direct-image-change-ring-transpose — NH stage-1 delivery

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-direct-image-change-ring-transpose.json: statement, split into four proof steps; no Mathlib match.
- citations.json: one verbatim statement quotation for every step/node citation.
- searches.jsonl: actual msearch.py results, retained with this sandbox.
- report.md: this report.

No new nodes, no Mathlib leaves, no unit record changed. The statement and its statement dependencies are unchanged. Existing blueprint, creation metadata and inherited searches are preserved; fresh logged searches are appended.

## Attachments

None. Searches of WeilConjectures/ by the item tag, coefficient/change-of-rings terms and projection/transpose terms found no declaration proving this item. I read SixFunctors/ProEtale/Derived/LowerStarProjection.lean: rightDerivedLowerStarProjectionMap_app_app and homEquiv_symm_rightDerivedLowerStarProjectionMap give the transpose of the fixed-coefficient projection map, not its identification with restriction of the B-linear coefficient map. The module documentation also explicitly records its dependence on sorryAx through derivedTensor. They are not an attachment of this item. No upstream master sorry declaration is treated as finished evidence.

## WANTED

None. All sources used are present locally.

## Findings and corrections

The item already carries the maintainer's corrected pro-etale, unbounded statement. I did not revert it to an etale comparison or introduce a boundedness assumption. The blueprint Step 1 defines an A-linear projection morphism; it does not itself justify identifying that morphism with restriction of the B-linear coefficient comparison. The existing generic coefficient-change adjunction node supplies precisely the missing adjunct compatibility, and the split now checks its coefficient-square hypothesis and the normalization of the canonical pullback/tensor map explicitly.

The whole argument stays in ordinary uncompleted constant-ring module derived categories. There is no identification with condensed or completed coefficient categories, and no change to any target. In particular, no finite Tor dimension of B over A is inferred from finiteness.

## Unfinished work

None for this one-level split. All non-elementary inputs already exist as nodes; this delivery adds no unsplit input.

## Not duplicates

No new nodes were created. DAG and blueprint searches for direct image/change-ring transposes, coefficient comparisons, projection morphisms and tensor pullback found no alternative node stating the same normalization. The coefficient-adjunction node is a generic input with arbitrary compatible identified ring sheaves; the item applies it to constant A and B and identifies its transpose with the specific tensor projection. The fixed-coefficient projection definitions and the etale comparison nodes do not assert this change-of-ring identification. The item's blueprint.same_as remains empty.

## Review by NH

I read the chapter record, the sk-lem-sp-reduction unit statement and its two steps, the current main-20261015 ancestor proof sk-lem-sp-reduction-direct-image.proof.md (especially Step 1 and naturality in Step 4), and the current item and statements of all seven proof dependencies. The unit uses compactification and the scalar projection argument; this item is the normalization in that route, and does not replace its finite-window argument. No blueprint_update is present on the item. There are no new-node sources to audit.

For the foundational literature I read sites-cohomology.tex, lemma-derived-pullback-composition (0D6D), lemma-derived-pushforward-composition (0D6E), lemma-adjoint (07A6), and lemma-pullback-tensor-product (07A4), and sites-modules.tex, lemma-tensor-product-pullback (03EL). These are unbounded ringed-topos results and the ordinary balanced tensor calculation used for normalization. No SGA source is used. The proof is marked agent-written because it expands the blueprint normalization by a specific comparison calculation rather than quoting a single literature proof of the whole item.

Step 1 uses lem-weil-pbc-ring-sheaf-change-adjunction for its actual stated b and d and its adjunct identity, not merely the existence of restriction. I verified its compatible coefficient square using prop-weil-pbc-proetale-constant-ring-map: its stated identifications preserve constants, so A to B commutes with them. Both coefficient rings are finite, and p is a scheme morphism; all hypotheses of these two statements hold. Properness and the standing geometric hypotheses remain in the item even though this formal argument needs less.

Step 2 checks the comparison that Step 3 needs, rather than simply calling two canonical maps equal. The operations definition gives identified-coefficient pullback as inverse image with transported action, and the change-adjunction statement says b is induced by exactly that inverse image. The sheaf tensor definition supplies the balanced local pure tensors and their sheafification. Both ordinary comparison maps send the inverse image of x tensor s to the inverse image of x tensor c_B(s). I checked the passage to complexes: det-sp-scalar-extension-functor states the K-flat computation and the right B-action; the tensor-pullback node states preservation of flat K-flat complexes and the canonical derived tensor comparison; the tensor-descent node states the localization equivalence and uniqueness of extension of natural transformations. Thus no ordinary pullback localization is assumed for arbitrary ring maps and no flatness of B is smuggled in. Resolving B to compute the underlying derived tensor gives the same comparison through its augmentation. This is a single routine normalization calculation using existing constructions, not a hidden new existence or comparison lemma.

Step 3 applies exactly the final adjunct clause of the change-adjunction statement with M=T_Y R_A N and target T_X N. Its t is T_X(epsilon_N) composed with theta, whose B-adjunct is gamma by the item's definition. I checked the direction of b inverse and of d: the A-transpose has source L_A r_Y M and the A-adjunct is d composed with r_Y(gamma). Step 2 identifies its source comparison with tau, and the scalar-extension statement explicitly sends a morphism v to v tensor identity. The resulting transpose is epsilon tensor identity after tau. Injectivity of the given Hom bijection proves equality with the projection morphism, without asserting that this map is invertible.

Step 4 writes the naturality equation for h_N, using the counit naturality in the stated adjunction and the simultaneous naturality explicitly asserted by the tensor-pullback node. The final Hom bijection in the operations statement is functorial in both inputs, so transposition proves the required naturality. Each quoted statement was opened and each citations.json quote is a literal substring of it; no step uses a cited node's proof instead of its statement.

I checked B=A (identity coefficient extension), N=0, empty source schemes, and the nonflat map Z/ell^2 to F_ell with an unbounded N. In the first case the equation is the ordinary counit transpose; in zero/empty cases all maps have the specified zero endpoints; in the nonflat case K-flat resolutions, not underived tensor of arbitrary complexes, compute the maps. No Tor-amplitude assertion is needed. All steps are shorter than 2000 characters. The B–E checklist found no relabelled new clauses, missing lemma citation, unsupported hypothesis, ambiguous coefficient category or cyclic reliance on the parent.

The off-unit generic tools are declared in split_report.tool_uses: coefficient-adjunction compatibility, derived tensor/pullback comparison, and K-flat tensor descent. They supply foundational functor comparisons which this unit does not state, and do not replace a geometric unit step. Mathlib searches were run through msearch.py with two semantic phrasings, Loogle and grep; returned ordinary module adjunctions and generic derived adjunctions do not state this item. Inherited searches were retained as inherited evidence, and every fresh record is copied from the actual sandbox log.
