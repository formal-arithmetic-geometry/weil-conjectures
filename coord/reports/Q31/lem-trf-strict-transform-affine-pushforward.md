# Stage-1 report: lem-trf-strict-transform-affine-pushforward

Group Q31, 2026-10-18. Direct delivery; no second worker or sub-agent.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-strict-transform-affine-pushforward.json — statement, split into six steps; not a Mathlib match. The statement and stmt_deps are unchanged. No new nodes and no new Mathlib leaves.
- citations.json — 18 records containing verbatim portions of the statements cited in the six proof steps.
- report.md — this report. searches.jsonl retains the actual search records. Local Python scratch scripts are not delivery nodes.

## Attachments

None. I searched the slopmaster2 WeilConjectures source for the exact item id and its blueprint tag and for strict transform, strictTransform, strict_transform and affine pushforward. No project declaration states the module-sheaf assertion. The module-power-torsion results in WeilConjectures/Mathlib/Algebra/Module/Torsion.lean concern chart modules, and the strict-transform blowup results concern schemes; neither supplies this assertion. Upstream master is reference material only.

## WANTED

None. All proof sources used are available locally.

## Findings and corrections

The item is Stacks Tag 080G, divisors.tex, lemma-strict-transform-affine, restricted to a finite-type quasi-coherent centre as already stated. No statement correction or weakening is necessary. In particular the two sides are modules on the full base-changed schemes, not modules on the scheme strict transforms. Affine pushforward is used on quasi-coherent modules, not on every module sheaf.

The initial candidate decomposition was reduced after reading the existing DAG: support pushforward is equality of kernels of restriction, and exact affine pushforward here is an immediate application of the existing affine cokernel statement. Neither deserves a new node. Even quasi-coherence of the supported subsheaf follows by applying the existing qcqs-pushforward and quasi-coherent-kernel statements. The uncommitted support-pushforward candidate was removed. No new node is delivered.

I also corrected the base-change application in the working proof: its base-change morphism is p_Y:Y_b -> Y, not b:S^b -> S. These define the same geometric square only after its fibre-product identifications are supplied in Step 1. The final proof explicitly supplies those identifications. Nonzerodivisorness of the exceptional equation is used only on the blowup base; it is not claimed after pullback to X_b.

The existing blueprint ancestry through lem-trf-local-term-locality and the flattening branch is historical metadata, which I retained. I read the current ancestor blueprint_update and the unit record: they state the contracting-correspondence/Varshavsky theorem, rather than explicitly stating this affine algebraic-geometry tool. This split addresses the already existing descendant tool with its specified source 080G; it does not change or replace any unit proof. The blueprint searches for strict-transform affine pushforward and lemma-strict-transform-affine found no node stating the same result. The chapter and unit records were read and are unchanged.

## Review by Q31

I checked delivery-errors B through E against the final item and its sources. I read the whole statement and proof of Stacks 080G in divisors.tex, the strict-transform definition 080D immediately before it, the supporting discussion of exceptional divisors, Properties 07ZP and 07ZQ in properties.tex (including the kernel argument and the omitted-proof hint), affine base change 02KG in coherent.tex, and the quasi-coherent kernel/cokernel and functoriality paragraphs of schemes.tex (01IC, 01ID, 01LA/01LB and 01LC). For pullback I read modules.tex at lemma-pullback-quasi-coherent (01BG); for principalization I read divisors.tex at lemma-blowing-up-gives-effective-Cartier-divisor and the current main-20261015 principalization blueprint statement. There are no new nodes whose sources require separate review.

Step 1 uses precisely clause (1) of lem-weil-pbc-affine-morphism-permanence for base-change affineness and clause (1) of lem-weil-pbc-affine-pushforward-base-change for quasi-coherence of g_*F and the specified canonical comparison. I opened both node files. The square is cartesian by giving its common compatible-map description. The hypothesis is affine g and quasi-coherent F; no flatness, finite type of g, or qcqs of the base is required. The node lem-pc-ringed-space-tensor-pullback-qcoh states quasi-coherence for arbitrary ringed-space pullback, so it applies to both scheme projections here and to the restriction in Step 3.

Step 2 uses the statement of thm-nagata-blowup-principalizes-center, read verbatim, with exactly the finite-type quasi-coherent centre of the item. It supplies a locally principal exceptional ideal; pulling its generator along the structure map preserves the equation of its inverse-image zero set, even if the pulled-back generator is a zero divisor. I opened the affine-open-basis, quasi-compact-spectrum, and localization-away-basic-open nodes: they respectively give the refining cover, a finite subcover, and quasi-compactness of each D(a). The finite-union calculation proves quasi-compactness of j_X without a quasi-separatedness assumption on X_b. Its diagonal is the identity under the open-immersion fibre-product identification, so the quasi-separatedness definition applies. This is an elementary geometric verification from those cited statements.

Step 3 uses only the statement of the module strict-transform definition, quasi-coherent pullback, pqf-lem-pushforward-qcoh, the quasi-coherent-kernel node, and clause (2) of the cokernel-image node. I opened each file. The target of the kernel map is quasi-coherent because j_X was proved quasi-compact and quasi-separated; its source is H_X from Step 1. The kernel node explicitly defines its kernel sectionwise. Thus it is exactly the support submodule, not a different notion of support or a definition cited for a closure theorem. The cokernel statement applies only after K_X is proved quasi-coherent. This is the short kernel argument from the proof of 07ZP, written in the item rather than extracted as a redundant new lemma.

Step 4 is the complete elementary proof of the support-pushforward comparison of 07ZQ. It uses the definition's zero-restriction description. For every U, the two conditions reduce to vanishing on the very same open g_b^{-1}(U minus D_Y). The equality D_X=g_b^{-1}D_Y follows from the structure maps commuting. The comparison beta is an isomorphism of sheaves, so it commutes with that restriction. No assertion that pushforward commutes with stalks is used.

Step 5 applies the statement of lem-weil-pbc-quasi-coherent-module-cokernel-image, clause (3), to K_X -> H_X on W=g_b^{-1}U. I checked that the affine-morphism definition gives affine W and that both modules are quasi-coherent by Step 3. The node gives the actual quotient map on affine sections, with surjectivity and the stated kernel. Surjectivity on the cited affine-open basis is local surjectivity of sheaves; the kernel identity is sectionwise on every open. This proves precisely the quotient comparison needed, not an uncited general exactness theorem.

Step 6 descends beta and its inverse to the equal submodule quotients. Their composite is the identity because it is the identity before quotienting, so no non-elementary isomorphism criterion is hidden. The strict-transform definition is cited for both endpoints. The characterization after the quotient epimorphism proves canonicity and is independent of the affine cover used to verify surjectivity.

All generic statements from other units are declared in split_report.tool_uses with their precise purpose. The source's Stacks route is retained and no SGA source is invoked. I checked that proof_deps is exactly the union of uses and that every citation quote is verbatim in its node's statement. No step exceeds 2000 characters (the longest is 1011), and none hides an unrecorded standard lemma: the support and quotient comparisons are written on sections. No new definitions, auxiliary statement clones, incomplete statements, or new nodes carrying proofs are present.

I tested the argument on g=id (both quotient maps agree), F=0, empty source and empty base, unit ideal (blowup is the identity and the support kernel is zero), and zero ideal (the blowup is empty, so both sides are zero). I also checked nonflat pullback by imagining an exceptional generator that becomes zero on X_b: the support is then all of the corresponding chart, K_X=H_X and the quotient is zero; the proof still applies. Arbitrary infinitely generated quasi-coherent F is allowed throughout, and no exactness of pullback was asserted.

## Not duplicates

No new node is delivered. DAG and blueprint searches found the existing affine-base-change, quasi-coherent kernel/cokernel, pullback, pushforward and blowup-principalization statements, all reused. Neither the scheme strict-transform nodes nor the power-torsion nodes state the item itself.

## Unfinished work

No mathematical work remains for the one-level split. Server checks and the required delivery dry run/push follow this report.
