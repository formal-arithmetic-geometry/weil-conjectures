# Q99 — lem-sbc-module-bc-integral-surjective

## Files written

- `dag/nodes/sec-smooth-base-change/lem-sbc-module-bc-integral-surjective.json`: statement; split into four proof steps; statement unchanged. Added quasi-compact and quasi-separated definition dependencies.
- `dag/nodes/sec-smooth-base-change/lem-sbc-fixed-base-critical-map.json`: new statement-only node, not Mathlib; its two clauses have completed project declarations (attachment candidates below).
- `dag/nodes/sec-smooth-base-change/lem-sbc-integral-test-pushforward-arrow.json`: new statement-only node, not Mathlib; the existing Lean comparison depends on an open integral exchange theorem.
- `citations.json`: verbatim statement excerpts for every use in every item proof step.
- `searches.jsonl`: 15 searches actually run through msearch.py, with queries and unmodified result records. Each node's five searches include LeanFinder, Loogle, LeanSearch, grep, and a second semantic phrasing.

No unit file changed: this item is a child of the already realized universal-datum unit. There is no earlier sandbox split or report to retain. No Lean files, compiler, Lake, global build, live repository files, or launcher files were touched. The sandbox prepare.py is a local construction aid only.

## Attachments

AlgebraicGeometry.Etale.mono_baseChangeHomologyMap, AlgebraicGeometry.Etale.mono_cokernelMap belong to lem-sbc-fixed-base-critical-map, respectively clauses (1) and (2), in `WeilConjectures/SixFunctors/Etale/SmoothBaseChange/Injectivity/CriticalMap.lean:82-104,156-177` (docstrings begin at 67 and 149). The exact source signatures use fixed-base `BaseChangeProperty`, arbitrary commutative Lambda, q an integer with 1 <= q, qcqs g, and the same Cartesian square. I read both complete proofs. A traversal of every dependency recorded in `local/sorry_map_slopmaster2_7d675a26.jsonl.gz` visits 2022 names for each and finds no direct or transitive sorry. These are project declarations, not Mathlib leaves. They are recorded as lean_candidates for maintenance to attach; the sandbox also records the audit evidence. This child has no proof steps and is not split further.

No finished attachment for the item: the exact declaration `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective` (IntegralBaseChange.lean:141-160) reaches `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isIntegralHom`, whose body is sorry in Integral/BaseChange.lean:48-50. The integral arrow-comparison candidate in IntegralBaseChange.lean:95-123 reaches the same sorry. Traversing the sorry map confirms this for both candidates (2557 and 2449 visited names, respectively). Its existing DAG node is lem-sbc-integral-underived-exchange. This is why neither candidate is used as a finished attachment.

## WANTED

None. All sources used are available locally.

## What needed correction

The item was statement-only. The old Z/n blueprint lemma cannot be used for arbitrary Lambda, and the existing arbitrary-Lambda injectivity node cannot be used with this item's fixed-base hypothesis: lem-sbc-module-bc-injectivity assumes universality over all preliminary base changes. Its completed universal theorem proves a different implication. The new fixed-base node records the weaker hypotheses actually present in the completed component theorems; the item statement has not been strengthened. In particular no torsion, ring-order invertibility, smoothness, or universal BC assumption was added.

The integral comparison must identify the canonical arrows, not merely endpoints. The new arrow node explicitly states the commuting-square equation. It is strictly smaller and independent of the descent problem: arbitrary M on T', any degree r, no surjectivity, and no lower-degree BC. The item still proves the unit injection and the cokernel descent; it does not become “apply a restatement”.

## Source error

In the local Stacks proof of Tag 0F04, the displayed prose `F -> pi_* pi^{-1} F'` is ill-typed: F' is already a sheaf on T', while pi^{-1} takes sheaves on T. The intended expression is `F -> pi_* pi^{-1} F = pi_* F'`. Step 1 uses exactly this unit, as does the read-only Lean proof. This is a proof typo; the source theorem and the item's statement are true and unchanged. No STATEMENT-DISPUTED correction is required.

## Unfinished work

The integral arrow child is intentionally unsplit for the next stage-1 worker. Its proof route, not part of its statement, is: pull back pi to Y' -> Y; integral pushforward is exact; integral underived exchange identifies e^{-1} pi_* with pi'_* e'^{-1}; derived composition and vertical pasting identify the actual exchange arrows; take cohomology. The existing Lean theorem and its docstring give exactly this route and locate the remaining open integral exchange. The fixed-base child needs maintenance to register the two finished attachments. Neither unfinished child leaves a missing step in this item's one-level split.

## Not duplicates

lem-sbc-fixed-base-critical-map vs lem-sbc-module-bc-injectivity: the existing node assumes universal BC and gives the result after every preliminary base change; the new node assumes only BC(p,Lambda,q-1) at the fixed base and proves the fixed-square assertions. Universal BC cannot be inferred from fixed-base BC. This difference prevents citation of the existing statement.

lem-sbc-fixed-base-critical-map vs sbc-lem-bc-injectivity: besides the universal/fixed-base distinction, the existing node treats n-annihilated abelian sheaves, whereas the new node works with arbitrary Lambda-module sheaves and their Lambda-linear lower-degree BC. Forgetting coefficients does not enlarge that hypothesis to all n-annihilated abelian sheaves.

lem-sbc-integral-test-pushforward-arrow vs lem-sbc-module-bc-integral-surjective: the new node is an arrow identity for an arbitrary coefficient M on T', integral pi without surjectivity, and every degree; it asserts no descent from pi^{-1}F to F and assumes no BC in any degree. The item proves descent using the unit and critical cokernel lemma.

lem-sbc-integral-test-pushforward-arrow vs sbc-lem-bc-integral-surjective: the existing node is the n-torsion, universally lower-degree descent implication; it does not state the generic arrow identity. Its proof contains related identifications, but a node's proof is not an available theorem statement. The new statement is neither a special case of that descent theorem nor its conclusion.

lem-sbc-integral-test-pushforward-arrow vs lem-sbc-integral-pushforward-base-change-arrow: the existing abelian comparison replaces the base S of p by an integral scheme and applies pi'_* to the resulting arrow. The new comparison keeps p fixed, replaces the test T of g, and compares the arrow at pi_*M with that for g pi; these are the two different operations described in IntegralBaseChange.lean.

lem-sbc-integral-test-pushforward-arrow vs lem-sbc-integral-underived-exchange: the existing node is the underived integral exchange for a single Cartesian square. The new node identifies higher comparison arrows after composing test morphisms. Underived exchange is an input to its eventual proof, not a statement that contains it.

Whole-DAG searches covered 0F03, 0F04, the exact three candidate names and the key phrases; blueprint_refs searches covered integral surjective, critical map, injectivity, integral pushforward, direct image along an integral, integral test, pushforward, 0F03 and 0F04, in all chapters. The Z/n universal nodes are related statements rather than same_as matches. The item and new nodes therefore keep same_as empty. No existing statement supplies either new interface with these hypotheses. Both children trace through this item to sk-lem-universal-datum; no unit route is replaced.

## Review by Q99

I read Stacks etale-cohomology.tex around lemma-base-change-q-injective and lemma-base-change-q-integral-top (Tags 0F03 and 0F04, checked against tags/tags), including the proof that the cokernel grows with the coefficient sheaf, the unit injection, and all three integral pushforward equalities. I compared this with the complete arbitrary-Lambda proofs in IntegralBaseChange.lean and CriticalMap.lean, and read UpperLowerStar/Surjective.lean and Integral/BaseChange.lean. The new fixed-base statement consists exactly of the two completed CriticalMap declarations, and its source records both clauses. For the new arrow statement, nonempty_arrowIso_baseChangeHomologyMap_lowerStar supplies an isomorphism in the arrow category for every integer q and every coefficient sheaf on T', with no qcqs or surjectivity premise. Writing out its two components is exactly the A,B equation in the new statement. I read its full proof and checked that it requires the open integral exchange, so I did not label it closed or Mathlib.

For Step 1 I opened every cited node and read its statement. The inverse-image definition supplies the unit. The module exactness theorem (2),(3) explicitly identifies the module and abelian adjunction units and their direct-image section formulas. Algebraic closure supplies a closure of each residue field; the geometric-point definition constructs the associated point; surjectivity ensures the image family meets every underlying point. The direct-image definition supplies G(U)=F'(U x_T T'), which makes the stalk map r well-defined under refinement. The inverse-image stalk-germ statement supplies the identity for every represented germ, rather than just an isomorphism of groups. The geometric-stalks-detect-mono statement permits any geometric-point family covering the underlying space, so the image family qualifies; there is no unproved lifting of a preselected geometric point. Its abelian conclusion proves module monicity by faithful forgetting, with the explicit cancellation argument in the step. These citations were chosen for their statements, not for anything in their proofs.

For Step 2 I checked all hypotheses of the new arrow node: pi is integral, both given squares have the same p, the coefficient is exactly F'=pi^{-1}F, and q is an integer. The A,B equation gives b_G=B^{-1} b' A, making the hypothesis on b' applicable to the actual canonical map. There is no surjectivity premise being smuggled into that helper and no claim of conservativity of integral pushforward. For Step 3 the new fixed-base critical node requires exactly the hypothesis that is available, and g is qcqs as assumed. It gives both monicity of b_F and monicity of the natural cokernel map for the unit. I specifically rejected the existing universal node here. Step 4 is the elementary abelian-category argument: a subobject of zero is zero, hence b_F has zero cokernel; mono plus epi is iso. The cited module-sheaf definition says that this is an abelian category, and the abelian-category definition supplies the kernel/cokernel structure. All these uses have verbatim quotations in citations.json.

Small cases checked: q=1 uses only degree-zero BC, no negative-degree induction; Lambda=0 makes every map an isomorphism; F=0 is immediate; pi=id gives identity A,B and the unit; empty T forces empty T' and empty Y,Y', so Step 1 uses an empty covering family on an empty space and all sheaves are zero. The new arrow node also permits negative r (the higher direct images then vanish) and non-surjective integral pi; it states no descent in that case. The fixed-base critical node does not require all lower degrees or preliminary base changes. No target statement, coefficient scope, or chapter route has changed, and no SGA source is used. New unsplit nodes contain statements only and no disguised proof sketches. I checked B1-B10, C1-C8, D1-D5 and E1-E7 against these actual sources and uses; the mathematical corrections were the fixed/universal distinction and the typo in the source unit expression.

## Second reading by Q99

- Item statement: checked hypothesis by hypothesis against Stacks Tags 0F03 and 0F04 and the arbitrary-commutative-ring declarations in `IntegralBaseChange.lean`; the fixed-base `BC(p,\Lambda,q-1)`, qcqs test morphism, integral-surjective `\pi`, Cartesian squares, coefficient pullback, and both canonical maps all agree, including `q=1`, zero coefficients, identity `\pi`, and empty schemes.
- Step 1: checked the unit, module/abelian compatibility, direct-image section formula, geometric-point germ identity, and stalk detection against every cited node; the image geometric points cover by surjectivity, and the explicit left inverse proves the unit monic without a hidden torsion or finite-stalk assumption.
- Step 2: checked the arrow equation against `nonempty_arrowIso_baseChangeHomologyMap_lowerStar` in `IntegralBaseChange.lean`; its two isomorphisms conjugate the actual canonical maps, with no surjectivity or lower-degree hypothesis added.
- Step 3: checked both clauses of `lem-sbc-fixed-base-critical-map` against `mono_baseChangeHomologyMap` and `mono_cokernelMap` in `CriticalMap.lean`; the fixed-base lower-degree hypothesis and the given qcqs `g` are exactly the hypotheses used.
- Step 4: checked the zero-cokernel argument against the abelian-category definition and the cited module-sheaf category; a monomorphism into zero forces the cokernel to vanish, hence the canonical map is epi and mono and therefore an isomorphism.
- `lem-sbc-fixed-base-critical-map`: checked self-contained definitions, exact two Lean clauses, source Tag 0F03, closed sorry-free declarations, and the recorded Mathlib searches; verdict: valid unsplit attachment interface.
- `lem-sbc-integral-test-pushforward-arrow`: checked self-contained objects, all-degree arbitrary-module arrow equation, source Tag 0F04 plus the Lean declaration, and the recorded three search families; verdict: valid unsplit statement-only child, with its Lean candidate correctly left unattached because the dependency closure contains the open integral exchange.

No node statement, proof step, citation, or search record required correction. The only change in this second reading is this report section, documenting the checks and retaining the already recorded Stacks unit typo (`\pi_*\pi^{-1}\mathcal F'` should use `\mathcal F`).
