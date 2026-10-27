# Repair: sk-thm-sf-dual-perfect (Q120, 2026-10-22)

## Files written

- `dag/nodes/sec-six-functors/sk-thm-sf-dual-perfect.json`: unchanged statement and Lean binding; three assembly steps, 1887 characters in total.
- `dag/nodes/sec-six-functors/lem-sf-coefficient-evaluation-naturality.json`: new statement, unsplit, no exact Mathlib match; canonical comparison, naturality, and the evaluation equation (returned Step 2).
- `dag/nodes/sec-six-functors/lem-sf-perfect-dual-pair-and-tate-stability.json`: new statement, unsplit, no exact Mathlib match; coefficient-dual perfectness, opposite shifted Tate lines, and the canonical dual-pair biduality with its inverse (returned Steps 3–4).
- `dag/nodes/sec-six-functors/lem-sf-oriented-double-hom-cancellation.json`: new statement, unsplit, no exact Mathlib match; internal-Hom cancellation on all test objects and its equality on the specified biduality arrow (returned Step 5).
- `dag/units/sk-thm-sf-dual-perfect.json`: only `realized` and `realized_by` filled for the existing unit statement and single proof paragraph.
- `citations.json`: exact verbatim statements for all eight step/node citations, including the three new nodes.

There are 3 new nodes, 0 Mathlib leaves. Each new node has an empty proof, empty proof_deps and null proof_origin. No new node asserts the whole oriented relative theorem. The original statement, imported metadata, pointers and existing Lean records are preserved. Sandbox-only support files retain the returned node, previous report, duplicate search outputs, and the actual Mathlib search log. They are not additional delivery nodes.

## Attachments

None for the item. I searched `lean/WeilConjectures/` by the blueprint ID, Orientation declaration names and invertible-dualizing terminology. The current `Orientation.lean:407–515` provides the finite ordinary-etale comparisons, naturality, preservation, and biduality clauses. Those are useful existing proofs but do not state this item's assertion simultaneously for finite, completed integral, rationalized, and common-stage operations. The item is now bound to `WeilConjectures.sfOrientedPerfectDuality`, `lean/Sheaf/Paper/OrientedPerfectDuality.lean:125`; its proof at line 139 is `sorry`. Thus a no-sorry attachment for all clauses is not available.

I also read `lean/WeilConjectures/CategoryTheory/Monoidal/Closed/InvertibleDualizing.lean`. The generic `ihomFlipIsoIhomUnitTensor`, evaluation equation, `ihomIhomIsoIhomIhomUnit`, and `dualizableIhomEquivalence` are valuable formal tools. Their statements concern a supplied native MonoidalClosed structure; the new nodes instead bind the actual stage-specific operations, the specified coefficient evaluation, dual-pair maps, and opposite Tate evaluations. No independent identification of the completed/localized/common-stage operation datum with that native structure is silently assumed. The new tasks can use these existing generic proofs rather than reprove their categorical core.

## WANTED

None. All sources used are in the supplied literature tree.

## Return repaired and current-source comparison

The Q120 directory initially contained only dispatcher marker files, not the promised retained node/report. I therefore copied the current repository's returned node and Q75 report into the sandbox. The required initial no-push run exited with the diagnostic that the inherited report lacked `## Review by Q120`. I retained that report separately and below as historical evidence, then performed the requested mathematical re-split. This is not an unchanged re-push.

The sole numbered repair is the human's request to spread the old 5177-character proof into independently queued tasks with at least two new nodes and an assembly of at most 3000 characters. This delivery adds three comparable tasks: the 753-character evaluation calculation; the related 1015+856-character perfect-model/dual-pair argument; and the 1253-character internal cancellation argument. Their statements expose the actual maps and all hypotheses. The 468-character construction and 832-character anti-equivalence/specialization argument remain in the assembly, with the generic step references shortened only after their full mathematical content has been assigned to the new nodes. Every old step is copied verbatim below, with its new owner. This preserves the arguments rather than discarding them.

The current node already incorporates the earlier repair of dangling bibliographic IDs. I have not recreated `sk-thm-smooth-purity` or `sk-prop-sf-dualizable-biduality` as nodes: these are blueprint units. I have kept the statement exactly, including its relative scope and the transpose definition of coefficient biduality. The node's newer stage-2 Lean binding is also retained. The old report's line ranges and statements about an absent affine-cohomological-dimension declaration are historical; no dependency has been fabricated from them.

## Mathlib searches and duplicate searches

All new records come verbatim from this sandbox's `searches.jsonl`, written by the prescribed msearch command. I ran LeanFinder, Loogle, grep, and LeanSearch; I used a second semantic phrasing for each proposed task. The first Loogle attempts using `CategoryTheory.IsInvertible` and `CategoryTheory.MonoidalClosed.toIhomIhomUnit` returned unknown-identifier errors, recorded as invalid queries. The later valid `CategoryTheory.HasRightDual` and `CategoryTheory.MonoidalClosed, CategoryTheory.ihom` searches returned the generic dual-pair and closed-structure interfaces. One LeanSearch request returned HTTP rate limiting and is recorded as unavailable. Other LeanSearch calls succeeded.

I read Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:95–200 and Monoidal/Rigid/Basic.lean:255–292,383–420, including `ihom.ev_naturality`, `ihom.ev_coev`, `ihom.coev_ev`, the two tensor-Hom equivalences, and the dual-of-dual instances. These are ingredients; none is a one-line specialization giving the actual completed/rational/common-stage Tate maps, coefficient evaluation identification and all the equations in a new node. Other hits concerned ordinary modules, FGModuleCat, LightCondensed modules, shifts or Tor; their returned types likewise do not supply the new assertions. The generic existing project proofs were also read as described above.

Before creating the nodes I searched the whole DAG statements, and ran blueprint_refs.py ancestor and searches for biduality, evaluation, coefficient biduality, evaluation comparison, opposite Tate, cancellation and shifted Tate. The focused searches and full matching statements are retained in duplicate-searches.txt. I read the likely overlapping node statements, especially the following distinctions.

## Not duplicates

lem-sf-coefficient-evaluation-naturality vs prop-sf-dualizable-hom: the existing result states invertibility of c on a separated local-projective domain; the new result states the morphism-level naturality and evaluation equations for the actual coefficient adjunction, with the explicit inverse-c identification of the twist map, without a separatedness assumption on X beyond its datum.
lem-sf-coefficient-evaluation-naturality vs lem-sf-twist-interchange: the existing result identifies the Tate comparison as inverse c and proves it invertible; the new result provides naturality for arbitrary second-variable morphisms and the evaluation equation after an arbitrary isomorphism gamma.
lem-sf-coefficient-evaluation-naturality vs lem-coef-closed-adjunction-naturality: the existing result compares Hom along a strong tensor adjunction F ⊣ G; it does not state the c_{P,M} comparison or its evaluation equation under gamma.
lem-sf-coefficient-evaluation-naturality vs lem-coef-monoidal-square-hom-transport: the existing result transports comparison maps along a square of four monoidal categories, whereas the new result identifies the within-category evaluation comparison itself.
lem-sf-perfect-dual-pair-and-tate-stability vs prop-sf-dualizable: the existing statement gives coefficient-dual perfectness and evaluation; it does not give the canonical coefficient biduality map and its dual-pair inverse or the specified shifted-line inverse functors.
lem-sf-perfect-dual-pair-and-tate-stability vs lem-sfb-ringed-site-perfect-duality: the existing assertion is for the ordinary derived category of a sheaf of rings; the new assertion includes the completed integral, raw rationalized and common-stage categories and the explicit dual-pair inverse, with their actual coefficient unit.
lem-sf-perfect-dual-pair-and-tate-stability vs lem-trf-perfect-complex-derived-biduality: the existing assertion is for ordinary modules over a ring at a point, not all four sheaf coefficient stages and their shifted Tate lines.
lem-sf-perfect-dual-pair-and-tate-stability vs prop-pod-biduality-at-the-point: the existing assertion is point duality; the new assertion is on the coefficient site of X with local models and the specified Tate-line evaluations.
lem-sf-perfect-dual-pair-and-tate-stability vs lem-weil-field-twist-inverse: the existing result gives field twist functor inverses; the new result also requires finite/integral perfect local models and the specified evaluation-defined coefficient biduality and its inverse.
lem-sf-perfect-dual-pair-and-tate-stability vs lem-pur-integral-line-restrictions: the existing result concerns preservation of completeness and constructibility by integral signed lines, not the coefficient dual pair and its canonical double-dual map at all stages.
lem-sf-oriented-double-hom-cancellation vs lem-sf-etale-twisted-bidual-transport: the existing statement involves exact etale g^*, two dualizing objects and base-change Hom comparisons in ordinary etale categories; the new assertion cancels a line within each actual coefficient category and identifies the map on all test objects, including the completed/localized/common stages.
lem-sf-oriented-double-hom-cancellation vs lem-coef-finite-bidual-transpose: the existing result is scalar extension between ordinary sheaf-of-ring derived categories with supplied evaluation comparisons; the new assertion cancels an internal invertible shifted line in the same coefficient category.
lem-sf-oriented-double-hom-cancellation vs lem-sf-even-line-hom-shift: the existing assertion concerns first-variable shift compatibility on ordinary ringed sites; the new assertion is the double-Hom cancellation isomorphism and its equation on evaluation-transpose biduality.
lem-sf-coefficient-evaluation-naturality vs sk-thm-sf-dual-perfect: the new result has no smooth morphism or anti-equivalence conclusion and isolates an evaluation comparison needed by the item's proof.
lem-sf-perfect-dual-pair-and-tate-stability vs sk-thm-sf-dual-perfect: the new result is coefficient duality and line stability independent of any orientation or exceptional inverse image.
lem-sf-oriented-double-hom-cancellation vs sk-thm-sf-dual-perfect: the new result gives an internal cancellation equation conditional on a specified c and gamma; it does not assert preservation of perfectness or anti-equivalence or construct the smooth orientation.
lem-sf-coefficient-evaluation-naturality vs thm-sf-dual-perfect: the existing whole oriented theorem has additional coefficient and shift compatibilities; it is not used as a replacement for this split, while the new lemma isolates the evaluation calculation for arbitrary L,W.
lem-sf-perfect-dual-pair-and-tate-stability vs thm-sf-dual-perfect: the new statement has no smoothness or orientation hypothesis and treats coefficient duality rather than Verdier duality.
lem-sf-oriented-double-hom-cancellation vs thm-sf-dual-perfect: the new statement isolates a conditional canonical-map cancellation argument, not the whole geometric theorem.
lem-sf-perfect-dual-pair-and-tate-stability vs lem-sf-package-normalized-orientation-perfect-duality: the existing package includes smooth absolute duality and coefficient-module statements; it does not give the coefficient-site dual-pair inverse and Tate stability for a general X independent of smoothness.

## Review by Q120

I read the actual main-20261015 item statement and proof and its chapter/unit records, the coefficient-dual-biduality unit's full dual-pair proof, and the statements of all old and new cited nodes. I also read Stacks Tag 08JJ, sites-cohomology.tex, lemma-dual-perfect-complex, including its local finite-projective proof and signed evaluation warning. That supports the ordinary ringed-site model, not an identification of integral or rational coefficients with ordinary discrete sheaves. No SGA source enters the split, and I did not alter the finite-purity route.

For the new evaluation lemma, I checked its formula by uncurrying: both sides of the naturality equation evaluate a functional on u followed by v, and its theta evaluation equation is the defining transpose of c followed by gamma. It introduces all P,P',M,M',u,v,L,W and requires c invertible precisely where theta is used. I explicitly added the inverse-c identification for a shifted Tate line, so the assembly is entitled to apply this equation to the exact canonical twist map in the item rather than an unspecified isomorphism. The blueprint's first three sentences are its source, with the returned Step 2 supplying the expanded argument.

For the new perfect-dual-pair/Tate lemma, I checked the completed-unit, rational localization and common finite-field meanings against sk-def-perfect, def-weil-site-perfect-complex, prop-sf-dualizable, lem-sf-twist-interchange and def-coefficient-twists-detailed. The node introduces the full coefficient datum and general X; it does not import the initial smooth geometrically-connected Poincare setting as an extra hypothesis. A local bounded finite-projective model stays such after dualization and tensor by a locally free rank-one line and after a degree translation. Negative twists are formed as the coefficient dual of positive tensor powers, so their evaluation is multiplication in a local basis; opposite shifts use the signed tensor constraints. The dual-pair argument identifies Q with H(P,1) by the transpose of its actual evaluation, and reversing the pair gives exactly j_P and the displayed inverse built from b_P. Both composites use the two original triangles. This single work package owns all of returned Steps 3 and 4, including the completed and field-stage details, rather than replacing them by a bare isomorphism claim. Its source is the last sentence of the item proof and the full coefficient-biduality unit proof just read.

For the new cancellation lemma, I checked both internal-Hom variables carefully. Since theta_P^{-1} has source P-dual tensor L and target DP, contravariance produces H(DP,W) → H(P-dual tensor L,W); then gamma^{-1} changes the target to L. This is t_P in the statement, with the correct direction. The q map is asserted internally and on every test object V, with inverse v tensor 1_L, not merely on global sections. Applying the evaluation equation of the first new lemma cancels gamma, and tensor cancellation sends the transpose of e_P tensor 1_L to the transpose of e_P. This is the equation q t delta=j in the derived category. The statement retains the signed symmetry and the even shift 2r; it does not silently drop signs. This is returned Step 5, assigned to its own worker. The source is exactly the item's applying-theta-twice sentence; the test-object details are retained verbatim below.

For assembly Step 1 I opened sk-def-sf-orientation, sk-def-sf-operations and sk-lem-sf-twist-interchange. They give gamma with arbitrary oriented base, the Hom bifunctor and adjunction, and the shifted twist isomorphism for perfect K. The new evaluation node states both the identification with the inverse of c and its naturality/evaluation equation, so the step does not take that extra equation from the sketch twist statement. Smooth separated finite type and pure dimension supply the orientation hypotheses; K is perfect as required. No properness or special hypothesis on Y is introduced.

For assembly Step 2 I checked that the coefficient-dual-pair node states all three facts actually taken from it: perfectness of K-dual tensor L, the specified inverse line and invertibility of j_K. K is perfect and m=d,s=2d are admissible integers. The first step has already supplied the exact c inverse used in the cancellation lemma. That lemma applies with W=Rf^!Lambda_Y, m=r=d, and gives the derived isomorphism with the actual equality q t delta=j_K; therefore delta is invertible. No proof body of a cited node is used as a stronger statement. Full quotations for these statements are in citations.json.

For assembly Step 3 I recomputed naturality of delta by transposing evaluation and checked the arrow inverse delta_{K'}^{-1} D(v) delta_K has source K and target K'. The double-transpose triangle gives D(delta_K) delta_{DK}=1, and applying naturality gives both inverse equations. This routine formal argument is kept explicitly in the assembly; it does not need another full-theorem node. The two existing definitions give the absolute names at f=a_X. It is not a use of general geometric biduality. This also accounts for returned Step 6 in full.

I tested P=0, the coefficient unit, a shifted unit including an odd shift of P, finite-projective retracts, m=0, d=0 and f=id, and the empty scheme. In the shifted-unit test the symmetry contributes the usual sign to the coefficient evaluation transpose; the inverse and cancellation use the same symmetry, so they agree instead of identifying unsigned double-dual maps. No formula divides by a rank, dimension or trace. There is no connectedness, properness, nonzero stalk, or cohomological-dimension hypothesis hidden in these new statements. All the new facts are strictly below the original oriented theorem. The coefficient duality and signed internal-map comparisons are substantive work packages, not new copies of its whole conclusion. Their sources and old arguments remain available for independent workers.

Against delivery-errors B–E: new statements introduce every object and cite the definition nodes they actually use; no proof sketch is embedded in an unsplit statement (formulas specifying the asserted arrows are definitions of the conclusions). All non-elementary arguments formerly inside Steps 2–5 now have nodes with real searches. I checked the likely duplicates above, kept the statement unchanged, retained the unit route, and did not use any child that depends back on the item. The longest remaining assembly step is below 2000 characters, and total assembly is below 3000. New nodes have no proof steps at all. I verified each citation by literal substring membership in the current cited statement.

## What could not be finished

The three new tasks intentionally remain unsplit, as requested by the human, so separate workers can prove them concurrently. This stage-1 delivery makes no claim that their Lean implementations are finished. Delivery validation results are recorded below when the required dry run completes.

## Retained arguments with new owners

These are the exact returned proof texts, not proof steps inside the new statement-only nodes. They document the complete work being transferred. The retained parent statement is byte-for-byte equal to the current read-only repository's statement at restoration.

### Returned Step 1 → Assembly Step 1

Write $H(A,B)=\RHom_X(A,B)$, $\mathbf1=\Lambda_X$, $L=\Lambda_X(d)[2d]$, $\omega=Rf^!\Lambda_Y$ and $D=H(-,\omega)$. The orientation [sk-def-sf-orientation] gives $\gamma:L\xrightarrow{\sim}\omega$. The bifunctor of [sk-def-sf-operations](i) sends $\gamma^{-1}$ to an isomorphism $H(K,\omega)\to H(K,L)$. The displayed special case $m=d,n=2d$ of [sk-lem-sf-twist-interchange] gives $H(K,L)\cong K^\vee\otimes L$. Thus the composite is exactly the specified $\theta_K$.

Cited nodes: sk-def-sf-orientation, sk-def-sf-operations, sk-lem-sf-twist-interchange.

### Returned Step 2 → lem-sf-coefficient-evaluation-naturality

The canonical comparison $c_{K,M}:H(K,\mathbf1)\otimes M\to H(K,M)$ is the transpose of evaluation tensored with $M$, using [sk-def-sf-operations](i). For $M=L$, its inverse is the unit case of [sk-lem-sf-twist-interchange]. For $u:K\to K'$, the two composites from $K'^\vee\otimes M$ to $H(K,M)$ have the same transpose: evaluation after $u$. Injectivity of the adjunction bijection makes them equal. Bifunctoriality likewise makes $H(K,\gamma^{-1})$ natural in $K$, so $\theta$ is natural. The defining transpose equation for $c$ says that, under $\theta_K$, evaluation $DK\otimes K\to\omega$ is $K^\vee\otimes L\otimes K\to K^\vee\otimes K\otimes L\xrightarrow{e_K\otimes1}L\xrightarrow{\gamma}\omega$. All symmetries are those of the derived tensor.

Cited nodes: sk-def-sf-operations, sk-lem-sf-twist-interchange.

### Returned Step 3 → lem-sf-perfect-dual-pair-and-tate-stability

By [prop-sf-dualizable], $K^\vee$ is perfect: the local finite-projective hypothesis follows from the equivalent description in [sk-def-perfect]. The Tate line is locally constant of rank one and invertible by [lem-sf-twist-interchange]. Locally tensor a bounded finite-projective model for $K^\vee$ with this rank-one module and translate its degrees by $2d$; it remains a bounded finite-projective model, with the completed, localized and common-stage meanings of [def-weil-site-perfect-complex]. Hence $K^\vee(d)[2d]$ and $DK$ are perfect. In [def-coefficient-twists-detailed] the negative twist is defined as the coefficient dual of the positive tensor power. Evaluation of a rank-one module and its dual is multiplication after trivializing that line, with inverse sending $1$ to the corresponding basis and dual basis. Thus the opposite Tate lines cancel. The inverse of $L$ is $L^{-1}=\Lambda_X(-d)[-2d]$: opposite Tate lines and opposite shifts cancel. Tensoring by these two objects gives inverse functors.

Cited nodes: prop-sf-dualizable, sk-def-perfect, lem-sf-twist-interchange, def-weil-site-perfect-complex, def-coefficient-twists-detailed.

### Returned Step 4 → lem-sf-perfect-dual-pair-and-tate-stability

Use the dual pair supplied by [sk-def-perfect], with evaluation $e:Q\otimes K\to\mathbf1$ and coevaluation $b:\mathbf1\to K\otimes Q$. Under the adjunction [sk-def-sf-operations](i), the transpose $Q\to H(K,\mathbf1)$ of $e$ has inverse obtained by inserting $b$ and evaluating $H(K,\mathbf1)\otimes K$. Both inverse equations are the two dual-pair triangle identities. Thus $Q$ identifies with $K^\vee$ with its canonical evaluation. Symmetry reverses the pair, giving a dual pair $(K^\vee,K)$. The transpose $j_K:K\to H(K^\vee,\mathbf1)$ of coefficient evaluation has inverse $K^{\vee\vee}\xrightarrow{b\otimes1}K\otimes K^\vee\otimes K^{\vee\vee}\xrightarrow{1\otimes\mathrm{ev}_{K^\vee}}K$, with the symmetry understood. Its two inverse equations are again those two triangle identities. Therefore the canonical coefficient biduality is an isomorphism.

Cited nodes: sk-def-perfect, sk-def-sf-operations.

### Returned Step 5 → lem-sf-oriented-double-hom-cancellation

Transport the first variable by $\theta_K$ and the second by $\gamma^{-1}$ to identify $DDK$ with $H(K^\vee\otimes L,L)$. Cancellation defines an isomorphism $q:H(K^\vee\otimes L,L)\xrightarrow{\sim}H(K^\vee,\mathbf1)$. Explicitly, for every test object $A$, the adjunction of [sk-def-sf-operations](i) identifies its map on Hom sets with
$$\operatorname{Hom}(A\otimes K^\vee\otimes L,L)\cong\operatorname{Hom}(A\otimes K^\vee,\mathbf1).$$
Send a map on the left to its tensor with $L^{-1}$ and cancel $L\otimes L^{-1}$; the inverse sends $v$ to $v\otimes1_L$. The two composites cancel to identities. Transposing these formulas gives inverse internal-Hom arrows, so the construction concerns internal Hom and not only global sections. These are the canonical opposite-twist maps of [sk-lem-sf-twist-interchange], applicable to the perfect $K^\vee$ by Step 3. Now $\delta_K:K\to DDK$ is the transpose of evaluation $DK\otimes K\to\omega$. Step 2 identifies that evaluation with $e_K\otimes1_L$, followed by $\gamma$. The cancellation sends its transpose to the transpose of $e_K$, namely $j_K$. Thus $q\delta_K=j_K$ and Step 4 proves the asserted biduality identification and invertibility. The symmetry retains the graded signs; the shift $2d$ is even.

Cited nodes: sk-def-sf-operations, sk-lem-sf-twist-interchange.

### Returned Step 6 → Assembly Step 3

Transposing naturality of evaluation gives $DD(u)\delta_K=\delta_{K'}u$. Thus Steps 3 and 5 supply the contravariant endofunctor $D$ on perfect objects and a natural isomorphism $\mathrm{id}\xrightarrow{\sim}DD$. This gives the equivalence between the perfect category and its opposite, with $D$ as inverse. More explicitly, the inverse on arrows $v:DK'\to DK$ is $\delta_{K'}^{-1}D(v)\delta_K$; the two inverse equations use the preceding naturality and $D(\delta_K)\delta_{DK}=1_{DK}$. The latter follows by transposing evaluation twice: both transposes are evaluation by the unit–counit triangle identities of [sk-def-sf-operations](i). Finally [sk-def-sf-orientation] and [sk-def-sf-operations] identify $Rf^!\Lambda_Y=\omega_X$ and $D=\mathbb D_X$ when $Y=\operatorname{Spec}k$, $f=a_X$, giving exactly the named absolute maps.

Cited nodes: sk-def-sf-operations, sk-def-sf-orientation.

## Historical Q75 report (retained verbatim; superseded by the Q120 review above)

# Stage-1 split: sk-thm-sf-dual-perfect

## Files written

- `dag/nodes/sec-six-functors/sk-thm-sf-dual-perfect.json`: existing statement, six proof steps; no exact Mathlib match.
- `dag/units/sk-thm-sf-dual-perfect.json`: only `realized` and `realized_by`, for the statement and the single unit proof paragraph.
- `citations.json`: a verbatim statement quotation for every step/node pair.

There are 0 new nodes and 0 Mathlib leaves. Mathlib searches were run through the prescribed msearch command; the node records the exact tool and query from searches.jsonl, together with the returned hits and verdict. The invalid first Loogle query is explicitly distinguished from an absence result. I read the relevant generic rigid-category candidates in Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean:266–291 and 386–448 and the closed-category interfaces in Monoidal/Closed/Basic.lean. They do not state the entire geometric coefficient-stage theorem with its specified composite and biduality map.

## Attachments

None for the whole item. In the supplied slopmaster2 checkout, Orientation.lean:183–191 states only Nonempty of an isomorphism, and :197–205 states preservation of dualizability. Their proof bodies contain no sorry, but neither declaration states naturality of the specified composite or compatibility with canonical biduality, and their coefficients are finite. They do not cover all clauses of this item. The generic Perfect/Dual.lean declarations also give Nonempty of comparisons rather than all the assigned canonical-map conclusions. No Lean was written or compiled.

## WANTED

None. The current blueprint, its dual-pair proof, and Stacks ringed-site perfect duality are available.

## Corrections and source comparison

The source is main-20261015/sec-six-functors/sk-thm-sf-dual-perfect, both _section.md and its proof file. Its one paragraph suppresses the evaluation comparison needed to identify the canonical biduality. The split now writes that calculation, the preservation of perfectness, and the inverse on morphisms for the anti-equivalence.

Two imported bibliographic ids have no node files: sk-thm-smooth-purity and sk-prop-sf-dualizable-biduality. I removed the former explanatory parenthesis and replaced the latter reference by the actual definition of coefficient biduality as a transpose of evaluation. The hypotheses, relative scope, canonical composite, naturality, anti-equivalence, biduality equality, and absolute specialization are unchanged. This is a reference repair, not a mathematical STATEMENT-DISPUTED. The existing orientation node already carries the finite-purity and coefficient-transport construction pointers, so no purity proof or forbidden SGA route is introduced here.

The existing expanded node thm-sf-dual-perfect has a relative-form clause giving this theorem together with extra compatibilities; it is recorded in blueprint.same_as. I did not create another copy or use the whole expanded theorem as a substitute for a split.

The inherited lean_audit ranges and transitive open list are stale for the supplied source: Orientation.lean's two declarations are at 183 and 197, not 436 and 456. The listed declaration AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine and its cited file are absent in the supplied slopmaster2 checkout; a declaration-name search in the specified upstream master also found none. I cannot extract a statement from an absent declaration. The proof here does not use an affine cohomological-dimension theorem; I have left the audit fields untouched and report the mismatch for regeneration.

## What could not be finished

No mathematical argument is deferred by this split. Existing dependencies retain their own states. Readiness is conditional on the required no-push dry run printing OK; no push is authorized in this turn.

## Not duplicates

No new nodes. The whole-DAG and blueprint searches for dualizable, biduality, twist-interchange and dual-perfect found the component statements reused here and thm-sf-dual-perfect. The missing sketch proposition is a blueprint section/unit record, not a DAG statement. Its formal dual-pair calculation is expanded inside this item's proof, so no duplicate clause node is proposed.

## Review by Q75

I read the chapter and unit, the current main-20261015 item statement and proof, the sketch perfect-biduality statement and its dual-pair proof, both detailed perfect-dual statements, the actual statements of every node used in the six steps, and the supplied Orientation.lean and Perfect/Dual.lean declarations. I also read Stacks Tag 08JJ, sites-cohomology.tex, lemma-dual-perfect-complex, for the ringed-site comparison; the argument here is the symmetric monoidal dual-pair argument rather than a substitution of a ringed-space theorem or a discrete non-torsion sheaf category.

Step 1 takes precisely the orientation isomorphism from sk-def-sf-orientation, the Hom bifunctor from clause (i) of sk-def-sf-operations, and the displayed shifted comparison from sk-lem-sf-twist-interchange. The orientation is inverted before applying Hom. The statement applies to a relative f and does not require the base to be a point.

Step 2 uses the adjunction in sk-def-sf-operations to define the comparison and prove its naturality by equality of transposes; sk-lem-sf-twist-interchange supplies invertibility at M=L. Its evaluation formula is the defining adjunction equation. I removed prop-sf-dualizable-hom after reopening its statement: it assumes separated X, while the assigned relative theorem allows the general base of the orientation setting. The proof therefore does not borrow its stronger hypotheses.

Step 3 uses prop-sf-dualizable only for its stated perfectness of the coefficient dual. Its local finite-projective hypothesis is supplied by the equivalence explicitly stated in sk-def-perfect. The non-sketch lem-sf-twist-interchange explicitly says the Tate object is locally constant of rank one and invertible. The remaining tensor-and-shift model calculation is written out using def-weil-site-perfect-complex, including its completed integral, localized rational and common finite-field conventions. No uncompleted tensor is substituted for completed tensor. This step supplies perfectness before the later application of theta to DK or K-dual.

Step 4 uses sk-def-perfect for an actual dual pair, not for an unproved assertion of biduality. The adjunction of sk-def-sf-operations identifies the chosen dual with coefficient Hom by evaluation. The displayed inverse to coefficient biduality is checked by exactly the two triangle identities. This is a finite formal calculation from the definition, not an invocation of the absent sketch node or a new node restating the item.

Step 5 uses the same Hom adjunction and opposite-twist interchange, whose perfect first variable has been justified in Step 3. It specifies cancellation on all Hom sets and the corresponding internal maps by transposition, with both inverse formulas. The evaluation equation proved in Step 2 then identifies the transported canonical relative biduality with coefficient biduality. This addresses maps, not merely isomorphic double-dual objects. The derived symmetry retains the Koszul signs and the shift 2d is even.

Step 6 proves naturality of biduality by transposing evaluation and writes the inverse on morphisms. The identity D(delta_K) delta_DK=1 is the evaluation adjunction's triangle calculation, so the asserted anti-equivalence follows with D itself as inverse. The two definitions cited give the absolute names and omega; no absolute Verdier biduality theorem is used to establish a relative result.

I checked K=0, d=0 (including f=id), the unit, a shifted unit, and finite-projective summands. The formulas retain the graded sign for an odd shift of K, and do not divide by a scalar or assume a nonzero stalk, connectedness, properness, finite-dimensional global cohomology or cohomological dimension. Empty schemes cause no failure. Every cited node's actual hypotheses were checked at its use. All coefficient stages stay within the setting fixed by the orientation.

Against delivery-errors B–E: no new nodes need statement-only or leaf checks; exact quotations cover every uses entry; no step borrows another node's proof, no new node duplicates a clause, and no non-elementary geometric fact or coefficient comparison is silently introduced. The unit route remains orientation, twist interchange and coefficient-dual biduality, whose elementary triangle details are expanded. There is no SGA citation. Only the unit's realization fields are changed. All writes are in this sandbox; no git command or compiler has been run in a reference checkout.

On the final C4 check I also opened def-coefficient-twists-detailed and cited it in Step 3: its negative-twist definition is the coefficient dual of the positive power. The step now gives the local evaluation/multiplication and basis inverse proving cancellation, rather than attributing the specific inverse Lambda(-d) solely to a statement saying that Lambda(d) is invertible. The citation file has 16 exact step/node pairs.

## Second reading by Q75

- Item statement: checked against `main-20261015/sec-six-functors/sk-thm-sf-dual-perfect/_section.md` and the imported DAG node; all hypotheses (smooth separated finite type, pure relative dimension, orientation, constructible perfect object, relative and absolute cases) agree, with the two absent bibliography IDs rendered as equivalent plain wording for preflight.
- Step 1: checked against `sk-def-sf-orientation`, `sk-def-sf-operations` (i), and `sk-lem-sf-twist-interchange`; the three cited statements supply the orientation map, internal-Hom functoriality, and the displayed twist isomorphism.
- Step 2: checked the transpose definition and naturality against `sk-def-sf-operations` (i) and the invertible twist comparison in `sk-lem-sf-twist-interchange`; the evaluation formula has the required symmetry and orientation map.
- Step 3: checked `prop-sf-dualizable`, `sk-def-perfect`, `lem-sf-twist-interchange`, `def-weil-site-perfect-complex`, and `def-coefficient-twists-detailed`; finite-projective tensoring, all coefficient stages, and cancellation of opposite twists are stated explicitly, so the step is marked non-elementary.
- Step 4: checked the dual-pair definition and adjunction in `sk-def-perfect` and `sk-def-sf-operations`; both inverse formulas are the two triangle identities and establish coefficient biduality.
- Step 5: checked the internal-Hom cancellation on test objects against `sk-def-sf-operations` and the opposite-twist instance of `sk-lem-sf-twist-interchange`; the construction is internal, with explicit inverse maps and the evaluation transpose identifying the canonical biduality.
- Step 6: checked naturality and the anti-equivalence inverse against the adjunction and orientation statements; the arrow inverse and the double-transpose triangle identity are written out, including the absolute specialization.
- New nodes: none; there are no new node statements or Mathlib leaves to audit, and all cited dependency statements were opened in the shared DAG.
- Edge cases: checked zero and shifted unit objects, (d=0) and (f=\mathrm{id}), empty schemes, finite-projective summands, and odd shifts; no step assumes nonzero stalks, connectedness, properness, or a positive dimension.
- Changes made: replaced the two absent bibliography references in the item statement by equivalent plain wording (the smooth-purity orientation and the transpose definition of coefficient biduality), as required by preflight B3; changed Step 3's `elementary` flag to `false` because its perfectness and inverse-twist argument is substantive. No mathematical clause or proof dependency was otherwise changed.
- Delivery-errors B–E: no new-node B checks apply; every non-elementary dependency is a cited node, no step uses a cited proof body, no duplicate node or cycle was introduced, and no SGA 4/4½ source is cited.
