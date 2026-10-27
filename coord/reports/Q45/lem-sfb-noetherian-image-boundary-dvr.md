# Repair report: lem-sfb-noetherian-image-boundary-dvr

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-image-boundary-dvr.json: statement unchanged; short three-step assembly, 1271 characters, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-boundary-affine-local-domain-model.json: new statement-only lemma, status unsplit, no Mathlib match. This carries returned steps 1-3 (2162 characters of argument).
- dag/nodes/sec-six-functors-basics/lem-sfb-local-domain-affine-dvr-square.json: new statement-only lemma, status unsplit, no Mathlib match. This carries returned steps 4-5 (1307 characters of argument).
- citations.json: one exact statement quotation per cited node in each assembly step. searches.jsonl retains the searches made through msearch.py.

Two new nodes; zero new Mathlib leaves. Neither new node has proof steps, proof dependencies or a proof sketch in its statement. The two statements expose complementary constructions, rather than moving the original conclusion into a single lemma. The first constructs local algebra, with no DVR conclusion; the second assumes that local algebra and constructs an affine square, with no global closure or image-point selection.

## Attachments

None for this item or the new nodes. The exact blueprint tag and declaration searches in lean/WeilConjectures found no completed assertion of the item. Sheaf.AlgebraicGeometry.NoetherianImageBoundaryDvr contains AlgebraicGeometry.exists_dvr_of_mem_closure_range_not_mem_range with sorry. The existing project IsLocalRing.exists_isDiscreteValuationRing in WeilConjectures/RingTheory/DiscreteValuationRing/Dominating.lean:250 only gives an injective local map to an unspecified DVR; it does not prescribe the source residue field as its fraction field. Ideal.exists_isDiscreteValuationRing_of_lt in that file similarly does not give the prescribed generic map. Neither is an attachment.

The pre-existing specialization node remains available to the worker of the first new node, and the pre-existing full 00PH node remains available to the worker of the second. They are not being recreated. The previous stage-1 report is retained below as historical material; its old file list and five-step assembly are superseded by this repair.

## WANTED

None. All sources are present locally.

## Findings and repair of the return

The sandbox initially contained only dispatcher marker files, with no node, report or searches.jsonl. I therefore continued the delivered proof by reading its current repository node and the previous NP stage-1 report. I kept the item's statement and all existing source, Lean and review metadata intact. The delivery tool will overlay only split-owned fields on current main. I made no git call and wrote no file in the shared repository or launcher.

The return requested work distribution, not a shortened description of the same unsplit argument. Every part of the old proof is assigned below, and its exact text is retained in the appendix. The new local-model node includes the image-specialization choice and both affine charts, not just its ring calculations; the new affine-square node includes residue-field finite generation, not just the final composition. Both nodes are delivered statement-only so that their proofs can be assigned independently. The old proof's labels calling some calculations elementary do not remove those calculations from the tasks: this explicit re-split moves the full 2162- and 1307-character construction packages into the two new tasks as requested.

The chapter and unit were read: sec-six-functors-basics and sk-thm-sf-ctf-stability. This stays below the existing Noetherian DVR properness input on the alteration/rigidity route of det-thm-sf-ctf-stability-direct-images. No unit route was replaced. tools/blueprint_refs.py ancestor returns a null blueprint ancestor for this already-created chain; I retained that null and the precise inherited place, prepending this item to each new node's via list. Searches of the whole blueprint for 0CM2, 00PH, local domain, prime quotient, dominating local, boundary point and affine square found no matching blueprint statement. The boundary-point hits concern lisse sheaves on curves, and the local-domain hits concern DVR characterizations or ordinary valuation domination. Whole-DAG searches by tags and keywords and project-source searches were also read.

## Source error retained from the previous delivery

Stacks limits.tex, Tag 0CM2, limits-lemma-reach-point-closure-Noetherian, has an additional 'Moreover' claim allowing the fraction field to be the generic-component residue field even for a trivial specialization. For the identity of Spec(F_p), that field would be F_p; a subring of F_p is a field and cannot be a nonfield DVR. The item's existing boundary restriction already avoids this error and is unchanged. No new statement dispute or weakening is introduced. The proof never needs a generic component replacement. The strict inclusion q properly contained in p ensures the local domain is not a field.

## Not duplicates

lem-sfb-boundary-affine-local-domain-model vs lem-sfb-noetherian-image-boundary-dvr: the item asks for a DVR square; the new lemma constructs the affine specialization charts and explicit nonfield local-domain subring of the source residue field, without any DVR or valuative square.

lem-sfb-boundary-affine-local-domain-model vs lem-sfb-noetherian-dvr-properness: the existing statement is a criterion for properness, not a construction of affine charts and a residue-field local-domain model.

lem-sfb-boundary-affine-local-domain-model vs lem-sfb-local-domain-fg-field-dvr: the existing statement constructs a DVR from an already supplied local domain and field extension; the new statement constructs the local domain itself from a boundary point, with no DVR conclusion.

lem-sfb-boundary-affine-local-domain-model vs lem-sfb-generic-dvr-properness-criterion: the existing statement is a properness criterion for integral schemes, not the local algebra of a missing image point of an arbitrary finite-type scheme morphism.

lem-sfb-local-domain-affine-dvr-square vs lem-sfb-noetherian-image-boundary-dvr: the new lemma is a ring-level construction from an already supplied local subring of a residue field, with its factorization and fraction-field identification as hypotheses; it performs neither image-point selection nor local-model construction.

lem-sfb-local-domain-affine-dvr-square vs lem-sfb-noetherian-dvr-properness: the existing properness criterion has no assertion giving this prescribed residue-field DVR and the compatible affine spectrum square.

lem-sfb-local-domain-affine-dvr-square vs lem-sfb-local-domain-fg-field-dvr: 00PH supplies the dominating subring for an already given finitely generated field extension. The new task includes proving that the finite-type residue extension is finitely generated and verifying equality of the two spectrum composites and contraction of the closed point for the specified B and C maps.

lem-sfb-local-domain-affine-dvr-square vs lem-sfb-local-domain-same-field-dvr: the old node is only same-fraction-field domination. The new task has a potentially larger residue field and prescribed affine maps and centre, so that statement does not supply its conclusions.

lem-sfb-local-domain-affine-dvr-square vs lem-sfb-local-domain-birational-dimension-one: the existing statement constructs a dimension-one birational local overring, not a DVR in a prescribed residue field and a commuting affine square.

lem-sfb-local-domain-affine-dvr-square vs lem-sfb-generic-dvr-properness-criterion: the existing statement tests properness, whereas the new statement constructs a square with given affine ring maps and a prescribed generic field.

## Review by Q45

I read the complete statement and proof of Stacks 0CM2 in limits.tex:3740-3781 for the item and both extracted statements. I also read its specialization input in morphisms.tex at lemma-reach-points-scheme-theoretic-image (02JQ), and algebra.tex:29312 onward, lemma-exists-dvr (00PH), including its nonfield and finite-generation hypotheses. No SGA source is used. The previous stage-1 proof and report and current Lean statement were compared, and the latter is still sorried. No compilation was run.

For assembly step 1 I opened the new local-model statement after writing it. It assumes exactly the item's finite-type morphism, locally Noetherian target and boundary point. It supplies x, both affine charts, their finite-type ring map, the three primes, the strict inclusion, the explicit R embedding, nonfield Noetherian locality, fraction field and maximal-ideal contraction. Thus the next step does not use an unmentioned construction from a cited proof. The proof task assigned to this node is all of returned steps 1-3: use the existing quasi-compact closure-specialization theorem; choose a member of the Noetherian affine covering; observe that opens contain generalizations; choose a finite-type source affine chart; compute the kernel, invert denominators, compare fractions, prove Noetherianity through ideal generators and exhibit a nonzero nonunit from p minus q. These arguments have not been discarded or compressed into an unexplained word. They are preserved verbatim below for the worker who will prove the node. The source explicitly constructs the image of the target local ring in the source residue field; the affine quotient-localization is that image with its kernel made explicit.

For assembly step 2 I reread the whole new affine-square statement. Its ring map is the finite-type map supplied in step 1, its prime is the source-chart prime r, and its field is L=kappa(r). Its R is exactly the embedded local domain from step 1. That statement supplies the required equality of fraction subfields compatibly with the B action, not merely an abstract isomorphism. The alpha map is the factorization of B to L in the first statement. Its maximal ideal contracts to p by that same statement. These are every hypothesis of the second lemma. Its conclusion supplies the exact square, prescribed fraction field L and special point p needed in the assembly. Its assigned proof is returned steps 4-5: apply the existing finite-type-residue-field finite-generation node to phi and r, apply the full existing 00PH node, define both spectrum maps from C to L and B to R to A, compare the two homomorphisms on b in B, then contract m_A first to R and then to B. I opened both existing statements; the first is for finite-type ring maps with the contracted prime, and the second permits arbitrary finitely generated extensions, not just finite extensions or unchanged fraction fields. No normality, excellence or regularity is used.

For assembly step 3, the square is already an equality of morphisms into Spec B. Composing with V into Y and W into U uses only the restriction identity supplied by the first lemma and associativity of composition. Its closed point p is y by the choice of V, so this is an elementary final step with no missing geometric lifting theorem. The original item's existential field is simply renamed L.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against these actual statements. Every non-elementary fact in the assembly is a cited complete statement. citations.json quotes those statements verbatim. Their proof fields are empty, and their hypotheses introduce all rings, maps, primes, residue fields and spectra; locality, integral domain and fractions are specified inline, with definitions of schemes, finite type, Noetherianity, localization and DVR cited where used. Neither new node depends on the parent. The parent proof has only these two dependencies, so it cannot create a cycle through the old properness route. Existing maintainer tool-use metadata is retained unchanged; the assembly needs no new off-unit tool.

Small cases were checked with the sources open. For the first node, an empty source, a surjective map or a closed image yields no admissible y; no data are falsely requested in those cases. The standard open immersion Spec(k[t,1/t]) into Spec(k[t]) at (t) gives q=0, p=(t), R=k[t]_(t) and L=k(t). Replacing B by k[t,e]/(e^2) makes q=(e) and p=(t,e), and the quotient removes nilpotents before the domain argument. The forbidden equality p=q would make R a field, so strictness is necessary. For the second node, C=B[1/t,z] gives L=k(t,z), illustrating why the full finitely generated extension input is necessary. A singular R is allowed: the claim never asserts R itself is a DVR. A field R is excluded explicitly. The maps alpha and beta need not be injective, and the proof compares their composites rather than claiming pointwise image containment gives scheme factorization. No point y is required to be closed globally.

All recorded searches were run with msearch.py and their hits read; both nodes have multiple semantic phrasings, Loogle and Mathlib grep. LeanSearch was rate-limited for the second node and is recorded as unavailable. LeanFinder and Loogle succeeded. The quotient-residue-field fraction-ring instance and nonfield localization theorem give pieces of the first construction, not its geometric chart choice and compatible subring package. The Mathlib valuative-square projections assume an existing square, and ordinary valuation domination does not supply a DVR in the required field. I inspected the relevant candidate interfaces in Localization/AtPrime/Basic.lean, LocalRing/ResidueField/Ideal.lean, IdealSheaf/Basic.lean, ResidueField.lean, ValuativeCriterion.lean, and Valuation/LocalSubring.lean. No complete match or one-line specialization was found. The original item searches are retained and the searches from this session appended. No service failure is called an absence result.

No non-elementary assembly step exceeds 2000 characters; their total is 1271. There are exactly two new proof tasks of comparable size (2162 and 1307 characters in the old proof). The following unchanged old text is their detailed handoff argument, outside the statement-only node files.

## Unfinished work

The two new statement-only lemmas await their own stage-1 workers, as required by the return. No part of the parent assembly remains unsupported.

## Preserved returned argument and assignment

Returned steps 1-3 belong to lem-sfb-boundary-affine-local-domain-model. Returned steps 4-5 belong to lem-sfb-local-domain-affine-dvr-square. These are the original text, not a shortened substitute:

Returned step 1 (627 characters):

Finite type includes quasi-compactness. Apply [lem-sc-picard-closure-specialization] to $g$ and $y$ to choose $x\in U$ such that $z=g(x)$ specializes to $y$. Since $y$ is outside the image, $z\ne y$. Choose an affine neighbourhood $V=\operatorname{Spec}B$ of $y$ with $B$ Noetherian, from the covering in local Noetherianity. The point $z$ belongs to $V$: otherwise the closed complement of $V$ would contain $z$ and hence its specialization $y$. By local finite type choose an affine neighbourhood $W=\operatorname{Spec}C$ of $x$ in $g^{-1}V$ such that the restricted map is induced by a finite-type ring map $\varphi:B\to C$.

Returned step 2 (897 characters):

Write $\mathfrak p\subset B$ for $y$, $\mathfrak r\subset C$ for $x$, and $\mathfrak q=\varphi^{-1}(\mathfrak r)$ for $z$. Specialization in an affine spectrum gives $\mathfrak q\subsetneqq\mathfrak p$: the closure of $\{\mathfrak q\}$ is exactly the set of primes containing $\mathfrak q$, and distinct points have distinct primes. Put $L=\kappa(\mathfrak r)$ and $R=(B/\mathfrak q)_{\mathfrak p/\mathfrak q}$. The map $B\to C\to L$ has kernel $\mathfrak q$, and every element of $B\setminus\mathfrak p$ has nonzero image in $L$. It therefore embeds $R$ into $L$, with $(b+\mathfrak q)/(s+\mathfrak q)\mapsto\varphi(b)/\varphi(s)$. Its maximal ideal is $(\mathfrak p/\mathfrak q)R$. Its fraction field is $K=\operatorname{Frac}(B/\mathfrak q)=\kappa(\mathfrak q)$, with the given embedding into $L$: taking fractions after localization gives the same fractions as taking them before localization.

Returned step 3 (638 characters):

The ring $R$ is Noetherian directly from the ideal definition. Every ideal of $B/\mathfrak q$ is the image of its inverse image in $B$, so images of finitely many generators generate it. Every ideal of its localization $R$ is generated by the images of its contraction to $B/\mathfrak q$: for $a/s$ in the ideal, $a/1=s(a/s)$ belongs to it. Thus finite generators of the contraction generate the localized ideal. The ring $R$ is a nonzero local domain. Choose $b\in\mathfrak p\setminus\mathfrak q$. Its image in $R$ is nonzero, since $B/\mathfrak q$ embeds into its fraction field, and lies in the maximal ideal. Hence $R$ is not a field.

Returned step 4 (592 characters):

Apply [lem-weil-pbc-finite-type-residue-field-extension-finitely-generated] to $\varphi:B\to C$ and $\mathfrak r$. Its hypotheses hold because this is the finite-type ring map chosen in step 1, and $\varphi^{-1}(\mathfrak r)=\mathfrak q$. It states that $L=\kappa(\mathfrak r)$ is a finitely generated field extension of $\kappa(\mathfrak q)=K$. Now [lem-sfb-local-domain-fg-field-dvr] applies to the nonfield Noetherian local domain $R\subseteq K\subseteq L$. Obtain a discrete valuation subring $A\subseteq L$ containing $R$, with fraction field $L$ and $\mathfrak m_A\cap R=\mathfrak m_R$.

Returned step 5 (715 characters):

Set the field called $K$ in the conclusion to $L$. Define $u:\operatorname{Spec}L\to W\hookrightarrow U$ by $C\to\kappa(\mathfrak r)=L$, and define $v:\operatorname{Spec}A\to V\hookrightarrow Y$ by $B\to B/\mathfrak q\to R\hookrightarrow A$. Both composites $\operatorname{Spec}L\to Y$ factor through $V$ and are induced by the same ring map $B\to L$: on $b\in B$ both send $b$ to the residue of $\varphi(b)$ in $L$. Functoriality of spectra therefore gives $g\circ u=v\circ j$. Finally the inverse image of $\mathfrak m_A$ in $B$ is $\mathfrak p$, because its contraction to $R$ is $(\mathfrak p/\mathfrak q)R$ and this ideal contracts to $\mathfrak p/\mathfrak q$ in $B/\mathfrak q$. Thus $v(s_A)=y$, as required.

## Preserved previous stage-1 report (NP; historical)

The following report was read from coord/reports/NP/lem-sfb-noetherian-image-boundary-dvr.md. Its attachment, source-error and search findings remain relevant; its old file list, dependency list and validation describe the previous delivery, not this repaired one.

# Stage-1 report: lem-sfb-noetherian-image-boundary-dvr

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-image-boundary-dvr.json`: item, statement unchanged, split into five steps following Stacks 0CM2 in affine coordinates. No Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-local-domain-fg-field-dvr.json`: one new statement-only unsplit node, full algebraic Stacks 00PH; no Mathlib match. This is the only new node; zero Mathlib leaves are created.
- `citations.json`: 13 entries, one per proof-step/node pair, each quoting the cited statement verbatim.

## Attachments

No attachment for the item. Searches of `lean/WeilConjectures/` by the exact blueprint tag and by closure, boundary, and DVR terminology found no declaration giving this diagram under these hypotheses.

`AlgebraicGeometry.exists_specializes_of_mem_closure_range` belongs to existing `lem-sc-picard-closure-specialization` (`lean/WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean:70` in this snapshot). This is only the specialization input, not an attachment for the item. I did not edit that existing node. The already available `IsLocalRing.exists_isDiscreteValuationRing` in `RingTheory/DiscreteValuationRing/Dominating.lean:250` provides an injective local map but does not fix the fraction field or provide its required extension to the chosen source residue field, so it cannot replace the new 00PH node.

## WANTED

None. All proof sources needed are present in `literature/stacks-project/`.

## Findings and corrections

The imported item is correct as stated. Its restriction to points outside the image ensures the two primes in the affine target are distinct, and therefore ensures the local domain to which 00PH is applied is not a field. I kept every hypothesis and every conclusion. There was no existing split in the sandbox to recover.

I read Stacks `limits.tex`, label `lemma-reach-point-closure-Noetherian` (0CM2), including its proof, and its cited inputs `morphisms.tex`, label `lemma-reach-points-scheme-theoretic-image` (02JQ), and `algebra.tex`, label `lemma-exists-dvr` (00PH). The 0CM2 source also claims that the fraction field can be fixed to the residue field of a generic point of a component even when the selected specialization is trivial. That extra claim fails for the identity of Spec(k) when k is algebraic over a finite field: it would require a nonfield DVR with fraction field k, whereas every subring of such a field is itself a field (the inverse of each nonzero element is a power of it). The current boundary-only item already excludes this issue. There is no statement dispute in this delivery and no further statement correction is needed. My proof does not replace the source point by a generic component point: 00PH only needs its residue extension to be finitely generated.

I expanded the source's local-ring map as the explicit inclusion `(B/q)_(p/q) -> kappa(r)`. This makes the kernel, inverted denominators, fraction field, nonfield hypothesis, commutative diagram and special-point image independently checkable. No additional lemma is hidden in these computations. The new 00PH node is an algebraic existence theorem with arbitrary input local domain and field extension, not a renamed clause of the geometric item.

## Not duplicates

lem-sfb-local-domain-fg-field-dvr vs lem-sfb-local-domain-same-field-dvr: the existing 00PH specialization only constructs a DVR inside the unchanged fraction field K; the new statement prescribes any finitely generated extension L/K as the fraction field, which is needed for the source residue field.

lem-sfb-local-domain-fg-field-dvr vs lem-sfb-generic-dvr-properness-criterion: the existing node is a properness criterion for an integral scheme morphism; it mentions 00PH as a proof input and does not state the algebraic existence theorem, much less its field-extension version.

lem-sfb-local-domain-fg-field-dvr vs lemma-nagata-local-domain-valuation-dominates: the existing statement allows arbitrary field extensions and gives a valuation ring without discreteness. It cannot supply the DVR conclusion.

lem-sfb-local-domain-fg-field-dvr vs lemma-nagata-valuation-ring-extension: the existing statement extends an already given valuation ring by another valuation ring; it gives neither a DVR nor the Noetherian local-domain construction.

lem-sfb-local-domain-fg-field-dvr vs lem-sbc-noetherian-specialization-trait: the existing geometric statement traces a specialization but does not prescribe the fraction field as L or lift a selected field-valued source point.

I searched the whole DAG for 00PH, finitely generated field extensions, local-domain domination, residue-field finite generation, and image-closure specialization. Blueprint searches for `00PH`, `finitely generated field extension`, `dominat`, `discrete valuation`, `image boundary`, and `closure-specialization` found no blueprint node stating the new algebraic theorem or the item. The ancestor tool reports `blueprint.from.node = None` for this already-created chain. I retained the item's recorded null ancestor and explicit place, and prepended the item to the new node's inherited via chain.

## Review by NP

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the node files and the sources named above. The new node's full source is precisely 00PH, not the same-field specialization, and its statement introduces R, K, L, their embeddings, field generation, domination and fraction fields. No proof has been placed in its statement or proof fields. Definitions of Noetherian ring, field and DVR are cited, while local integral domain, fractions, finitely generated field extension and domination are defined inline. The item retains all its original statement definitions. JSON has single TeX escapes and no hollow definitions.

For step 1 I opened `lem-sc-picard-closure-specialization`, which states exactly that a point in the closure of the image of a quasi-compact morphism is a specialization of an image point. The finite-type definition supplies quasi-compactness and the affine finite-type charts. The local-Noetherian definition supplies a covering by affine spectra of Noetherian rings, so I choose a member of that covering; I do not need the stronger theorem that every affine open has Noetherian coordinate ring. Closure of a singleton proves that this chart also contains the general point. I declared the generic closure-specialization result as an off-unit tool rather than silently changing the unit route.

For step 2 I opened the spectrum, localization-at-prime and residue-field definition nodes. On the chosen affine charts the preimage prime q represents g(x). The closed set V(q) computes specialization, and the missing-image hypothesis implies q is strictly smaller than p. The quotient B/q embeds in L because q is the kernel; elements outside p are outside q, hence invertible in L. Thus the displayed fraction formula embeds R in L. The maximal ideal and fraction field identifications are the elementary localization and residue-field calculations recorded in the step; no field-extension lifting is being assumed here.

For step 3 I checked the Noetherian definition literally means every ideal is finitely generated. The proof explicitly lifts ideals through the quotient and contracts them through localization, proving the needed permanence in two ideal-generator calculations. It does not treat a theorem about Noetherian rings as supplied merely by a definition. A chosen b in p minus q stays nonzero in the domain's localization and is a nonunit, proving R is not a field. This verifies exactly the hypothesis that the unrestricted 0CM2 proof can overlook.

For step 4 I opened `lem-weil-pbc-finite-type-residue-field-extension-finitely-generated`. It applies to the finite-type ring homomorphism B -> C, not to a different or unstated notion of morphism, and its primes are r and its inverse image q. Its conclusion is finite generation of kappa(r) over kappa(q), which equals the fraction field of R from step 2. I then reread the new 00PH statement and the source: R is a Noetherian local domain, R is not a field, and L/K is finitely generated. All four requirements hold before invoking it. It supplies both the prescribed fraction field L and contraction of the maximal ideal; the same-field node would not suffice.

For step 5 I opened again the spectrum, residue-field and localization nodes. These define the actual maps C -> L and B -> R -> A. Commutativity is checked by equality of the maps on every b in B. The special-point condition follows by two explicit contractions of the maximal ideal, ending at p. This uses the actual domination conclusion of 00PH and does not infer scheme factorization merely from containment of point images. The field in the item's conclusion is L, a permitted renaming of its existentially bound K.

For small cases, the empty source and a point already in the image give no boundary input. For `Spec(k[t,t^-1]) -> Spec(k[t])` at (t), q=0, p=(t), R=k[t]_(t) and L=k(t), recovering the usual trait. With source `Spec(k[t,t^-1,z])`, L=k(t,z), so the field-extension clause of 00PH is essential. A nilpotent thickening in B is removed by the prime quotient before using a domain. A singular example B=k[s^2,s^3], q=0, p=(s^2,s^3) is allowed: no normality, excellence or regularity is assumed. For the new 00PH node, L=K recovers the existing same-field statement; R already a DVR works; transcendental and inseparable finite extensions are included by the source's unrestricted finitely generated extension hypothesis. The excluded field case is necessary, as the algebraic-over-finite-field example shows.

I read all Mathlib search hits and their relevant source interfaces. Searches used only the required msearch.py command and are logged verbatim. Both semantic phrasings returned DVR characterizations or ordinary valuation extension interfaces, not this existence theorem. In particular `Valuation.HasExtension` is a compatibility hypothesis on given valuations; it is not an existence theorem. The item searches likewise returned the general valuative criterion (requiring a lifting assumption) and generalizations through a stalk, neither of which supplies this diagram. One exploratory grep mistakenly named `Valuation/Extend.lean`; its empty result was not used as absence evidence or recorded in a node. The corrected file `Valuation/Extension.lean` was read and searched. No service failure was reported as absence.

All five proof steps are under 1000 characters, so no step exceeds the long-step threshold. I checked that each quoted citation is an exact substring of its node's statement and that proof_deps equals the union of step uses. The only new dependency is strictly algebraic and cannot depend on the geometric item. No SGA source is used. No Lean was written or compiled, and the read clone and launcher files were untouched.

## Unfinished work

Only the new statement-only 00PH node remains to be split in a future stage-1 item, as required by one-level splitting. Nothing in this item's split is left unproved except the explicitly cited nodes.

## Validation

The server dry run passed preflight, DAG and split checks. I corrected the report-only line reference for the existing specialization declaration from 74 to 70 after reading the exact declaration line, then reran the final dry run before pushing.
