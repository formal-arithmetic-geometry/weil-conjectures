# Worker report: Q146

Repair of lem-zl-condensed-dualizable-local-perfect-models, 2026-10-22.

## Files written

- dag/nodes/sec-zeta-weil/lem-zl-condensed-dualizable-local-perfect-models.json: unchanged statement; five assembly steps, 2054 text characters.
- dag/nodes/sec-zeta-weil/lem-zl-condensed-wcontractible-projective-calculus.json: statement, unsplit; no Mathlib match. Local cone representatives, exact realization, shifts, zero, and arbitrary scalar extension.
- dag/nodes/sec-zeta-weil/lem-zl-condensed-irreducible-generic-scalar-model.json: statement, unsplit; no Mathlib match. Generic stalk and component-section descent on a prescribed cover.
- dag/nodes/sec-zeta-weil/lem-zl-condensed-finite-closed-model-lifts.json: statement, unsplit; no Mathlib match. Canonical henselian lifts of prescribed closed-fiber models, uniqueness, and covering verification.
- citations.json: exact statement quotes for every node cited by every parent proof step.

## Attachments

None. Both project declarations in lean/Sheaf/AlgebraicGeometry/CondensedDualizableLocalPerfectModels.lean have sorry proofs. Searches of lean/WeilConjectures/ by blueprint id and by local-perfect/scalar/generic/henselian terms found no declaration proving the item exactly. The generic derived-category cone closure theorem in WeilConjectures/CategoryTheory/DerivedCategory/Monoidal/DualizableProjectiveUnit.lean:336 does not state the new projective representative and scalar comparison package; it is available as a tool to its future worker, not an attachment of that package.

## WANTED

None. HRS and Bhatt--Scholze PDFs are present and were read using pdftotext to stdout, without writing to the repository.

## Return repaired and continuation

The repair note releases stage 1 with keep_plan true and requires at least two comparable new argument nodes and an assembly proof of at most 3000 characters. The sandbox initially contained only dispatcher .brief files, no retained nodes, report or search log. I copied the current live node, including its statement, citations/search history, blueprint metadata, reviewed and Lean records. original-proof.json preserves its seven original proof steps exactly for this repair's audit; these are also reproduced below in full. Three statement-only nodes now carry separate arguments, with statement lengths 2006, 2386 and 2410 characters. They have no proof steps or proof dependencies. The parent statement and original statement dependencies are unchanged. The parent retains every structural argument; this is not an unchanged re-push or a shortened proof offered alone.

## Distribution of the original arguments

Old Step 1 is the cone/shift/zero part of wcontractible-projective-calculus; the parent Step 1 retains the basis and locality assembly. Old Step 2 is its arbitrary scalar-extension part; parent Step 2 performs the two locality descents. Old Steps 3 and 4 become irreducible-generic-scalar-model, including the existence of the generic perfect P, the component object M, the derived comparison on S_eta, and descent along the section with the same P. Old Step 5 remains the concrete finite-component input selection in parent Step 3: reduced induced structures, pullback, prescribed w-contractible covers, application of the irreducible lemma. Old Step 6 and the finite-cover part of old Step 7 become finite-closed-model-lifts, including the precise H_A construction, ind-etaleness, reduction, henselianity, w-contractibility, lifting the isomorphism and inverse, and image/flat/quasi-compact cover check. The Zariski and empty-case part of Step 7 remains written out in parent Step 5. None of the original arguments is discarded; the original text is reproduced below to give the three future workers the full reasoning without putting proof sketches inside their statements.

## Review by Q146

I read Hemo--Richarz--Scholbach Definition 3.3 and its stability observation, Definition 3.5, Lemma 4.1(1)-(2), Proposition 4.3(3), Corollary 4.4, Lemma 4.5 and Theorem 4.13 including diagram (4.4) and the finite-component paragraph. For the third new statement I additionally read Bhatt--Scholze Definition 2.2.10, Lemmas 2.2.12-2.2.15, Proposition 2.3.3 and Lemma 6.1.1. I kept the previous repair's distinction between w-strictly local and w-contractible: BS 2.2.15 establishes only the former for arbitrary quotients. The proof therefore first covers the components by w-contractible affines and lifts those covers; no false quotient-contractibility assertion was reinstated. The blueprint ancestor and its current blueprint_update were read; this remains a local coefficient-theory tool below relative duality, without changing a chapter or unit route.

For parent Step 1 I opened the statements of the new projective calculus, sk-thm-pe-weakly-contractible-basis and lem-zl-condensed-lisse-proetale-locality. The calculus explicitly covers every local morphism of dualizable objects, not just objects already exhibited in a scalar model; the basis theorem supplies the cover; locality supplies exact inverse images and detection of dualizability. These statements give exactly the stability assembly. For Step 2 the same calculus states perfect arbitrary base change and its derived realization isomorphism, and locality includes scalar pullback compatibility and covers without a component restriction. Thus its use on the cover members is valid without irreducible-component or flatness assumptions.

For Step 3 I opened lem-weil-pbc-reduced-induced-closed-subscheme, lem-sc-irreducible-components-cover, the locality statement and lem-weil-pbc-source-wcontractible-extension. The first explicitly gives reduced affine Spec(A/I) on each affine open; the second says the components cover; locality preserves dualizability for every scheme morphism, including closed immersions; the last provides a faithfully flat ind-etale w-contractible affine algebra without a nontriviality hypothesis. The new generic lemma applies because each irreducible component is nonempty and affine. It accepts this prescribed cover rather than merely asserting existence of an unrelated one, so its conclusion supplies exactly the inputs of Step 4. The zero ring/empty affine case is handled with no components.

For Step 4 I read the new finite-closed-model-lifts statement and its named definition dependencies. It accepts arbitrary finitely many closed subsets covering X, not just irreducible components, and arbitrary supplied perfect models and isomorphisms. Its conclusion specifies C_a=H_A(Cbar_a), the closed-fiber identification, henselian pair, and the actual pro-etale family. Its claim is strictly below the item: it assumes all scalar models on the closed covers and proves their extension. It does not assert local models for an arbitrary K. Fully faithful restriction is applicable to both objects: pullback of K is dualizable by locality and scalar models are dualizable by the first new lemma on the w-contractible lift. Lifting the inverse and using faithfulness proves that the lifted arrow is an isomorphism; faithfulness also gives uniqueness. This detailed argument is retained in old Step 6 below.

For Step 5 I read def-weil-pbc-proetale-site, which states the site and its fpqc covering rule. Only restriction to open neighborhoods, elementary finite irreducible closed-cover topology and composition of covers remain here. Intersections of an irreducible closed subset with an open are empty or irreducible closed in the relative open; finite unions therefore remain finite-component. The empty cover is valid for the empty scheme. No long non-elementary step remains in the parent (every text is under 2000 characters).

I checked each new statement on zero objects, the zero coefficient ring, shifted complexes and identity/zero maps. Bounded finite-projective summands remain summands after arbitrary base change, so no hidden flatness is needed. Nonreduced irreducible affines are allowed: the generic lemma uses the topological generic point, not integrality. In the third statement the closed covering need not be disjoint and models need not agree on different members; only local models, not gluing a common scalar complex, are asserted. For a one-element cover with I=0 the canonical lift is the existing ind-etale algebra and the isomorphism assertion reduces to restriction along the identity. For an empty finite family the covering assumption forces X empty. These tests expose no false clause.

I searched the whole DAG and blueprint before writing the new files: blueprint_refs searches for dualizable, w-contractible, scalar, perfect constant, finite closed, generic scalar and projective calculus, plus DAG keyword and source-place searches. I read the nearby evaluation, locality, generic-component scalar transport, component coefficient comparison, flat scalar realization, projective triangle closure and henselian rigidity statements. None supplies the three new conclusions. The logged Mathlib searches use two independent semantic phrasings (LeanFinder and LeanSearch), Loogle and source grep for each new statement. All responses were read. The initial IsHenselianRing Loogle pattern was rejected as an unknown identifier; I retained this actual diagnostic and ran the valid CondensedMod, CategoryTheory.Functor.FullyFaithful query. Its one hit is ordinary discrete module full faithfulness (read at Mathlib/Condensed/Discrete/Module.lean:146), not henselian derived lifting. The closest projective hit is CochainComplex.isKProjective_of_projective (read at Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean:113), which is an input for representing maps and does not prove the condensed evaluation/scalar result. No fabricated searches or Mathlib matches are recorded.

The newly cited parent statements were opened after writing; citations.json copies their actual text, and also copies the existing cited statements exactly. Cross-unit scheme-topology tools retained by parent Step 3 and the basis theorem are declared in split_report.tool_uses as before; the proof route is unchanged. No new node depends on the parent. The evaluation node used in the generic statement has no dependency back to the parent, so the extraction introduces no cycle.

## Not duplicates

lem-zl-condensed-wcontractible-projective-calculus vs lem-zl-condensed-wcontractible-lisse-evaluation: evaluation states an equivalence; the new statement supplies strict chain representatives and cone/scalar perfectness, with no arbitrary-scheme local-model assertion.

lem-zl-condensed-wcontractible-projective-calculus vs lem-sf-perfect-ring-triangle-closure: ring triangle closure has no condensed realization or arbitrary scalar comparison.

lem-zl-condensed-wcontractible-projective-calculus vs lem-zl-flat-condensed-scalar-realization: that statement assumes flat coefficient sections and asserts exactness on all ordinary modules; the new statement concerns perfect complexes and imposes no flatness.

lem-zl-condensed-wcontractible-projective-calculus vs lem-pc-ring-derived-map-representative: chain-map representability alone does not state the derived condensed realization, cone and scalar assertions.

lem-zl-condensed-irreducible-generic-scalar-model vs lem-zl-generic-fiber-components-section: the existing statement gives the geometric section and site square; the new statement extracts P at the generic point and descends the given scalar model with that same P.

lem-zl-condensed-irreducible-generic-scalar-model vs lem-zl-generic-fiber-component-section: the existing statement is only a topological component-section theorem, not a scalar model theorem.

lem-zl-condensed-irreducible-generic-scalar-model vs lem-zl-generic-component-derived-scalar-transport: abstract equivalence/scalar compatibility does not construct or descend a generic perfect model.

lem-zl-condensed-irreducible-generic-scalar-model vs lem-zl-condensed-wcontractible-lisse-evaluation: evaluation gives perfect complexes over the section ring of U, not over Gamma(*,Lambda) selected at the generic point.

lem-zl-condensed-finite-closed-model-lifts vs lem-zl-condensed-henselian-lisse-rigidity: rigidity assumes a henselian pair; the new statement constructs the ind-etale lift from supplied closed-cover data, lifts the prescribed models and verifies the resulting covering.

lem-zl-condensed-finite-closed-model-lifts vs lem-zl-henselian-indetale-closed-lift: henselianity alone gives neither extension of scalar-model isomorphisms nor a finite pro-etale covering.

lem-zl-condensed-finite-closed-model-lifts vs lem-exc-closed-lift-reduction: the reduction identity gives neither dualizable model extension nor the covering conclusion.

lem-zl-condensed-finite-closed-model-lifts vs def-exc-ind-etale-closed-lift: the definition constructs a colimit; it proves none of the new geometric/model conclusions.

## Original argument retained for the new workers

### Original Step 1

First establish stability, without any restriction on irreducible components. By [sk-thm-pe-weakly-contractible-basis] and [lem-zl-condensed-lisse-proetale-locality], it suffices to check a distinguished triangle on a w-contractible affine $U$. Write $A=\Gamma(U,\Lambda_U)$. The equivalence [lem-zl-condensed-wcontractible-lisse-evaluation] writes any dualizable first and second terms as $F_U(P)$ and $F_U(Q)$ for perfect $A$-complexes, and represents the arrow by an arrow $P\to Q$ in $D(A)$. Choose bounded finite-projective representatives using [def-pc-perfect-ring-complex]. By [lem-pc-ring-derived-map-representative] that arrow is represented by a chain map $p^\bullet\to q^\bullet$. Its cone has terms $q^n\oplus p^{n+1}$, again bounded and finite projective. Exactness of $F_U$ identifies its image with the third term of the triangle, which is therefore dualizable. The zero complex and integer shifts are likewise bounded finite-projective, and the equivalence preserves isomorphisms. Locality descends all these assertions to $X$.

Cited statements: lem-zl-condensed-wcontractible-lisse-evaluation, lem-zl-condensed-lisse-proetale-locality, sk-thm-pe-weakly-contractible-basis, def-pc-perfect-ring-complex, lem-pc-ring-derived-map-representative.

### Original Step 2

We prove the implication from local scalar models to dualizability for every scheme, including cover objects with infinitely many irreducible components. For a perfect $P\in D(R)$ and any scheme $T$, cover $T$ by w-contractible affines $V$ using [sk-thm-pe-weakly-contractible-basis]. Put $A=\Gamma(V,\Lambda_V)$. By [lem-zl-condensed-wcontractible-lisse-evaluation], the restriction of $\Lambda_T\otimes^L_{\underline R}\underline P$ is $F_V(A\otimes_R^L P)$. A bounded finite-projective representative of $P$ computes this derived base change: each projective summand of $R^n$ becomes the corresponding summand of $A^n$. Thus $A\otimes_R^L P$ is perfect, even if $A$ is not flat over $R$, and its image under $F_V$ is dualizable. Apply [lem-zl-condensed-lisse-proetale-locality] first to this cover of $T$, and then to the given covering family of $X$. This proves the reverse implication with varying $P_i$.

Cited statements: lem-zl-condensed-wcontractible-lisse-evaluation, lem-zl-condensed-lisse-proetale-locality, sk-thm-pe-weakly-contractible-basis, def-pc-perfect-ring-complex.

### Original Step 3

For the forward implication first suppose that $X$ is nonempty irreducible affine. Fix a geometric generic point $\eta:\operatorname{Spec}\Omega\to X$. Pullback preserves dualizability by [lem-zl-condensed-lisse-proetale-locality]. The affine geometric point is w-contractible (one strictly henselian local ring and one component), so [lem-zl-condensed-wcontractible-lisse-evaluation] supplies $P\in\operatorname{Perf}(R)$ and $K|_\eta\simeq\Lambda_\eta\otimes^L_{\underline R}\underline P$, since $\Gamma(\eta,\Lambda_\eta)=\Gamma(*,\Lambda)=R$. Choose an affine faithfully flat ind-etale w-contractible cover $U\to X$ by [lem-weil-pbc-source-wcontractible-extension]. For $S=\pi_0U$ the same evaluation lemma gives a dualizable $M\in D(S,\Lambda)$ with $\pi_U^*M\simeq K|_U$.

Cited statements: lem-zl-condensed-wcontractible-lisse-evaluation, lem-zl-condensed-lisse-proetale-locality, lem-weil-pbc-source-wcontractible-extension.

### Original Step 4

Apply [lem-zl-generic-fiber-components-section] to $U\to X$ and $\eta$. With $S_\eta=\pi_0(U\times_X\eta)$ and $r:S_\eta\to S$, its commutative component square and the isomorphism at $\eta$ identify
$$r^*M\simeq\Lambda_{S_\eta}\otimes^L_{\underline R}\underline P.$$
Indeed their images under the coefficient-compatible equivalence $\pi_{U\times_X\eta}^*$ are respectively $K|_{U\times_X\eta}$ and the pullback of the scalar model at $\eta$; full faithfulness reflects the resulting isomorphism. Pull this isomorphism back along the continuous section $s:S\to S_\eta$. Inverse images on these profinite slice sites compose, $r\circ s=\mathrm{id}$, and the coefficient and constant-sheaf pullbacks are the specified ones. Thus $M\simeq\Lambda_S\otimes^L_{\underline R}\underline P$. Applying $\pi_U^*$ and its scalar compatibility from [lem-zl-condensed-wcontractible-lisse-evaluation] gives $K|_U\simeq\Lambda_U\otimes^L_{\underline R}\underline P$. This proves the irreducible-affine case, with the very same $P$ on any such chosen cover.

Cited statements: lem-zl-generic-fiber-components-section, lem-zl-condensed-wcontractible-lisse-evaluation.

### Original Step 5

Now take an affine open $X=\operatorname{Spec}A$ having finitely many irreducible components $X_a$. Give each component its reduced closed scheme structure by [lem-weil-pbc-reduced-induced-closed-subscheme], so $X_a=\operatorname{Spec}(A/I_a)$ is irreducible affine. Their underlying sets cover $X$ by [lem-sc-irreducible-components-cover]. Pullback of $K$ to each $X_a$ is dualizable by [lem-zl-condensed-lisse-proetale-locality]. Choose an affine faithfully flat ind-etale w-contractible cover $W_a=\operatorname{Spec}\overline C_a\to X_a$ by [lem-weil-pbc-source-wcontractible-extension]. Steps 3-4, applied over $X_a$ with this cover, give $K|_{W_a}\simeq\Lambda_{W_a}\otimes^L_{\underline R}\underline{P_a}$ for a perfect $R$-complex $P_a$. Different components may give different $P_a$. We have made no claim that a closed subscheme of a w-contractible affine is w-contractible.

Cited statements: lem-weil-pbc-reduced-induced-closed-subscheme, lem-sc-irreducible-components-cover, lem-zl-condensed-lisse-proetale-locality, lem-weil-pbc-source-wcontractible-extension.

### Original Step 6

Set $C_a=H_A(\overline C_a)$, using [def-exc-ind-etale-closed-lift]. Its diagram is filtered by [lem-exc-closed-lift-filtered], so its defining colimit of etale $A$-algebras makes $C_a$ ind-etale over $A$. By [lem-exc-closed-lift-reduction] the specified map identifies $C_a/I_aC_a$ with $\overline C_a$. By [lem-zl-henselian-indetale-closed-lift] the pair $(C_a,I_aC_a)$ is henselian. Put $V_a=\operatorname{Spec}C_a$, with closed fiber $W_a$. Since $W_a$ is w-contractible, [lem-zl-condensed-henselian-lisse-rigidity] makes $V_a$ w-contractible and makes restriction $D_{\mathrm{lis}}(V_a,\Lambda)\to D_{\mathrm{lis}}(W_a,\Lambda)$ fully faithful. Both $K|_{V_a}$ and its scalar model are dualizable: use [lem-zl-condensed-lisse-proetale-locality] for the former, and Step 2 for the latter. Full faithfulness lifts the isomorphism of Step 5 and its inverse; faithfulness makes their composites identities. We obtain $K|_{V_a}\simeq\Lambda_{V_a}\otimes^L_{\underline R}\underline{P_a}$.

Cited statements: def-exc-ind-etale-closed-lift, lem-exc-closed-lift-filtered, lem-exc-closed-lift-reduction, lem-zl-henselian-indetale-closed-lift, lem-zl-condensed-henselian-lisse-rigidity, lem-zl-condensed-lisse-proetale-locality.

### Original Step 7

There are finitely many $a$. Each $V_a\to X$ is affine ind-etale, hence weakly etale by [lem-weil-pbc-ind-etale-stability], so flat and a pro-etale site object. Its image contains all of $X_a$, since its closed fiber $W_a\to X_a$ is surjective. As the $X_a$ cover $X$, the finite affine disjoint union $\coprod_a V_a\to X$ is surjective, flat and quasi-compact, hence is a covering in the small pro-etale site [def-weil-pbc-proetale-site, def-weil-pbc-ind-etale-algebra]. The models of Step 6 therefore give the required covering. For a general $X$ with Zariski locally finitely many irreducible components, take affine open neighborhoods inside the open neighborhoods from that hypothesis. An open subset of a finite union of irreducible closed subsets has at most that finite number of irreducible components: intersect those subsets with the open and discard the empty ones. Apply the affine construction and compose the resulting covers with the Zariski open cover. The empty scheme uses the empty covering. No uniform amplitude, rank, or scalar model across cover members is required.

Cited statements: def-weil-pbc-proetale-site, def-weil-pbc-ind-etale-algebra, lem-weil-pbc-ind-etale-stability.

## Unfinished work

The three new nodes intentionally remain statement-only, status unsplit, for parallel later work as ordered. No Lean was edited and no compiler, Lake or build command was run. Delivery validation is recorded below when available.
