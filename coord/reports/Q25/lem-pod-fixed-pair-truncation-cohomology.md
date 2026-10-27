# Q25 stage-1 repair: lem-pod-fixed-pair-truncation-cohomology

1. Files written:
   - `dag/nodes/sec-poincare-duality/lem-pod-fixed-pair-truncation-cohomology.json`: item, unchanged statement, four-step assembly (2396 text characters).
   - `dag/nodes/sec-poincare-duality/lem-pod-texact-truncation-triangle-comparison.json`: statement, unsplit; no Mathlib match. Entire normalized comparison of distinguished truncation triangles, with the shifted boundary and naturality.
   - `dag/nodes/sec-poincare-duality/lem-pod-fixed-pair-postnikov-identifications.json`: statement, unsplit; no Mathlib match. Shifted fixed-pair cohomology and canonical absorption/interchange identifications as isomorphisms in the underlying category equipped with structures.
   - `citations.json`: verbatim statement quotes for every citation of every assembly step. `searches.jsonl` contains the searches actually run.
2. Attachments: none. The blueprint-tag search in `lean/WeilConjectures/` returns no exact project declaration. The four relevant theorems in `lean/Sheaf/Paper/FixedPairTruncationCohomology.lean` still have `sorry`; the condensed separated-scheme homology functor in `WeilObject/BoundedConstructible/Homology.lean` supplies neither all clauses nor these rational/common-stage categories.
3. WANTED: none. BBD and the current blueprint are locally available.
4. The returned defect was excessive proof work in one node. This is an actual re-split, not an unchanged re-push: the two new independently actionable statements distribute the old arguments. I also reused an existing node for elementary truncation lifts rather than duplicating it. The source and target statement are not disputed and are unchanged.
5. Unfinished work: the two new nodes are deliberately statement-only, with empty proofs and proof dependencies, for independent workers. No Lean is written or compiled.

## Repair provenance and argument allocation

The named sandbox initially contained only dispatcher marker files: no retained node, report or search log. I recovered the returned ten-step proof from the read-only current repository and read its released stage-1 repair note (`keep_plan: true`). No delivery was active or had been invoked by this session. All old arguments are preserved below verbatim as working material; the new nodes carry their self-contained mathematical claims, not proof sketches in their statements.

- Old Step 1 is assembly Step 1: the standard bounded t-structure, exact Frobenius equivalence, t-exactness and uniquely normalized comparisons. For the inverse, use pullback along the inverse scheme automorphism and the same automorphism clause of prop-constructible-truncations.
- Old Steps 2–3 are assembly Step 2 using the pre-existing lem-a1-fixed-pair-truncation-orthogonality, with the explicit naturality equation and uniqueness fixing the formula. These arguments already had a general node and should not generate a duplicate.
- Old Steps 5–6 are the work assigned to lem-pod-texact-truncation-triangle-comparison. Its self-contained statement includes the unique isomorphism of full triangles, its normalized components, the last-square equation, and naturality of the connecting map for an arbitrary morphism. Assembly Step 3 substitutes theta and multiplies the two equations, without hiding any boundary assertion.
- Old Steps 4, 7 and 8 are assigned to lem-pod-fixed-pair-postnikov-identifications: the shift structure and its action on arrows, the explicit composite e_i, heart-valued cohomology, and both absorption identifications. I made the lower-truncation interchange explicit, as BBD 1.3.5 is needed to identify tau<=m tau>=m K with the chosen order defining H^m. Both nodes concern derived objects themselves, not only cohomology groups.
- Old Step 9 is the short functorial calculation in assembly Step 4. Its entire equality is retained, and the common-stage H^i is the actual functor of def-weil-coefficient-cohomology-modules, rather than an identification with D(Qbar).
- Old Step 10 remains in assembly Steps 1 and 4: both E and the literal common-stage category are covered, including arrows defined only after extending the finite coefficient field. No triangulated structure on fixed pairs and no enlarged direct-image domain is introduced.

The first new argument is the two-triangle comparison in old Steps 5–6 (1955 characters); the second is shifts, cohomology and repeated-truncation normalization in old Steps 4,7,8 (2277 characters). They have comparable workloads; neither restates the full item. The assembly keeps the specialization and the elementary point-fiber calculation.

## Not duplicates

lem-pod-texact-truncation-triangle-comparison vs lem-pod-texact-truncation-comparison: the existing node states comparisons of truncation functors normalized by units and counits, but does not assert their last square as an isomorphism of entire distinguished triangles. The new node adds exactly this shifted-boundary assertion and triangle naturality.
lem-pod-texact-truncation-triangle-comparison vs lem-weil-heart-short-exact-triangles: the existing node supplies truncation uniqueness and adjunctions, but has no t-exact functor F or shift comparison; the new node identifies the comparison components and the resulting last square for F.
lem-pod-texact-truncation-triangle-comparison vs lem-zl-texact-cohomology-boundary-comparison: the existing statement concerns the cohomology long exact sequence of an arbitrary triangle, after H^r; the new statement is an isomorphism of truncation triangles themselves in the original category, before applying cohomology.
lem-pod-fixed-pair-postnikov-identifications vs lem-a1-fixed-pair-truncation-orthogonality: the existing node gives truncation lifts/maps and adjunctions; the new node specifies shifts, composite cohomology structures, equivariant absorption, cancellation and interchange identifications, which are absent from that statement.
lem-pod-fixed-pair-postnikov-identifications vs lem-pod-directed-pair-bounded-tstructure: the latter is a directed coefficient-stage category (i,K) construction, not the category of automorphism-fixed pairs (K,theta), and does not state the equivariant absorption or cohomology formulas.
lem-pod-fixed-pair-postnikov-identifications vs lem-weil-heart-short-exact-triangles: the latter is nonequivariant t-structure theory, without an automorphism P, shift comparison or fixed-pair structures.
lem-pod-fixed-pair-postnikov-identifications vs prop-constructible-truncations: the latter gives the underlying rational/common-stage bounded t-structures and commutation with scheme automorphisms, not equivariant shifts and absorption identifications in a general fixed-pair category.

Whole-DAG and whole-blueprint searches were performed for truncation, fixed pair, point transport, connecting morphism, successive truncation, absorption and t-exact; the nearest blueprint ancestor is prop-weil-operations and every new via list is [lem-pod-fixed-pair-truncation-cohomology]. Same_as is empty: no imported statement states either new assertion. I read the statements of the relevant hits above. Sources use BBD rather than a guessed Stacks tag: there is no Stacks tag for this general t-structure/fixed-pair form. No SGA source is used.

## Review by Q25

I read the current main-20261015 prop-weil-operations statement and proof sentence 2, its final cohomology assertion, the chapter record and sk-lem-finite unit route. The operation-equivariance domain is conditional on bounded constructibility, and the item retains that restriction. I read BBD Proposition 1.3.3(i),(ii) and paragraphs 1.3.4–1.3.5 directly from PDF pages 30–32 (printed 29–31). In particular the source proves uniqueness of the degree-one arrow, not only uniqueness after forgetting it. This supports the first new node; the truncation absorption and interchange on the next page support the second, with the fixed-pair consequences explicitly agent-formulated. I also read the project's existing exact comparison and fixed-pair truncation statements before deciding what genuinely needed a new node.

For assembly Step 1 I checked prop-constructible-truncations gives the bounded t-structure and commutation for every scheme automorphism. lem-pod-semilinear-field-operation-lifts explicitly gives P as an exact equivalence inverse to pullback along g^-1 at both field coefficient stages. I checked its separated finite-type f_0 requirement using f_0=id, without assuming W_0 separated. These hypotheses give precisely preservation of both halves needed by lem-pod-texact-truncation-comparison, whose counit/unit normalizations fix the desired comparisons. Each cited statement was opened, not inferred from its proof.

For assembly Step 2 I checked the pre-existing lem-a1-fixed-pair-truncation-orthogonality actually asserts lifted functors, equivariant canonical maps and truncation adjunctions, with underlying objects and morphisms unchanged. These force the stated structure by the adjunction uniqueness; naturality of the normalized comparisons verifies the displayed arrow equation. The second new node explicitly states the shifted structure, composite e_i, functor on arrows and heart condition. It does not merely define these objects without asserting their properties. The elementary identity/composition laws use the underlying functors.

For assembly Step 3 I checked the new triangle-comparison statement gives both equations used, with the same cutoffs m and m+1. In its application to P the source and target category are the same, and the second application is the actual underlying morphism theta:PK->K. The last-square composite has domain PV and codomain U[1], so the final theta on U[1] is exactly theta_U[1] s_{U,1}. The second new node supplies the canonical absorption, interchange and shift-cancellation isomorphisms of fixed pairs, including the lower form; applying the canonical triangle to truncated inputs then produces the usual successive triangles. This corrects the old proof's implicit lower-order interchange, without changing the item statement.

For assembly Step 4 I read def-weil-weil-sheaf-complex, lem-weil-frobenius-point-transport-natural(2), def-weil-frobenius-point-transport and def-weil-coefficient-cohomology-modules. The definition of transport does not assert naturality; the cited lemma does, at both E and Qbar and for every common-stage arrow. This is why that theorem remains a citation. The fiber functor applied to the Weil-arrow equation gives the first equality and naturality gives the last. Cohomology is applied to an equality of point-fiber morphisms: at E it is ordinary derived module cohomology, at Qbar the explicitly stagewise functor. It is not a claim that a direct image exists on a larger domain.

Small-case checks: zero complexes and arrows give zero equations. For a single heart object M[-j], all cutoffs on either side of j give either zero or the original object; H^j=M and other H^i vanish. This tests the sign [i] and the shifted third arrow. Positive and negative r use coherent shift comparisons; shift cancellation is canonical, not an identification with an arbitrary comparison. At the point with P=id and a nontrivial matrix theta, every displayed equation reduces to the usual intertwining equation, including a Jordan block. Non-separated W_0 causes no extra restriction since only its identity morphism is fed to the semilinear lemma. The generic new statements require bounded t-structures, which both actual coefficient categories possess, and P^-1 is t-exact as required. No invalid assertion about all fixed-pair triangles being distinguished was introduced.

I checked delivery-errors B–E: new nodes have self-contained objects, explicit definitions, no proof steps or proof sketches, empty proof_deps, and genuine recorded semantic/Loogle/grep searches with a second semantic phrasing. Returned hits were infrastructure for t-structure truncations or unrelated group cohomology; I read Mathlib's truncGEδLE and triangleLEGE definitions and repeated-truncation isomorphism lemmas, none of which alone states the new equivariant or normalized functor-comparison assertion. The current project Homology source has the stronger separated/condensed setting and only the cohomology clause, so it is not an attachment. New sources have no Stacks-tag collisions; the mathematical overlaps are distinguished above. C1/C4 are checked through the actual quoted statements in citations.json. No proof step exceeds 2000 characters. No statement is weakened and no source or blueprint metadata is deleted. The old report was absent, so this report records the recovery explicitly.

## Preserved returned proof, verbatim

These are archived arguments for the workers taking the new nodes and the maintainer; they are not proof fields on the new statement-only nodes.

### Old Step 1

Work simultaneously in $\mathcal D=D^b_c(W,\Lambda)$ for $\Lambda=E$ and $\overline{\mathbf Q}_\ell$. By [prop-constructible-truncations] this category has the stated bounded t-structure and its truncation functors. By [lem-pod-semilinear-field-operation-lifts], $P=P_W$ is an exact equivalence with its canonical shift comparison. That lemma applies with the identity morphism of $W_0$ (which is separated and of finite type even if $W_0$ is not separated). The commutation with both truncations in [prop-constructible-truncations] implies that $P$ preserves both halves: if $K\in\mathcal D^{\le m}$, then $PK\simeq P\tau^{\le m}K\simeq\tau^{\le m}PK$, and similarly for $\mathcal D^{\ge m}$. Apply [lem-pod-texact-truncation-comparison] to obtain natural isomorphisms $c^-_K:P\tau^{\le m}K\simeq\tau^{\le m}PK$ and $c^+_K:P\tau^{\ge m}K\simeq\tau^{\ge m}PK$, characterized by
$$\iota_{PK}c^-_K=P(\iota_K),\qquad c^+_KP(\pi_K)=\pi_{PK}.$$
These characterize the particular comparisons in the statement, rather than an arbitrary choice of commuting isomorphisms.

Cited nodes: prop-constructible-truncations, lem-pod-semilinear-field-operation-lifts, lem-pod-texact-truncation-comparison.

### Old Step 2

For either truncation $\tau$, put $a_K=\tau(\theta_K)c_K$. This is an isomorphism, being a composite of two isomorphisms. If $u\theta_K=\theta_LP(u)$, naturality of the comparison in [lem-pod-texact-truncation-comparison] gives
$$\tau(u)a_K=\tau(u\theta_K)c_K=\tau(\theta_L)\tau(Pu)c_K=\tau(\theta_L)c_LP(\tau u)=a_LP(\tau u).$$
Thus $\tau(u)$ is a morphism of the fixed pairs defined in [def-weil-weil-sheaf-complex]. The identity and composition laws are those of $\tau$ on the underlying category. This proves the asserted functor on objects and arrows.

Cited nodes: lem-pod-texact-truncation-comparison, def-weil-weil-sheaf-complex.

### Old Step 3

For upper truncation, naturality of $\iota$ for $\theta_K:PK\to K$ and the defining equation for $c^-$ give
$$\iota_K\theta_{\tau^{\le m}K}=\iota_K\tau^{\le m}(\theta_K)c^-_K=\theta_K\iota_{PK}c^-_K=\theta_KP(\iota_K).$$
For lower truncation, naturality of $\pi$ and the defining equation for $c^+$ give
$$\pi_K\theta_K=\tau^{\ge m}(\theta_K)\pi_{PK}=\tau^{\ge m}(\theta_K)c^+_KP(\pi_K)=\theta_{\tau^{\ge m}K}P(\pi_K).$$
These are precisely the two fixed-pair equations for the canonical truncation maps.

Cited nodes: lem-pod-texact-truncation-comparison, def-weil-weil-sheaf-complex.

### Old Step 4

Write $s_{K,r}:P(K[r])\simeq(PK)[r]$ for the shift comparison of the exact functor $P$ of [lem-pod-semilinear-field-operation-lifts]. Equip $K[r]$ with $\theta_{K[r]}=(\theta_K)[r]s_{K,r}$. For a Weil morphism $u$, the equality
$$u[r]\theta_{K[r]}=(u\theta_K)[r]s_{K,r}=(\theta_L)[r](Pu)[r]s_{K,r}=(\theta_L)[r]s_{L,r}P(u[r])$$
uses naturality of $s$ and proves that shifts send Weil arrows to Weil arrows. This specifies the structure on the shifted last term of a triangle.

Cited nodes: lem-pod-semilinear-field-operation-lifts, def-weil-weil-sheaf-complex, lem-a1-integral-pullback-completed-comparison.

### Old Step 5

Put $U_K=\tau^{\le m}K$, $V_K=\tau^{\ge m+1}K$, and write the canonical distinguished triangle as $U_K\xrightarrow{\iota_K}K\xrightarrow{\pi_K}V_K\xrightarrow{\delta_K}U_K[1]$. The exactness of $P$ from [lem-pod-semilinear-field-operation-lifts] makes
$$PU_K\longrightarrow PK\longrightarrow PV_K\xrightarrow{s_{U_K,1}P(\delta_K)}(PU_K)[1]$$
distinguished. Its outside terms lie in degrees $\le m$ and $\ge m+1$ by Step 1. The uniqueness of the truncation triangle in [lem-weil-heart-short-exact-triangles](1) gives its unique isomorphism to the canonical triangle of $PK$, inducing $1_{PK}$ in the middle. The first and third components are $c^-_K,c^+_K$ (with cutoffs $m,m+1$): their characterizing counit and unit equations are exactly those of [lem-pod-texact-truncation-comparison]. In particular the last square of this triangle isomorphism says
$$\delta_{PK}c^+_K=c^-_K[1]s_{U_K,1}P(\delta_K).$$
Here uniqueness is used for the whole distinguished truncation triangle, including its last arrow.

Cited nodes: lem-pod-semilinear-field-operation-lifts, lem-weil-heart-short-exact-triangles, lem-pod-texact-truncation-comparison.

### Old Step 6

Transport the canonical triangle of $PK$ along the isomorphism $\theta_K:PK\simeq K$. Its outside terms still have the required bounds. By [lem-weil-heart-short-exact-triangles](1), its comparison with the canonical triangle of $K$ is the unique isomorphism over this middle isomorphism. By the truncation adjunctions in the same statement, the first and third components are $\tau^{\le m}(\theta_K)$ and $\tau^{\ge m+1}(\theta_K)$: these have the required counit and unit squares by naturality. Its last square is therefore
$$\delta_K\tau^{\ge m+1}(\theta_K)=\tau^{\le m}(\theta_K)[1]\delta_{PK}.$$
Compose this equality with $c^+_K$ and use Step 5. The result is
$$\delta_K\theta_{V_K}=(\tau^{\le m}\theta_K)[1]c^-_K[1]s_{U_K,1}P(\delta_K)=\theta_{U_K[1]}P(\delta_K).$$
This proves equivariance of the third arrow for exactly the shift structure of Step 4. Together with Step 3 it proves equivariance of all arrows of the canonical truncation triangle.

Cited nodes: lem-weil-heart-short-exact-triangles, def-weil-weil-sheaf-complex.

### Old Step 7

Apply the two functors of Step 2 and then the shift functor of Step 4 to obtain
$$\mathcal H^i(K)=(\tau^{\ge i}\tau^{\le i}K)[i].$$
This is the cohomology functor in [prop-constructible-truncations], so its values are in the constructible heart. More explicitly, let $Z_K=\tau^{\ge i}\tau^{\le i}K$ and
$$e_{i,K}=\bigl(\tau^{\ge i}(c^-_K)\,c^+_{\tau^{\le i}K}\bigr)[i]s_{Z_K,i}:P\mathcal H^i(K)\xrightarrow{\sim}\mathcal H^i(PK).$$
The induced structure is $\mathcal H^i(\theta_K)e_{i,K}$; its arrow equation follows by composing the two equations of Step 2 and the shift equation of Step 4. Thus every Weil morphism induces an equivariant cohomology-sheaf morphism. The underlying functors and maps are unchanged by these constructions, since the forgetful functor of [def-weil-weil-sheaf-complex] retains the underlying objects and arrows.

Cited nodes: prop-constructible-truncations, def-weil-weil-sheaf-complex.

### Old Step 8

The successive upper truncation triangle follows as well: apply Steps 3–6 to $\tau^{\le m}K$ at cutoff $m-1$. The outer objects identify canonically with $\tau^{\le m-1}K$ and $\mathcal H^m(K)[-m]$. The first identification is the one preserving the map to $K$; it is unique by the upper truncation adjunction of [lem-weil-heart-short-exact-triangles](1), so its two Frobenius composites agree after that counit and hence agree. The second identification is the defining expression for $\mathcal H^m$ from Step 7 with the shifts cancelled. Both identifications are therefore equivariant, and the third arrow retains the shifted structure of Step 4. For successive lower truncations, apply the same argument to $\tau^{\ge m}K$ at cutoff $m$, and use the lower adjunction (precompose with the unit) to identify $\tau^{\ge m+1}\tau^{\ge m}K$ with $\tau^{\ge m+1}K$. This also proves equivariance for the usual successive-truncation forms of the standard triangles.

Cited nodes: lem-weil-heart-short-exact-triangles, prop-constructible-truncations.

### Old Step 9

For the point complexes in the statement, write $v=\operatorname{Fib}_s(u)$ and use their given Weil equation $u\theta_A=\theta_BP_s(u)$ [def-weil-weil-sheaf-complex]. Naturality at rational and common-stage coefficients is the actual assertion (2) of [lem-weil-frobenius-point-transport-natural]:
$$\operatorname{Fib}_s(P_su)\iota_A=\iota_B\operatorname{Fib}_s(u).$$
By the definition of transport in [def-weil-frobenius-point-transport] and functoriality of $\operatorname{Fib}_s$,
$$vF_A=\operatorname{Fib}_s(u\theta_A)\iota_A=\operatorname{Fib}_s(\theta_B)\operatorname{Fib}_s(P_su)\iota_A=\operatorname{Fib}_s(\theta_B)\iota_Bv=F_Bv.$$
Apply the cohomology functor $H^i$ to this equality: at $\Lambda=E$ the point fibers lie in $D(E)$ and $H^i$ is the cohomology functor of [def-weil-abstract-derived-category]; in the common-stage category the point fibers lie in $D^b_{\mathrm{fd}}(\overline{\mathbf Q}_\ell)$, where $H^i$ is the stagewise functor $\mathrm H^i(C')\otimes_{E'}\overline{\mathbf Q}_\ell$ of [def-weil-coefficient-cohomology-modules], defined on morphisms represented over a common stage. In both cases $H^i(v)H^i(F_A)=H^i(F_B)H^i(v)$. This is the desired assertion for either supplied direct-image Weil lift. No preservation or existence of a direct image on any additional domain was used.

Cited nodes: def-weil-weil-sheaf-complex, lem-weil-frobenius-point-transport-natural, def-weil-frobenius-point-transport, def-weil-abstract-derived-category, def-weil-coefficient-cohomology-modules.

### Old Step 10

Every argument above takes place in the underlying category $D^b_c(W,\Lambda)$ and the category of fixed pairs of [def-weil-weil-sheaf-complex]. The bounded t-structure and commutation in [prop-constructible-truncations], exactness of $P$ in [lem-pod-semilinear-field-operation-lifts], and point-transport naturality in [lem-weil-frobenius-point-transport-natural](2) all explicitly cover both $E$ and the common-stage $\overline{\mathbf Q}_\ell$ category. Thus Steps 1–9 apply directly at either stage, including morphisms represented only after extension of the coefficient field. We have used only underlying distinguished triangles and their equivariant arrows, and have imposed no triangulated structure on fixed pairs.

Cited nodes: def-weil-weil-sheaf-complex, prop-constructible-truncations, lem-pod-semilinear-field-operation-lifts, lem-weil-frobenius-point-transport-natural.
