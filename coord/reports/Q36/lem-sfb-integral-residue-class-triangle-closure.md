# Q36 repair: lem-sfb-integral-residue-class-triangle-closure

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-residue-class-triangle-closure.json: existing statement retained verbatim; split proof is a 1695-character assembly of two new nodes.
- dag/nodes/sec-six-functors-basics/lem-sfb-complete-integral-residue-functor.json: statement, unsplit; no Mathlib match. Carries returned steps 1–3, a 2774-character argument, comprising completeness, exact reduction and the actual finite residue-ring identification.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-etale-origin-cohomology-closure.json: statement, unsplit; no Mathlib match. Carries returned steps 4–6, a 3313-character argument, comprising constant-scalar encoding, the cohomological origin criterion and triangle rotations.
- citations.json: verbatim supporting statements for both citations in the parent.

## Attachments

None. I searched WeilConjectures by the parent tag and by residue, constructible origin and constant-module encoding. The attached project theorem AlgebraicGeometry.ProEtale.integralResidueClass_triangle_closure in lean/Sheaf/Paper/IntegralResidueClassTriangleClosure.lean:115 has sorry at line 133. Existing upstream fixed-module comparison declarations cover inputs used by the extracted arguments, not the whole parent or either extracted statement. The copied Lean record remains untouched. No compiler was run.

## WANTED

None. Sources used are present locally. No SGA is used.

## Repair of the returned delivery

The return requires spreading the 6787-character proof into at least two comparable, independently actionable nodes, retaining the parent's statement and using at most 3000 characters in its assembly. The sandbox initially contained only dispatcher markers, without the asserted retained node/report/search log. I copied the current read-only repository node, which has the seven returned steps of the stated lengths, and preserved its metadata and proof material. No work was discarded and no git command was run in the read repository.

The first new node is the precise functor from the complete integral category into the finite ordinary residue category; it imposes no constructibility condition. The second is a finite-coefficient comparison/characterization theorem on arbitrary schemes, without integral coefficients or completeness. Neither states P or the parent theorem. Their separate source arguments have comparable size. Both are delivered statement-only, with empty proof/proof_deps and null proof_origin; the workers taking them can work independently. The parent contains two cited applications and one elementary conjunction argument. Its statement, stmt_deps, Lean attachment and imported/maintainer fields are retained verbatim.

The full earlier proof follows below, assigned argument by argument, not shortened into node statements or hidden in a parent step. The only new strengthening is making explicit the natural comparison of the two termwise inverse-image functors already identified in old step 4; its normalization on constants is part of the extracted statement. No hypothesis or conclusion of the parent has changed.

## Unfinished work

The two new nodes deliberately remain unsplit for separate workers. Stage 1 alone was performed; no Lean file, compiler, Lake, build, repository, launcher file, chapter or unit was changed. Final delivery verification is recorded at the end.

## Review by Q36

I read GOAL.md, the chapter and sk-lem-int-integral-heart unit, the live blueprint paragraph (1) of sk-lem-int-integral-heart-triangulated.proof.md, and the completion source's Cones paragraph in sk-lem-pe-derived-nakayama-first-reduction.proof.md. The unit's first two stability assertions are the route here. Its later integral-model, boundedness and truncation assertions are not hypotheses of this standalone result. I compared the current read repository and the sandbox copy: the parent statement is identical, including the ambient unbounded category and arbitrary-scheme conclusion. I read delivery-errors B–E in both copies of that document and checked the following concrete obligations.

Parent step 1 uses precisely the new complete-integral-residue-functor statement. It supplies zero/isomorphism/shift/two-out-of-three for the specified canonical-map completeness notion, and an exact residue functor on the whole ambient category, not just on the complete subcategory. This last distinction is needed when the third vertex has not yet been shown complete. Its value retains the kappa-action, and the constant-function normalization identifies the coefficient ring used in the parent's nu*. The hypotheses agree: X arbitrary, ell prime, E finite, and no invertibility of ell on X. Parent step 2 uses precisely the second new statement: its O_B is the parent's bounded globally constructible etale-origin predicate; its normalization identifies both coefficient conventions and its cohomological criterion is in the ordinary ring-sheaf derived category. Kappa is finite commutative, so every hypothesis holds. The theorem explicitly supplies all three two-out-of-three positions, avoiding any inference that an arbitrary essential image is automatically cone-closed. Parent step 3 uses only the two preceding conclusions and the definition of a conjunction. Both citations are backed by verbatim copies of their statements in citations.json; there are no other node citations in the parent proof.

For the first new node I read Stacks 014A, derived.tex lemma-third-isomorphism-triangle, and 06YY, sites-cohomology.tex lemma-derived-base-change, plus sites-modules.tex section-constant (093I). I opened lem-pe-completion-triangle-comparison: its statement supplies the additive functor F, canonical unit c, equality sigma*c=c[shift] and the full morphism of distinguished triangles including the last square. I opened lem-sf-triangle-morphism-iso: it supplies precisely two isomorphism components implying the third. These justify old steps 1–2 without assuming completeness stability itself. I opened lem-pur-derived-change-of-rings: clause (2) gives the everywhere-defined exact scalar-extension functor on unbounded ordinary module complexes, with target scalar structure retained. I also read lem-sf-module-object-ordinary-coefficient-equivalence: it identifies p_X* of the finite discrete ring with the constant ring, and its exact termwise equivalence preserves shifts and triangles. The remaining constant-function identification is the actual argument in old step 3: continuity to a finite discrete ring gives clopen fibres forming a Zariski cover; distinct constants differ on every nonempty object, and the empty object is covered by the empty family. Thus the map is locally bijective before sheafification, as required. It is not an arbitrary coefficient-ring choice. The new node retains every part of this argument as its explicit conclusion/interface; the argument itself is preserved below, while proof fields remain empty as requested.

For the second new node I read proetale.tex 09AK, lemma-compare-constructible, and 09AL, lemma-compare-constructible-derived, including the proof's triangulated-subcategory paragraph, and sites-modules.tex 03CY, lemma-sheafification-presheaf-modules, and 093I. Stacks defines constructibility affine-locally; I did not silently replace that with a finite global stratification on a non-quasi-compact X. The precise global refinements used are the existing lem-weil-pbc-fixed-module-constructible-origin and lem-weil-pbc-fixed-module-bounded-constructible-origin, whose statements I read. The former gives both sheaf directions for any scheme and finite commutative ring; the latter reconstructs a bounded etale complex from the antecedents of each cohomology sheaf. I read lem-weil-pbc-proetale-constant-module-encoding, the etale equivalence lem-weil-pbc-module-sheaf-constant-ring-equivalence, lem-sf-exact-functor-derived-triangulated and lem-weil-pbc-exact-functor-complex-cohomology. These give the exact constant-scalar equivalence and termwise derived/cohomology identifications used in old step 4. Scalar actions on nu* are determined by the same constant sections, so the intertwining is normalized on those actions, and restriction to a stratum and the finite constant values are unchanged. I read lem-weil-proetale-dbc-triangulated: its statement has bounded global constructible cohomology, contains zero, and supplies shift and extension closure on arbitrary schemes. With the origin criterion this gives the residue closure. I checked TR2 in def-weil-triangulated-category: rotating once handles known first/second vertices, and rotating twice and shifting back handles known second/third vertices. Both rotations, including the minus sign in the rotated connecting arrow, are legitimate distinguished triangles; object membership is unaffected by that sign.

I tested X empty (the empty cover is essential to the ring comparison), the zero derived object, arbitrary negative shifts, triangles with a zero vertex, a non-Noetherian affine scheme, and a non-quasi-compact disjoint union. No step uses a common bound on all integral vertices, local-to-global finiteness of X, or a Noetherian assumption. For the second node I also tested B=0 and the empty scheme: only zero module sheaves occur, so the assertions remain valid. For a general finite ring, no field or finite-Tor assumption is inserted; boundedness is cohomological, not a chosen bounded representative. I checked self-contained introduction of objects and every bracketed notion against stmt_deps. New nodes have no proof sketches inside the statements, no proof dependencies, and no dependency on the parent, so they create no back-edge. Each extracted node has its own source and blueprint ancestor/via chain. No parent non-elementary step exceeds 2000 characters.

The Mathlib searches are real msearch.py calls, recorded exactly in searches.jsonl and in the node fields with the actual result names. Each new node has semantic searches with a second phrasing, Loogle, and source grep; LeanSearch was available. I read the source of the closest generic hits: Sheaf.isConstant_iff_of_equivalence (ConstantSheaf.lean:165) is about equivalent sites, and ObjectProperty's triangulated image instance (Subcategory.lean:749) needs an already full triangulated functor and a triangulated source. Neither states the normalized coefficient comparison, the global constructible criterion, or canonical completion stability. The inverse-image triangulation instance at Subcategory.lean:580 likewise presupposes the relevant exact functor. AdicCompletion.map_exact is ordinary module completion under Noetherian and finite-module assumptions. Mathlib's Proetale.lean and ElladicCohomology.lean define sites/coefficients, not these theorems. Consequently neither new node is a Mathlib leaf.

## Preserved arguments and assignment

### Returned step 1: lem-sfb-complete-integral-residue-functor

Apply [lem-pe-completion-triangle-comparison] with $R=R_X$ and $\pi=\pi_E$. It gives an additive completion functor $F$ and its natural map $c:\mathrm{id}\Rightarrow F$, with completeness equivalent to invertibility of $c_K$. Since $F$ is additive, $F(0)$ is zero, so $c_0$ is an isomorphism. For an isomorphism $u:K\to L$, naturality gives $c_L=F(u)c_Ku^{-1}$; hence completeness is invariant under isomorphisms. For every integer $n$, the identity $\sigma_{K,n}c_{K[n]}=c_K[n]$ and invertibility of $\sigma_{K,n}$ show that $K[n]$ is complete if and only if $K$ is complete. No boundedness of $K$ is used.

Uses: lem-pe-completion-triangle-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.proof.md; Cones and shifts paragraphs: the canonical completion map and its shift comparison; applied to the first sentence of paragraph (1) of the item source.

### Returned step 2: lem-sfb-complete-integral-residue-functor

For an ambient distinguished triangle $T=(K\to L\to M\to K[1])$, [lem-pe-completion-triangle-comparison] makes $(c_K,c_L,c_M)$ a morphism from $T$ to the distinguished triangle $F(T)$, including the last square involving $c_K[1]$. By [lem-sf-triangle-morphism-iso], invertibility of any two of these three maps implies invertibility of the third. The completeness criterion from step 1 therefore gives the required two-out-of-three assertion for completeness alone.

Uses: lem-pe-completion-triangle-comparison, lem-sf-triangle-morphism-iso.

Source: literature/stacks-project/derived.tex; Tag 014A, lemma-third-isomorphism-triangle, applied to the completion triangle morphism of the preceding source.

### Returned step 3: lem-sfb-complete-integral-residue-functor

The coefficient map $R_X\to\kappa_X$ is a map of commutative ring sheaves on the same fixed small site. Apply [lem-pur-derived-change-of-rings], clause (2), to obtain the exact derived scalar-extension functor $T_1:D(R_X)\to D(\kappa_X)$, $T_1(K)=K_1$, retaining its $\kappa_X$-module structure. Thus $T_1$ carries the given ambient triangle to a distinguished triangle of $\kappa_X$-modules, and its shift comparisons identify $T_1(K[n])$ with $K_1[n]$. Exact functors are additive, so $T_1(0)$ is zero, and every functor preserves isomorphisms. Next identify the residue coefficient ring. By [lem-sf-module-object-ordinary-coefficient-equivalence], applied to the finite commutative ring $\kappa$ with its discrete condensed structure, the pulled-back ring $\kappa_X=p_X^*\underline\kappa$ over which $K_1$ is formed is isomorphic as a ring object to the constant ring sheaf of $\kappa$, and its module objects are exactly equivalent to ordinary module sheaves over that constant ring, by a termwise derived equivalence preserving shifts and distinguished triangles. The coefficient sheaf of [def-weil-pbc-proetale-modules] for $\Lambda=\kappa$ is the same ring: the map from the constant presheaf $\kappa$ to $U\mapsto\operatorname{Cont}(\pi_0(|U|),\kappa)$ is locally surjective, since a continuous function to the finite discrete set $\kappa$ is constant on each member of the Zariski covering of $U$ by its clopen fibres, and locally injective, since distinct constants differ on every nonempty $U$ and an empty $U$ is covered by the empty family; so it becomes an isomorphism after sheafification [def-weil-pbc-sheafification]. Below, $\kappa_X$ and $T_1$ are read through these identifications.

Uses: lem-pur-derived-change-of-rings, lem-sf-module-object-ordinary-coefficient-equivalence, def-weil-pbc-proetale-modules, def-weil-pbc-sheafification.

Source: literature/stacks-project/sites-cohomology.tex; Tag 06YY, lemma-derived-base-change, for the identity underlying topos with the coefficient map; compare Tag 06YU and the K-flat change-of-rings construction. Residue ring identification: sites-modules.tex Tag 093I (constant sheaves) and the cited module-object comparison.

### Returned step 4: lem-sfb-finite-etale-origin-cohomology-closure

In the residue category use the ordinary constant finite ring sheaf $\kappa_X$ and the termwise exact comparison $\nu_X^*$ specified in [def-weil-pbc-proetale-modules]. When applying the fixed-module-valued comparison results below, use [lem-weil-pbc-proetale-constant-module-encoding]: restriction to constant scalars is an equivalence and leaves the underlying additive sheaf unchanged. The inverse extends constant scalar actions locally along the sheafification unit; hence on an étale pullback both descriptions have the same scalar action, determined by their constant sections. This identifies the two comparison functors. The equivalence preserves zero, kernels and cokernels by their universal properties; [lem-sf-exact-functor-derived-triangulated] and [lem-weil-pbc-exact-functor-complex-cohomology] therefore give its termwise derived equivalence and its cohomology identifications. Constant module sheaves, finite stalks and restrictions to each stratum are unchanged: all their scalar-linear maps are the same maps after restriction to constant scalars. In particular the global finite-stratification predicates in the fixed-module comparison nodes are precisely the ordinary constant-ring-sheaf predicates used here. This step changes no integral coefficient ring and uses no constructibility theorem for condensed integral modules.

Uses: def-weil-pbc-proetale-modules, lem-weil-pbc-proetale-constant-module-encoding, lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-exact-functor-complex-cohomology.

Source: literature/stacks-project/sites-modules.tex; Tags 03CY and 093I, constant scalar restriction and module sheafification; homology.tex Tag 010N and derived.tex Tag 015F for the exact equivalence on complexes.

### Returned step 5: lem-sfb-finite-etale-origin-cohomology-closure

For $N\in D(\kappa_X)$ let $Q(N)$ mean that its cohomology vanishes outside a finite integer interval and each cohomology sheaf is intrinsically globally constructible. If $N\cong\nu_X^*A$ with $A$ bounded constructible étale, exactness of the inverse image and [lem-weil-pbc-exact-functor-complex-cohomology] give $H^i(N)\cong\nu_X^*H^i(A)$, with the same vanishing interval. The forward construction in [lem-weil-pbc-fixed-module-constructible-origin] makes each of these sheaves constructible. Conversely, if $Q(N)$ holds, that same node supplies a globally constructible étale antecedent for each $H^i(N)$. Apply [lem-weil-pbc-fixed-module-bounded-constructible-origin] to the bounded complex $N$ and these antecedents. It supplies an étale derived object $A$ with bounded globally constructible cohomology and $N\cong\nu_X^*A$. Step 4 identifies its coefficient convention with ours. Consequently $Q(N)$ is equivalent to the condition of being isomorphic to the inverse image of a bounded étale complex with constructible cohomology. All these comparison statements allow arbitrary schemes and finite commutative coefficient rings; here $\kappa$ is a finite field.

Uses: lem-weil-pbc-exact-functor-complex-cohomology, lem-weil-pbc-fixed-module-constructible-origin, lem-weil-pbc-fixed-module-bounded-constructible-origin.

Source: literature/stacks-project/proetale.tex; Tags 09AK (lemma-compare-constructible) and 09AL (lemma-compare-constructible-derived), with the global finite-stratification comparison and bounded reconstruction stated in the two cited fixed-module nodes.

### Returned step 6: lem-sfb-finite-etale-origin-cohomology-closure

Apply [lem-weil-proetale-dbc-triangulated] with $Y=X$ and $\Lambda=\kappa$. It says exactly that $Q$ contains zero, is invariant under isomorphisms and integer shifts, and is closed under extensions in ambient distinguished triangles. To spell out the remaining positions, if $Q(N_1)$ and $Q(N_2)$ hold for a distinguished triangle $N_1\to N_2\to N_3\to N_1[1]$, rotate it to $N_2\to N_3\to N_1[1]\to N_2[1]$ and apply extension closure. If instead $Q(N_2)$ and $Q(N_3)$ hold, rotate twice, obtaining $N_3\to N_1[1]\to N_2[1]\to N_3[1]$, apply extension closure and shift back. These rotations are distinguished by TR2 of [def-weil-triangulated-category]. Thus any two imply the third. Using the equivalence in step 5, the same statements hold for the bounded constructible étale-origin condition.

Uses: lem-weil-proetale-dbc-triangulated, def-weil-triangulated-category.

Source: literature/stacks-project/proetale.tex; Tag 09AL, lemma-compare-constructible-derived, proof: the constructible cohomology subcategories are triangulated; its bounded form is the cited node. Rotations: derived.tex Tag 0145, TR2.

### Returned step 7: parent elementary assembly

The predicate $P(K)$ is the conjunction of completeness and $Q(T_1(K))$ by step 5. Steps 1, 3 and 6 give $P(0)$, isomorphism invariance, and $P(K[n])\Longleftrightarrow P(K)$ for every integer $n$. Given a distinguished triangle and any two of its $P$ assertions, step 2 supplies completeness of the third vertex; step 3 reduces the triangle and step 6 supplies $Q$ at its third vertex. Step 5 converts this back to bounded constructible étale origin. This proves every two-out-of-three implication. In particular completeness and the required residue origin hold for $L$ when $P(K)$ and $P(M)$ hold. None of the steps imposes a Noetherian, dimension, finite-type, or invertibility hypothesis on $X$.

Uses: previous steps, conjunction only.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-integral-heart/sk-lem-int-integral-heart-triangulated.proof.md; Paragraph (1): combine shift/cone stability of completeness and exact reduction, before the integral-model comparison and boundedness assertion.

## Not duplicates

I searched the entire DAG by the Stacks tags and the notions and searched all blueprint nodes with blueprint_refs.py (completion triangle, constructible origin, coefficient equivalence, finite residue, bounded constructible, constant module, etale origin, derived complete, coefficient comparison, constructible derived, constant scalars, completion reduction, residue functor). No existing node states either complete extracted interface. The following are distinctions from the same-tag nodes listed by the delivery tool and the closest semantic candidates. These citations are comparisons, not extra proof dependencies of the unsplit nodes.

lem-sfb-complete-integral-residue-functor vs lem-weil-derived-limit-levelwise-iso: a levelwise isomorphism between two supplied Roos triangles induces an isomorphism; it does not identify the canonical completion locus or define normalized residue scalar extension.

lem-sfb-complete-integral-residue-functor vs lem-sfb-small-triangulated-extension-classes: proves essential smallness of a class of triangle middle vertices, not completeness or any residue functor.

lem-sfb-complete-integral-residue-functor vs lem-sfb-bounded-homology-essentially-small: proves essential smallness of bounded objects with prescribed cohomology, not the unbounded complete integral category or residue scalar extension.

lem-sfb-complete-integral-residue-functor vs lem-sp-derived-injective-resolution-naturality: compares specified bounded-below injective resolutions for a derived additive functor; no complete-locus or finite residue-ring assertion occurs.

lem-sfb-complete-integral-residue-functor vs lem-sf-triangle-morphism-iso: is the abstract two-component isomorphism lemma used inside this argument; it supplies neither the canonical completion-unit triangle nor the finite residue coefficient functor.

lem-sfb-complete-integral-residue-functor vs lem-etale-projection-formula-triangle-closure: asserts triangle closure for projection-formula map components on etale sites, not canonical completion or residue scalar extension.

lem-sfb-complete-integral-residue-functor vs prop-weil-pbc-cone-independence: asserts independence of finite-stage cone representatives after field scalar extension, not completeness or the actual finite residue coefficient ring.

lem-sfb-complete-integral-residue-functor vs lem-pe-kflat-roos-representative-invariance: establishes invariance of a strict Roos representative under changes of K-flat model; it does not establish the complete subcategory and its normalized exact residue functor.

lem-sfb-complete-integral-residue-functor vs lem-pe-two-term-reduction-cohomology: computes one two-term complex on a geometric point; it does not prove the arbitrary-scheme categorical stability and normalized residue functor.

lem-sfb-complete-integral-residue-functor vs lem-pe-restricted-kflat-tensor-identification: identifies scalar-first/scalar-last tensor models and restrictions for supplied coefficient maps; it does not identify the canonical complete locus or the constant-function residue ring.

lem-sfb-complete-integral-residue-functor vs def-pe-integral-presentation-encoding: defines supplied integral encoding data with no existence theorem; the new node proves stability of the canonical complete locus and describes its exact residue functor.

lem-sfb-complete-integral-residue-functor vs lem-pe-kflat-scalar-tower-realization: normalizes all quotient transitions on a chosen K-flat tower; it does not state completeness two-out-of-three or the residue category identification.

lem-sfb-finite-etale-origin-cohomology-closure vs def-pe-finite-discrete-presentation-encoding: only defines supplied data, with no assertion of existence, comparison along nu, global constructibility/origin criterion or triangulated-origin closure.

lem-sfb-finite-etale-origin-cohomology-closure vs def-sfb-constant-module-coefficient-transport: defines scalar transport between constant Ring/CommRing sheaves; it does not compare the two site inverse images or characterize bounded etale origin.

lem-sfb-finite-etale-origin-cohomology-closure vs def-sfb-scalar-extension-pure-tensor-section: defines one pure-tensor section under scalar extension, with no constructibility, derived site square or origin assertion.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-sc-hom-tensor-comparison-natural: is naturality of a sheaf tensor comparison under module maps, not the coefficient/site comparison and bounded global origin criterion.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-sc-exterior-sheaf-comparison: identifies two exterior power constructions on scheme modules, not finite constant coefficient encodings or etale origin.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-sc-hom-tensor-section-natural: is naturality of a sheafified tensor section map, not the comparison of nu and bounded constructible origins.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-pc-open-localized-module-sheafification: compares sheafification with restriction to an open on a topological space; it does not compare etale/proetale inverse images or finite-coefficient origin.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-sc-exterior-dual-pairing-local: constructs a local alternating pairing for exterior powers, with no finite coefficient or site-comparison conclusion.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-pc-sites-module-sheafification-interface: constructs a module action on a sheafification and its universal property; this is input for an encoding, not the global origin/cohomology comparison and closure theorem.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-sc-exterior-sheaf-dual-ext: is extensionality of exterior-dual sections on pure wedges, not any coefficient/site/derived origin assertion.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-sc-exterior-dual-pairing-functional: is existence and uniqueness of a functional on an exterior power, not a finite-coefficient comparison or origin theorem.

lem-sfb-finite-etale-origin-cohomology-closure vs def-sfb-site-derived-constant-module-functor: defines the derived constant realization of scalar complexes; it does not identify constant-scalar restriction on the two sites or characterize/close etale origins.

lem-sfb-complete-integral-residue-functor vs lem-sfb-ringed-complete-triangulated: uses a locally derived ideal-complete/Koszul reflector for arbitrary ringed sites, not the canonical integral reduction-tower map of sk-def-pe-derived-completion or the actual finite residue coefficient functor. Identifying the two completeness presentations is additional work, not a one-line specialization.

lem-sfb-complete-integral-residue-functor vs lem-pe-completion-triangle-comparison: provides the additive canonical completion functor/unit and a morphism of triangles; the new node carries the deduction of all stability assertions and the exact finite residue scalar-extension normalization.

lem-sfb-complete-integral-residue-functor vs lem-pur-derived-change-of-rings: provides generic exact scalar extension retaining target coefficients; it does not assert canonical integral completeness stability or identify the pulled-back residue ring with the continuous-function sheaf.

lem-sfb-complete-integral-residue-functor vs lem-sf-module-object-ordinary-coefficient-equivalence: gives finite internal/ordinary coefficient equivalence, but neither integral completion stability nor the continuous-function-presheaf identification and exact residue functor on the complete locus.

lem-sfb-complete-integral-residue-functor vs lem-sf-finite-discrete-normalized-encoding: supplies normalized finite-discrete encoding data, not canonical integral completeness or exact residue scalar extension from the complete integral category.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-weil-pbc-fixed-module-constructible-origin: gives the global finite-coefficient sheaf-origin equivalence only; the new node includes the ordinary/fixed derived site square, bounded reconstruction and all triangle closure positions.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-weil-pbc-fixed-module-bounded-constructible-origin: is one-way bounded reconstruction in fixed-module coefficients from supplied etale antecedents, not the ordinary/fixed comparison and iff criterion together with ambient triangle closure.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-weil-proetale-dbc-triangulated: closes the intrinsic bounded constructible class, not the etale-origin predicate; the new node supplies the coefficient normalization and equivalence of these predicates before using that closure.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-sf-proetale-constructible-origin: is restricted to the finite-field/ell-adic quotient coefficient system A_E,n; the new node allows any finite commutative ring, including a product with different residue characteristics, and records the normalized derived coefficient square and all ambient closure positions.

lem-sfb-finite-etale-origin-cohomology-closure vs sk-thm-pe-constructible-comparison: assumes X quasi-compact and quasi-separated and uses affine-local constructibility; the new node uses a finite global stratification on arbitrary X and explicitly identifies the ordinary/fixed coefficient encodings.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-sfb-finite-discrete-constructible-model: assumes a Noetherian scheme and uses internal stratified-lfp coefficients; the new node uses arbitrary schemes and ordinary/fixed finite module sheaves with global constructible cohomology.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-sf-finite-discrete-encoding-constructibility: compares internal and fixed finite local models, with affine-local convention on non-qcqs schemes; the new node compares nu in both encodings and establishes the global finite-stratification bounded etale-origin criterion and closure.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-pe-constant-derived-encoding: compares constant-ring/fixed encodings, cohomology and classicality, but does not state the global bounded constructible-origin criterion and all triangle closure positions.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-sfb-adic-constructible-triangulated: assumes a Noetherian scheme, completed A-coefficients and a finite-Tor residue clause; the new theorem is an arbitrary-scheme finite-coefficient comparison with no integral or Tor condition.

lem-sfb-finite-etale-origin-cohomology-closure vs lem-weil-pbc-finite-coefficient-derived-origin-presentation: assumes a Noetherian scheme and proves one complex-presentation existence assertion, not a normalized equivalence of both inverse images and a global-origin iff criterion with ambient closure.

lem-sfb-complete-integral-residue-functor vs def-a1-integral-completed-tower-pullback-universes: defines strict reduction and pullback resolving pairs with independent universes, before completion or derived inverse limit. It does not state stability of the canonical complete locus or identify the finite continuous-function residue ring.

lem-sfb-complete-integral-residue-functor vs def-per-scalar-extension-unit: defines the normalized scalar-extension unit only for a coefficient endomorphism equal to the identity. The residue quotient is not such a map, and neither integral completeness stability nor the finite-ring identification is a clause there.

lem-sfb-complete-integral-residue-functor vs lem-per-proetale-scalar-slice-comparison: compares derived scalar extension with restriction to a slice and normalizes its counit. It supplies neither stability of the canonical integral complete locus nor the finite constant/continuous-function residue identification.

lem-sfb-complete-integral-residue-functor vs lem-pod-derived-reduction-sheaf-resolution-independence: assumes exact global sections and proves equality of reduction/sections comparisons from two K-flat resolutions. No exact-sections assumption holds here, and the new statement concerns completeness and exact residue reduction, not a sections comparison.

lem-sfb-complete-integral-residue-functor vs lem-pod-point-sections-derived-reduction-cone: identifies a single point-module quotient reduction with a mapping cone of a uniformizer power. It does not assert arbitrary-scheme complete-locus stability, the ring-sheaf identification, or the exact residue functor on the complete category.

lem-sfb-finite-etale-origin-cohomology-closure vs def-weil-pbc-ideal-module-quotients: defines ideal-module quotients, quotient ring sheaves and quotient transitions on a site. It asserts no equivalence between module encodings, derived comparison along nu, constructible-origin criterion or triangle closure.

## Verification

The preliminary server review_split check passed. The first delivery dry run stopped at the same-tag duplicate check, before server preflight. I opened all six additionally listed node statements, found that they concern different constructions as detailed above, and added the requested individual distinctions. No node statement or proof argument changed to bypass the check.

After these six distinctions were added, deliver.py --no-push completed successfully and printed preflight passed at 2809c3b265a. The required server checks, including DAG validation and review_split, therefore accepted the two new statement-only nodes and parent assembly. This verification note is followed by one final dry run of the exact report content before the direct push.

The old isolated-project reference coord/dag-sync.md in the standing brief is absent from the current live read clone. The live-repository brief and deliver.py's current-origin overlay govern this repair; no isolated checkout or retired source tree was used.
