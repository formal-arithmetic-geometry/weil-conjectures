# Q153 repair: lem-sfb-qcqs-integral-finite-model-completeness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-integral-finite-model-completeness.json: item, statement unchanged, five assembly steps, 2481 characters total.
- dag/nodes/sec-six-functors-basics/lem-sfb-strict-completion-restriction-comparison.json: statement, unsplit; no exact Mathlib match after five recorded searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-scalar-local-model-complete.json: statement, unsplit; no exact Mathlib match after five recorded searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-strata-completion-detection.json: statement, unsplit; no exact Mathlib match after five recorded searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-model-sheaf-quotient-constructible.json: statement, unsplit; no exact Mathlib match after five recorded searches.

## Attachments

None. The exact item tag is absent from lean/WeilConjectures. The existing project declaration AlgebraicGeometry.ProEtale.qcqs_integral_finite_model_completeness, lean/Sheaf/Paper/QcqsIntegralFiniteModelCompleteness.lean:247, ends with sorry. Neither that declaration nor its copied eleven-step docstring is a finished proof. Searches by completion, restriction, scalar model, finite reduction and the item tag found no upstream declaration giving all clauses.

## WANTED

None. All sources used here are available in literature/.

## What was wrong and what changed

This repairs the human's 2026-10-21 re-split return, applied 2026-10-22. The returned proof contained eleven steps totalling 11678 characters. The sandbox initially contained only dispatcher marker files; no node, report, citations or searches survived there. I copied the live returned node without any git operation. The mandatory initial dry run exited with the missing report/Review-section diagnostic. I retained the statement, source, prior Mathlib searches, all inherited metadata, and the entire returned argument below. No statement dispute or route change is needed.

Four separately assignable statement-only nodes now carry four comparable arguments: completion/restriction compatibility (old 1--2, 2451 characters), local scalar-model completeness (old 3--4, 2138), finite-stratum completion detection and pullback of models (old 5--6, 2301), and constructibility of sheaf reductions (old 8--9, 2238). The parent keeps bounded-complex devissage (old 7 and 10) and the final classical realization (old 11). The new nodes have no proof steps and no proof dependencies: their proofs are intentionally future work, as this repair requires. They are not new copies of the entire item.

## Remaining work

The four new statements are unsplit and ready for independent stage-1 workers. There is no Lean editing, compiler invocation, Lake invocation, or repository write in this delivery. The old long Lean docstring remains reference material for the maintainer to update later; changing it is outside the stage-1 authorization.

## Review by Q153

I read GOAL.md, the worker brief and role, the stage-1 contract, the three-level route in SETUP.md, the compactification-coherence unit and the six-functors-basics chapter, and delivery-errors B--E, including the merged copy. The item is an auxiliary input to the closed-complement calculation for compactification comparisons; the new statements inherit its chapter and unit and do not change that route.

For the item I read the actual finite-model proof in main-20261015, Local models, Locality, Strata and Complexes. Its open-stratum argument is not being reinstated: the returned proof already repaired that by a finite scheme-theoretic open/closed refinement. I read Bhatt--Scholze Sections 3.1 and 3.5, Definition 6.5.1, Lemmas 6.5.3--6.5.4 and 6.5.8, and the opening of 6.6. Definition 6.5.1 assumes completeness rather than proving it from our local models; Section 6.6 has a topologically Noetherian hypothesis. Consequently our qcqs finite-model argument remains explicitly agent-written. Hemo--Richarz--Scholbach Proposition 7.6 and Theorem 7.7 provide contextual confirmation of the adic criterion on qcqs schemes, not a silently substituted equivalence of coefficient categories.

For the restriction node I checked Stacks 09AA in proetale.tex, label lemma-closed-immersion, whose clause (1) is limit preservation for closed inverse image. The existing immersion-limit-preservation statement adds the identified module coefficients. The new assertion also identifies the actual cone transition, quotient augmentation and Roos augmentation, and the section-action equivalence; preservation of abstract limit objects alone would not suffice. Old steps 1--2 below retain exactly the calculation needed to prove these map assertions.

For the local-model completeness node I checked the finite-scalar two-term-resolution statement, the exact principal reduction sequence, the integral coefficient inverse-limit identification, the epimorphic-tower result, and completion-triangle comparison against old steps 3--4. In particular the coefficient ring is the pulled-back norm-topological integral ring, not the discrete constant ring of integers. The scalar module may have torsion, and finite rank zero is included. The retained cone-to-quotient maps commute with their augmentations, so the assertion is about the specified unit. The existing integral-lisse completeness node applies only to finite locally free sheaves and cannot dispose of the torsion case.

For the finite-stratum detection node I read Stacks 005H/lemma-constructible (Boolean operations), 09YH/lemma-constructible-is-retrocompact, and 09Y4/lemma-constructible-partition-refined-by-stratification in topology.tex. These alone do not produce a factorization of a scheme morphism from a mere image containment. The existing qcqs refinement theorem explicitly gives actual morphisms from leaves to the strata and quasi-compact open children. Those are the hypotheses needed to pull back the same finite scalar matrices and apply open/closed detection. The new node adds coefficient-model transfer and detection of completion cones and arbitrary cohomological vanishing. It does not re-prove the existing geometric refinement as a second node. Old steps 5--6, together with the vanishing part of 9, supply its argument.

For the quotient-sheaf node I checked the Local models paragraph and old steps 8--9, the K-flat change-of-rings statement and the finite-discrete coefficient equivalence. A scalar resolution over the DVR reduces by the actual quotient homomorphism to a two-term matrix over the finite ring. Its kernel and cokernel are finite; a finite module over a finite ring is finitely presented because a surjection from a finite free module has finite kernel. The bound is [-1,0], not [0,0]; this matters for torsion models. Exact restrictions, cover conservativity and finite-tree detection are required to obtain that bound globally.

The assembly's citations were read as statements, not taken from their proofs. Step 1 uses precisely the new comparison's preservation of units, towers, cohomology and models, and sk-def-sfb-constructible's boundedness. Step 2 uses the detection node's leaf models and iff for the specified completion unit and the local-model node's actual isomorphism conclusion. Step 3 uses the displayed truncation triangle, completion-triangle comparison including its shift clause and last square, and the cohomology long exact sequence. Its only remaining argument is finite induction from the zero truncation and the five consecutive cohomology terms. Step 4 uses the quotient node's finite ring, uniform [-1,0] bound and both constructibilities, change-of-rings exactness, the coefficient equivalence's shifts/triangles/local-model identifications, triangulated closure of ordinary bounded constructible complexes, and the long exact sequence for the [r-1,s] bound. Step 5 checks that a finite ring is Noetherian before invoking the qcqs discrete-Noetherian constructible-comparison equivalence, then retains the actual pair (L_n, alpha_n) required by the witness definition. Every entry in citations.json quotes the complete verbatim cited statement, so all clauses used can be checked directly.

I tested the new assertions on the empty scheme and empty leaves (zero categories), the zero module and rank zero, a one-stratum partition, a nilpotent closed stratum, scalar P=A and P=A/pi^m, n=1, and nonzero ramification of F/Q_l. For P=A/pi^m the derived reduction may have both H^-1 and H^0, so no torsion-freeness or false degree-zero conclusion has entered. The closed complement need not be reduced. Qcqs is used for finite constructible refinement; no dimension bound, residue-characteristic assumption or invertibility of ell is introduced. All new statements explicitly introduce their objects. No unsplit node contains a proof sketch. Parent steps are all below 2000 characters and their total is below 3000.

## Coverage of the returned argument

| Returned step | Destination | Argument retained |
|---|---|---|
| 1 | restriction-comparison node | Section-action equivalence, cohomology and scalar matrices, products and quotient augmentations, size convention. |
| 2 | restriction-comparison node | Immersion/slice exactness and products, strict cones, 1-T, augmentation and finite reduction compatibility. |
| 3 | local-model-completeness node | Exact principal reduction, epimorphic quotient tower, actual integral inverse-limit projections, Roos quasi-isomorphisms, all finite ranks. |
| 4 | local-model-completeness node | Scalar length-one resolution, completion map of triangles, torsion/zero cases, cover descent. |
| 5 | finite-strata-detection node | Actual leaf-to-stratum factorization, inverse-image composition and cover base change, coefficient/tensor comparison, same scalar matrix, empty leaves. |
| 6 | finite-strata-detection node | Completion-cone cohomology and finite upward induction using the quasi-compact open child. |
| 7 | parent step 3 | Bounded truncation triangles, shifts, the specified completion units and the induction from zero. |
| 8 | quotient-sheaf node | Finite scalar quotient, K-flat two-term reduction, exact constant functor, finite/finitely presented kernel and cokernel. |
| 9 | quotient-sheaf node, detection node | Restriction to original strata and covers, finite models in both coordinates, global vanishing via tree detection. |
| 10 | parent step 4 | Exact tensor of truncation triangles, triangulated constructibility, uniform [r-1,s] bound. |
| 11 | parent step 5 | Finite ring is Noetherian, qcqs comparison, retained etale-origin pair. |

The full text below is a handoff plan, not additional proof steps on the new unsplit nodes. In proving the restriction node use the dependencies of old steps 1--2; for local-model completeness use those of 3--4 plus the restriction node; for detection use those of 5--6 plus restriction; for quotient constructibility use those of 8--9 plus restriction and detection. Thus every non-elementary fact named in the old argument remains available with its original node id. No work is erased by reducing the parent length.

## Full returned proof, preserved verbatim

### Returned step 1

Write $B_T=A_T$ and $k_n=A/\pi^n$. Use the exact section-action equivalence and its termwise derived equivalence of [lem-sfb-module-object-ringed-site-derived-comparison], with the tensor comparison [lem-pe-internal-section-tensor-comparison], to work with ordinary sheaves of $B_T$-modules. These equivalences leave underlying abelian sheaves and maps unchanged; hence they identify cohomology, scalar matrices and their finite constant local models. They preserve products by the product universal property and identify the strict quotient towers and their augmentations: tensor is identified by the cited comparison, and every quotient map is the same underlying map. Thus the completion assertion may be proved in these coordinates and transported back, including its specified unit. All sites and products are small in the universe of [def-weil-size-convention].

Uses: lem-sfb-module-object-ringed-site-derived-comparison, lem-pe-internal-section-tensor-comparison, def-weil-size-convention.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md; Local models: interpret internal coefficients by the section-action equivalence.

### Returned step 2

We first record how to test the canonical completion map $c_K$. For an immersion $h:T\to W$, [lem-weil-pbc-proetale-immersion-limit-preservation] says that inverse image with an identified coefficient ring is exact and preserves products; its coefficient identification is an isomorphism by [lem-sfb-alpha-iso]. For a covering object $U\to W$, [lem-weil-proetale-weakly-etale-localization] and [lem-sfb-proetale-object-inverse-image-restriction] identify inverse image with slice restriction. Exactness follows from [det-pe-topos-functoriality-inverse-image] on abelian sheaves and [det-prop-sfb-module-pullback-exact-lifted] on modules with the identified coefficient ring. Slice restriction preserves products because module limits are sectionwise [lem-weil-pbc-module-sheaves-limits-sectionwise]. In either case apply inverse image to the strict model $D_n(M)=\operatorname{Cone}(\pi^n:M\to M)$, with transition $(x,y)\mapsto(x,\pi y)$ and augmentation $m\mapsto(m,0)$, of [lem-pe-principal-reduction-cone-calculus]. Exactness identifies these cones and scalar maps with those on the restricted complex. Product preservation then identifies $1-T$ and its cone in [lem-pe-roos-cone-calculus]. It also takes the augmentation $m\mapsto(((m,0))_n,0)$ to the restricted augmentation. By [lem-pe-completion-triangle-comparison] this proves compatibility with $c_K$ itself, rather than just an abstract isomorphism of completion objects. Inverse image also commutes with finite reduction, by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]; here $h^*B_W=B_T$ and $h^*(k_n)_W=(k_n)_T$.

Uses: det-pe-topos-functoriality-inverse-image, det-prop-sfb-module-pullback-exact-lifted, lem-weil-pbc-proetale-immersion-limit-preservation, lem-sfb-alpha-iso, lem-weil-proetale-weakly-etale-localization, lem-sfb-proetale-object-inverse-image-restriction, lem-weil-pbc-module-sheaves-limits-sectionwise, lem-pe-principal-reduction-cone-calculus, lem-pe-roos-cone-calculus, lem-pe-completion-triangle-comparison, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

Source: literature/stacks-project/proetale.tex; Tag 09AA (lemma-closed-immersion), (1); slice restriction; strict cone/Roos calculation of the completion map.

### Returned step 3

For any scheme $T$, [det-pe-derived-nakayama-resolution] identifies the derived reduction of $B_T[0]$ with $(k_n)_T[0]$: the exact sequence $0\to B_T\xrightarrow{\pi^n}B_T\to(k_n)_T\to0$ gives the levelwise quasi-isomorphism from the strict cone to this quotient. The cone projections commute with $(x,y)\mapsto(x,\pi y)$ and take the augmentation to the quotient projection. The transitions $(k_{n+1})_T\to(k_n)_T$ are epimorphic: the scalar quotient is surjective and every local constant value has a scalar lift. Their ordinary inverse limit, with its actual quotient projections, is $B_T$ by [det-prop-sfb-qlbar-colimit-x-integral-limit]. Apply [det-pe-milnor-epimorphic] to this tower, reindexed by $n\ge1$, to identify that cone with its derived inverse limit. The levelwise cone-to-quotient quasi-isomorphisms give a quasi-isomorphism of Roos complexes by [lem-pe-roos-cone-calculus], respecting the augmentations just described. Consequently $c_{B_T[0]}$ is an isomorphism. The same proof works for each finite power $B_T^r$, since finite products commute with the displayed limits, scalar quotients and $1-T$; it includes $r=0$.

Uses: det-pe-derived-nakayama-resolution, det-prop-sfb-qlbar-colimit-x-integral-limit, det-pe-milnor-epimorphic, lem-pe-roos-cone-calculus.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Sections 3.1 and 3.5 (repleteness, inverse limits and regular principal reductions); coefficient identification in blueprint integral-limit detail.

### Returned step 4

Let $M=B_T\otimes_A P$ for a finitely presented scalar $A$-module $P$. By [lem-sfb-finite-constant-model-two-term-free-resolution] there is an exact sequence $0\to B_T^a\to B_T^b\to M\to0$, induced by an exact scalar sequence $0\to A^a\xrightarrow{u}A^b\to P\to0$. Thus $M[0]$ is the cone of $B_T^a[0]\to B_T^b[0]$. By [lem-pe-completion-triangle-comparison], the three canonical completion maps form a morphism of distinguished triangles. The first two maps are isomorphisms by step 3; the long exact cohomology sequences [lem-sf-derived-homology-long-exact] show that the third is an isomorphism too (in each degree, use the five consecutive terms around $H^q(M)$). This proves completeness for each finite constant scalar model, including torsion models and the zero module. For a sheaf merely having such models on a pro-étale cover, step 2 identifies its restricted completion maps with these maps, and [lem-zl-condensed-cover-restriction-conservative] shows its completion map is an isomorphism.

Uses: lem-sfb-finite-constant-model-two-term-free-resolution, lem-pe-completion-triangle-comparison, lem-sf-derived-homology-long-exact, lem-zl-condensed-cover-restriction-conservative.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md; Local models and locality; completion closure from Bhatt--Scholze Sections 3.5 and 6.5.

### Returned step 5

Let $M$ be any constructible $B_V$-module in the finite constant scalar-model sense [sk-def-sfb-constructible]. Apply [lem-fix-constructible-open-closed-refinement] to its finite constructible locally closed stratification. It gives a finite binary tree of qcqs subschemes, each internal vertex split into a quasi-compact open and its closed complement, and an actual morphism from every nonempty leaf to one original stratum. Write $t:T\to S_\alpha$ for this morphism. The leaf restriction $M|_T$, an iterated inverse image along the branch immersions, is isomorphic to $t^*(M|_{S_\alpha})$ by the composition isomorphisms $(g\circ f)^{-1}\cong f^{-1}g^{-1}$ of [det-pe-topos-functoriality-inverse-image] (5), since the branch composite equals $s_\alpha\circ t$; and for a trivializing pro-étale cover $\{U_i\to S_\alpha\}$ the base change $\{U_i\times_{S_\alpha}T\to T\}$ is a pro-étale cover by clause (1) of that node. A finite constant model pulls back to a finite constant model: base-change the trivializing cover and its finite scalar presentation, using the coefficient isomorphism [lem-sfb-alpha-iso] and the tensor pullback comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. The pulled-back presentation is a cokernel presentation with the same constant scalar matrix. Thus the leaf restrictions of $M$ have the local models to which step 4 applies. Empty leaves have the zero module category and zero completion map. No ordering of the original strata by an open-stratum argument is assumed.

Uses: sk-def-sfb-constructible, lem-fix-constructible-open-closed-refinement, lem-sfb-alpha-iso, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, det-pe-topos-functoriality-inverse-image.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md; Strata: replace an open-stratum induction by the qcqs open/closed refinement tree.

### Returned step 6

For each vertex $T$ of the tree of step 5 consider the cone $C_T$ of $c_{M|_T[0]}$. Step 2 identifies its restrictions to the two children with their corresponding cones; inverse image is exact, so it also identifies their cohomology. At a leaf the cone is zero by steps 4--5. Suppose the cones at both children of a vertex vanish. Each sheaf $H^q(C_T)$ then has zero restrictions to the complementary open and closed children. Their open immersion is quasi-compact by the refinement theorem, so [lem-exc-open-closed-detection] gives $H^q(C_T)=0$ for every $q$. Hence $C_T=0$ in the ordinary derived category. Finite upward induction reaches $V$, proving that every such constructible sheaf $M[0]$ is complete. This uses no Noetherian hypothesis on the space or on its structure sheaf.

Uses: lem-exc-open-closed-detection, lem-fix-constructible-open-closed-refinement.

Source: literature/stacks-project/proetale.tex; Tag 09AA, (1), with elementary finite induction using the open/closed detection lemma.

### Returned step 7

Choose $r\le s$ with $H^q(J)=0$ outside $[r,s]$. Each nonzero cohomology sheaf is constructible by [sk-def-sfb-constructible], hence complete by step 6. Use the successive-truncation triangles [lem-weil-pbc-truncation-triangle]. The initial truncation $\tau_{\le r-1}J$ is zero. Inductively the triangle with vertices $\tau_{\le q-1}J$, $\tau_{\le q}J$, and $H^q(J)[-q]$ has complete first and third vertices: shifts preserve completeness and the completion maps form a morphism of triangles by [lem-pe-completion-triangle-comparison]. The same long-exact-sequence argument as step 4 gives completeness of the middle vertex. At $q=s$, $\tau_{\le s}J\simeq J$. Thus precisely the strict-tower completion unit of the statement is an isomorphism; no auxiliary choice of an isomorphism to a limit has replaced it.

Uses: sk-def-sfb-constructible, lem-weil-pbc-truncation-triangle, lem-pe-completion-triangle-comparison.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Sections 3.5 and 6.5: completion triangles and bounded cohomological dévissage.

### Returned step 8

Fix $n\ge1$. The ring $k_n$ is finite by [lem-weil-l-adic-extension-integers-dvr] and [lem-weil-valued-dvr-finite-quotients]. For a local model $M=B_T\otimes_A P$, use the scalar resolution $0\to A^a\xrightarrow{u}A^b\to P\to0$ from step 4. By the K-flat calculation in [lem-pur-derived-change-of-rings], its derived reduction is $[(k_n)_T^a\xrightarrow{\bar u}(k_n)_T^b]$ in degrees $[-1,0]$. The finite-discrete equivalence [lem-sf-module-object-ordinary-coefficient-equivalence] identifies these terms and their maps with ordinary constant-$k_n$ module sheaves. The constant module functor is exact by [def-sfb-site-derived-constant-module-functor], so the two cohomology sheaves are the constant sheaves of $\ker(\bar u:k_n^a\to k_n^b)$ and $\operatorname{coker}\bar u$. These scalar modules are finite, being a subset and a quotient of finite sets. They are finitely presented over $k_n$: choose finitely many generators from all their elements, and finitely many relations from the finite kernel of the resulting map from a finite free $k_n$-module. Thus this computation supplies both the ordinary finite-stalk local models and the finite constant scalar local models for the reductions, with cohomology only in $[-1,0]$.

Uses: lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients, lem-sfb-finite-constant-model-two-term-free-resolution, lem-pur-derived-change-of-rings, lem-sf-module-object-ordinary-coefficient-equivalence, def-sfb-site-derived-constant-module-functor.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md; Local models: reduce the actual scalar matrix, then take its finite kernel and cokernel.

### Returned step 9

For any constructible integral sheaf $M$, restrict $M\otimes^L_{B_V}(k_n)_V$ to its original finite stratification and then to the trivializing pro-étale covers. The reduction/restriction compatibility from step 2 gives exactly the two-term complexes of step 8. Exact inverse image commutes with cohomology. Therefore every restricted cohomology sheaf is locally constant with finite $k_n$-values, so is constructible by [def-weil-proetale-constructible-sheaf]; it also has the finite scalar-model meaning of [sk-def-sfb-constructible], since the scalar modules in step 8 are finitely presented. The cover conservativity of [lem-zl-condensed-cover-restriction-conservative] and the same finite-tree detection as step 6 give vanishing outside $[-1,0]$ globally. Consequently $M\otimes^L(k_n)_V$ is bounded constructible in ordinary finite-coefficient coordinates, and the finite-discrete equivalence of [lem-sf-module-object-ordinary-coefficient-equivalence] gives the same assertion for the internal reduction.

Uses: def-weil-proetale-constructible-sheaf, sk-def-sfb-constructible, lem-zl-condensed-cover-restriction-conservative, lem-sf-module-object-ordinary-coefficient-equivalence.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md; Locality and strata, applied to finite quotient cohomology.

### Returned step 10

Apply the exact triangulated functor $-\otimes^L_{B_V}(k_n)_V$ of [lem-pur-derived-change-of-rings] to the finite sequence of truncation triangles used in step 7. Its graded vertices are $(H^q(J)\otimes^L(k_n)_V)[-q]$, bounded constructible by step 9. The finite-discrete equivalence [lem-sf-module-object-ordinary-coefficient-equivalence] preserves shifts and distinguished triangles. In ordinary finite-coefficient coordinates, [lem-weil-proetale-dbc-triangulated] therefore proves by induction that $J_n$ is bounded constructible. The bound can be taken to be $[r-1,s]$: each graded vertex has cohomology only in $[q-1,q]$, and exactness of the cohomology sequences [lem-sf-derived-homology-long-exact] preserves their common containing interval under extensions. In particular the bound is independent of $n$.

Uses: lem-pur-derived-change-of-rings, lem-weil-pbc-truncation-triangle, lem-sf-module-object-ordinary-coefficient-equivalence, lem-weil-proetale-dbc-triangulated, lem-sf-derived-homology-long-exact.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Section 6.3; bounded cohomological dévissage after finite reduction; Stacks Tags 09B5 and 09AL.

### Returned step 11

The finite discrete ring $k_n$ is Noetherian: any ascending chain of its ideals stabilizes because it is a chain of subsets of a finite set. Apply [sk-thm-pe-constructible-comparison] on the qcqs scheme $V$ to the ordinary bounded constructible reduction from step 10. Its derived equivalence gives $L_n\in D^b_c(V_{\mathrm{ét}},k_n)$ and an isomorphism $\alpha_n:\nu_V^*L_n\xrightarrow{\sim}J_n$ in ordinary finite-coefficient coordinates. Retain this pair, which is exactly the étale-origin witness of [def-weil-pbc-etale-origin-witness]; boundedness implies membership in $D^+$. The coefficient equivalence used here is precisely [lem-sf-module-object-ordinary-coefficient-equivalence]. Steps 7 and 10--11 give every asserted clause for arbitrary $n\ge1$. The hypotheses throughout were finite scalar models, a finite constructible stratification and qcqs for its refinement; no geometric condition involving $\ell$ was used.

Uses: sk-thm-pe-constructible-comparison, def-weil-pbc-etale-origin-witness, lem-sf-module-object-ordinary-coefficient-equivalence.

Source: literature/stacks-project/proetale.tex; Tags 09AI (constructible comparison) and 09AL (lemma-compare-constructible-derived).

## Searches and existing work

Each new id has five real msearch.py searches: LeanFinder, LeanSearch, Loogle, grep and a second LeanFinder phrasing. Queries, complete hit lists and verdicts are in the new node records and the searches.jsonl audit log. I read all hits. IsAdicComplete and AdicCompletion concern scalar modules; SheafOfModules.IsFinitePresentation concerns presentations without pro-etale derived completeness; HomologicalComplex limit and mapping-cone hits concern general complexes without our coefficient identification or normalized quotient unit. IsLocallyClosed and scheme-limit hits do not give finite-stratum completion detection. None is an exact match or a one-line specialization of a whole new statement. All searches completed; none is recorded as unavailable.

DAG searches used the full tag sets 09AA, 005H, 09YH, 09Y4, 09B5 and 09AL, plus completion/restriction/local model/finite quotient and title searches. Blueprint searches used finite constant, completion, finite scalar, open closed, reduction, strict, scalar model, finite stratification and finite quotient. The closest statements were opened individually. No imported blueprint node states one of the four new lemmas. The nearest blueprint ancestor is det-sf-comp-coherence-cocycle; every new from.via starts with this item and retains its inherited intermediate ancestors. Source-local arguments remain the finite-model route below the compactification-coherence unit.

## Not duplicates

lem-sfb-strict-completion-restriction-comparison vs def-pur-flasque-support: the existing node concerns Supported sections and flasque objects; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs def-sfb-proetale-unit-normalized-adjunction: the existing node concerns Unit-normalized adjunction for pro-etale module inverse image; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs det-formal-closed-support-ii-limits: the existing node concerns Closed support commutes with derived limits of sequences; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs det-lem-formal-closed-support-adjunction: the existing node concerns Sections with closed support: adjunction and fiber triangle for all coefficients; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs det-lem-formal-closed-support-sheaves: the existing node concerns Sections with support: the sheaf-level adjunction; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs det-lem-int-ext-bound: the existing node concerns Uniform vanishing of Ext between integral constructible sheaves; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs det-lem-int-tensor-pullback: the existing node concerns Integral inverse image preserves $\Dbc$ and agrees with the completed inverse image; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs det-prop-closed-adjoint-constructible-support: the existing node concerns Sections with support of a constructible complex are constructible; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs det-prop-p1-adjunction-rational-unit-counit: the existing node concerns Unit and counit for the rational projective line; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs det-sf-open-closed-pullback-limits: the existing node concerns Closed inverse image preserves limits; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs det-sf-open-closed-sequence-ring-sheaf: the existing node concerns The open–closed sequence for module sheaves over a sheaf of rings; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs det-sfb-dc-restricted-functors-closed-image: the existing node concerns Extension by zero and closed direct image preserve integral constructible complexes; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-a1-integral-constructible-reduction-fibres: the existing node concerns Ordinary finite quotients and adic fibres of an integral constructible heart object; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-a1-integral-stratum-chart-restrictions: the existing node concerns Exact integral restriction charts and their pullback square; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-cbc-extension-zero-stratified-perfect: the existing node concerns Extension by zero preserves stratified perfect local models; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-cbc-integral-compact-support-uniform-restriction: the existing node concerns Integral compact-support image preserves uniform constructibility; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-cbc-ringed-open-extension-products: the existing node concerns Products of ringed pro-etale open extensions without ambient quasi-compactness; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-exc-proetale-finite-supported-module-units: the existing node concerns Finite supported module units through the abelian comparison; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-formal-closed-pullback-derived-products: the existing node concerns Closed coefficient-compatible pullback preserves derived products; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-per-qbar-dual-recollement: the existing node concerns Verdier-compatible open and closed recollement for arbitrary-field adic coefficients; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-pur-classical-support-counit-identification: the existing node concerns Canonical identification of a supported triangle by its first arrow; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-pur-closed-supported-cup-vanishing: the existing node concerns Restriction to a closed support detects the zero action on supported cohomology; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-pur-flag-local-comparison: the existing node concerns Coordinate Gysin composition and the supported cup product; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-pur-proetale-injective-support-global-model: the existing node concerns Injective model for global sections of the closed support object; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-pur-support-localization-triangle: the existing node concerns Localization triangle for the exceptional inverse image; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sf-derived-immersion-comparison-normalization: the existing node concerns Derived open/closed site mates retain sheaf restriction normalization; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sf-finite-immersion-constructibility-interval: the existing node concerns Finite constructibility partitions and unchanged intervals for immersion restriction and closed direct image; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sf-locally-closed-closure-adjoint-realization: the existing node concerns Closure compactification realizes the immersion adjoint and its bounds; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sf-ring-sheaf-closed-localization: the existing node concerns Closed localization for arbitrary pro-etale ring-sheaf module objects; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sf-ringed-closed-kernel-adjoint: the existing node concerns The support-kernel adjoint for an arbitrary pro-etale ring sheaf; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-closed-supported-scalar-comparison: the existing node concerns Supported closed-unit construction and normalization of scalar comparison; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-condensed-support-derived-localization: the existing node concerns Open/closed localization for ordinary derived condensed module objects; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-condensed-support-projection-formula: the existing node concerns Natural support tensor projection formulas on unbounded condensed modules; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-continuous-qbar-constructible-generators: the existing node concerns Finite-cone generation for all-continuous algebraic-closure coefficients; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-integral-bounded-stratum-base-change: the existing node concerns Bounded ambient base change for integral stratum extension; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-local-integral-perfect-model-cohomology: the existing node concerns Cohomology of a local integral perfect scalar model; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-locally-closed-extension-coherence: the existing node concerns Restriction and composition for locally closed extension by zero; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-locally-closed-module-extension-coherence: the existing node concerns Normalized locally closed extension on module sheaves; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-normalized-immersion-comparison-coherence: the existing node concerns Coherence of comparison maps normalized on an immersion image; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-proetale-identified-open-closed: the existing node concerns Exact open and closed extensions with identified inverse-image coefficients; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-proetale-identified-supported-reconstruction: the existing node concerns Normalized supported reconstruction for actual tensor pullbacks; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-proetale-locally-closed-extension: the existing node concerns Pointwise exact locally closed extension; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-proetale-supported-reconstruction: the existing node concerns Normalized reconstruction from two successive support conditions; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-qcqs-integral-finite-model-completeness: the item proves completeness and classical reductions for bounded finite-Tor constructible complexes; this sublemma instead compares actual units under functors for arbitrary unbounded complexes, with no constructibility hypothesis.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-scalar-model-immersion-extension: the existing node concerns Open and closed extension preserve stratified finite scalar models; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-closed-costalk-duality: the existing node concerns Exceptional restriction of a Verdier dual; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-adic-flat-iff-supplied-model-flat: the existing node concerns Ambient and supplied-model Padic cohomology flatness; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-closed-immersion-scalar-change: the existing node concerns Ordinary closed scalar change with transported coefficients; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-condensed-open-closed-recollement: the existing node concerns Open/closed recollement for condensed coefficient modules; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-condensed-sheaf-ext-continuity: the existing node concerns Derived continuity for a single constructible condensed module sheaf; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-continuous-coefficients-immersion-restriction: the existing node concerns Continuous coefficient sheaves, localization and restriction to immersions; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-integral-model-open-closed-pieces: the existing node concerns Integral open and closed pieces remain constructible and rationalize to the localization sequence; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-proetale-abelian-closed-counit: the existing node concerns The closed counit on abelian pro-etale sheaves; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-proetale-abelian-closed-support: the existing node concerns Closed support for abelian pro-etale sheaves; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-proetale-closed-underived-projection: the existing node concerns Underived tensor projection for closed pro-etale immersions with arbitrary ring coefficients; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-proetale-immersion-limit-preservation: the existing node concerns Inverse images along immersions preserve pro-etale limits; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-proetale-inverse-image-limits-zariski-local: the existing node concerns Zariski locality of preservation of pro-etale inverse-image limits; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-proetale-restriction-preserves-limits: the existing node concerns Limits preserved by weakly etale pro-etale restriction; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-proetale-ringed-closed-counit: the existing node concerns Closed ringed counit is invertible; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-proetale-ringed-open-closed: the existing node concerns Ringed pro-etale open-closed localization; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-stratum-completion-unit-restriction: the existing node concerns Restriction and finite-stratum detection of the adic completion unit; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-stratum-ambient-hom: the existing node concerns Internal Hom from extension along a stratum; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: the existing node concerns finite model on immersion range; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: the existing node concerns condensedSurjectiveClosedPullback isEquivalence; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: the existing node concerns lfp lowerStar of surjective closed; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs prop-exc-open-adjoint: the existing node concerns The right adjoint for an open immersion; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs prop-sf-closed-immersion-unit: the existing node concerns The closed-immersion exceptional unit; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs prop-sf-closed-unit-all-stages: the existing node concerns Closed direct image is fully faithful at every coefficient stage; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs prop-sf-localization-all-stages: the existing node concerns The closed-support triangle at every coefficient stage; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs sk-lem-formal-closed-support-ii: the existing node concerns Closed support, truncation and derived limits; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs sk-lem-int-ext: the existing node concerns Continuity and boundedness of Ext; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-strict-completion-restriction-comparison vs sk-lem-int-tensor: the existing node concerns Inverse image and tensor product; this node compares the strict quotient tower and its specified augmentation under both the section-action equivalence and immersion/slice inverse image for arbitrary schemes.

lem-sfb-finite-strata-completion-detection vs def-fix-scheme-refinement-tree: the existing node concerns Recursive finite scheme refinement trees; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs def-weil-constructible-subset: the existing node concerns Constructible subset; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs def-weil-pbc-w-local: the existing node concerns Patch topology and w-local affine schemes; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-fix-constructible-open-closed-refinement: the existing node concerns Finite open–closed refinement through constructible strata; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-fix-constructible-open-closed-refinement-tree: the existing node concerns Finite binary pullback refinement tree; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-fix-constructible-tensor-completion: the existing node concerns Ordinary and completed tensor agree on integral constructible complexes; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-fix-scheme-refinement-tree-encoding: the existing node concerns Parent-before-child numbering of refinement trees; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-sc-perfect-lowest-rank-bound-open: the existing node concerns Rank-bound open and factorization for perfect lowest cohomology; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-sc-picard-universal-rank-match-fixed-rank-retrocompact: the existing node concerns Retrocompactness of a fixed-rank universal Picard point locus; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-sf-constructible-partition-local-closed-stratum: the existing node concerns Locally, a stratum of a constructible partition is closed with quasi-compact complement; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-sfb-finite-stratification-wide-pullback: the existing node concerns Finite constructible stratifications have a limiting common fibre-product refinement; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-sfb-stratified-tor-interval-devissage: the existing node concerns Uniform local-model Tor bounds extend across finite constructible strata; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-weil-pbc-affine-basic-sets-disjoint-refinement: the existing node concerns A finite union of sets D(f) ∩ V(g_1,…,g_n) in an affine spectrum is a finite disjoint union of such sets; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-weil-pbc-constructible-abelian-bounded-exponent: the existing node concerns A constructible abelian sheaf on a quasi-compact scheme is killed by a positive integer; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-weil-pbc-constructible-in-retrocompact-open: the existing node concerns A constructible subset of a constructible subset is constructible; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-weil-pbc-constructible-intersection-in-constructible: the existing node concerns The trace of a constructible set on a constructible set is constructible there; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-weil-pbc-constructible-is-retrocompact: the existing node concerns Constructible subsets are retrocompact; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-weil-pbc-constructible-qcqs-affine-local: the existing node concerns Constructible sheaves of modules on a qcqs scheme: global partition iff affine-local (Stacks 095E); this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-weil-pbc-constructible-stratification-intersection: the existing node concerns Common refinement of two stratifications with constructible strata; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lem-weil-pbc-spectral-constructible-clopen-constructible-topology: the existing node concerns Constructible subsets of a spectral space are open and closed in the constructible topology; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs lemma-weil-pbc-constructible-finite-pushforward: the existing node concerns Constructible sheaves reduce to finite pushforwards; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-finite-strata-completion-detection vs thm-constructible-serre: the existing node concerns Constructible sheaves form a weak Serre subcategory; this node additionally tests actual completion cones and all cohomological vanishing on stratum covers, and transports the same scalar matrices along leaf-to-stratum morphisms.

lem-sfb-strict-completion-restriction-comparison vs lem-sfb-adic-stratum-completion-unit: the existing result assumes a Noetherian base and uses intrinsic Koszul completeness; the new result has arbitrary schemes, the specified principal strict-tower unit and an explicit section-action equivalence.

lem-sfb-strict-completion-restriction-comparison vs lem-weil-pbc-stratum-completion-unit-restriction: the existing result assumes Noetherian X; the new comparison is for arbitrary schemes and also identifies internal/ringed-site coordinates and cone/Roos augmentations.

lem-sfb-finite-scalar-local-model-complete vs lem-sfb-integral-lisse-module-complete: the existing result is for finite locally free integral modules; the new result includes finitely presented torsion scalar modules via length-one free resolutions and cover descent.

lem-sfb-finite-scalar-local-model-complete vs det-prop-integral-criterion-constant-coefficients: the existing result compares derived-complete subcategories and gives flatness of the constant-to-completed coefficient map; it does not assert the specified completion unit is invertible on arbitrary finite scalar local models.

lem-sfb-finite-strata-completion-detection vs lem-sfb-adic-stratum-completion-unit: the existing detection assumes Noetherian X; the new detection is for qcqs X and includes same-matrix leaf-cover transfer and all cohomological degrees.

lem-sfb-finite-strata-completion-detection vs lem-weil-pbc-stratum-completion-unit-restriction: the existing detection assumes Noetherian X; the new result only assumes qcqs and finite constructible locally closed strata and retains actual leaf maps, with no open-stratum induction.

lem-sfb-finite-model-sheaf-quotient-constructible vs lem-weil-pbc-perfect-strata-uniform-reductions: the existing result assumes a Noetherian scheme and stratified perfect complexes; this one treats finite-scalar-model sheaves on arbitrary qcqs schemes with the explicit uniform [-1,0] calculation.

lem-sfb-finite-model-sheaf-quotient-constructible vs lem-sfb-adic-constructible-finite-reductions: the existing result assumes Noetherian X, derived completeness and an etale-origin residue object; this one starts from integral sheaf scalar models without any completeness hypothesis.

lem-sfb-finite-model-sheaf-quotient-constructible vs det-prop-integral-criterion-reductions: the existing result assumes Noetherian X and completeness plus a constructible first reduction; this one constructs all finite reductions directly from scalar sheaf models on qcqs X.

lem-sfb-finite-model-sheaf-quotient-constructible vs lem-sfb-finite-discrete-constructible-model: the existing result compares finite-coefficient constructible objects with etale realizations on Noetherian schemes; this one calculates derived reductions of integral sheaves without Noetherianity and without asserting an etale witness.

lem-sfb-finite-model-sheaf-quotient-constructible vs lem-sfb-local-integral-perfect-model-cohomology: the existing result identifies integral cohomology of an already supplied perfect scalar model; this one computes finite derived reductions of constructible integral sheaves, their explicit kernels/cokernels and their global uniform bound.

lem-sfb-finite-scalar-local-model-complete vs lem-sfb-qcqs-integral-finite-model-completeness: this sublemma treats a single locally finite scalar sheaf on any scheme, without finite stratifications, bounded-complex assembly or classical reduction witnesses.

lem-sfb-finite-model-sheaf-quotient-constructible vs lem-sfb-qcqs-integral-finite-model-completeness: this sublemma treats sheaves, gives explicit finite-quotient matrices and cohomology in [-1,0], and makes no completeness or etale-witness conclusion.

