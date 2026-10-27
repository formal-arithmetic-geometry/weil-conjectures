# prop-sf-open-closed-triangle-all-stages: repair of G1/A6/D

## Worker report

This repairs the returned delivery substantively: **five new statement-only nodes**, not a rebase or unchanged re-push. The parent retains its statement and statement dependencies verbatim, has seven assembly steps (2569 characters), and extracts the missing arguments specified in the return. Every new node is unsplit, with an empty proof and proof_deps, its own self-contained statement, blueprint provenance, and real Mathlib search records. No Mathlib leaf is claimed.

## Files written

- `dag/nodes/sec-smooth-purity/prop-sf-open-closed-triangle-all-stages.json`: repaired assembly, provenance and split report; all imported, Lean and maintainer metadata retained.
- `dag/nodes/sec-smooth-purity/lem-sf-finite-immersion-constructibility-interval.json`: statement; unsplit; no Mathlib match. Finite constructibility partitions and unchanged intervals for immersion restriction and closed direct image.
- `dag/nodes/sec-smooth-purity/lem-sf-rational-localization-triangle-orthogonality.json`: statement; unsplit; no Mathlib match. Normalized rational localization triangles and cross-object orthogonality.
- `dag/nodes/sec-smooth-purity/lem-sf-qbar-localization-common-stage.json`: statement; unsplit; no Mathlib match. Common-stage descent of localization data and cross-stage orthogonality.
- `dag/nodes/sec-smooth-purity/lem-sf-automorphism-constructible-stage-equivalence.json`: statement; unsplit; no Mathlib match. Automorphism pullback preserves constructible categories at every coefficient stage.
- `dag/nodes/sec-smooth-purity/lem-sf-open-closed-weil-mate-structures.json`: statement; unsplit; no Mathlib match. Explicit Frobenius mates, outer Weil structures and the unit-counit squares.
- `report.md` and `citations.json`: the current report and one verbatim current-statement quote for every citation of every assembly step.
- Sandbox research artifacts retain the actual search outputs and query plan. `original-node.json` retains the original sixteen-step proof; `retained-returned-report.md` and `retained-returned-citations.json` preserve the previous report and citations. These auxiliary files are not delivered node files.

## Attachments

None. I searched the actual `lean/WeilConjectures/` tree by the item id, openClosed/exists_distTriang_openClosed, constructible pullback and automorphism/constructibility. `AlgebraicGeometry.WeilComplex.exists_distTriang_openClosed`, `WeilSheaf/LowerShriekFunctoriality.lean:171`, still has `sorry` at line 182 and its docstring explicitly says its first two arrows are not pinned. `AlgebraicGeometry.Etale.exists_distTriang_openClosed`, `SixFunctors/OpenClosed/Derived.lean:264`, is a proof for the ordinary etale derived category, not the four coefficient stages and their normalized Weil structures. The constructible etale pullback lemma in `CategoryTheory/DerivedCategory/Constructible.lean:263` is likewise not the new finite pro-etale restriction-and-closed-image statement. None is an attachment for this item or an exact replacement of a new statement.

## WANTED

None. The actual available source is `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.md` and its `.proof.md`. I read both. The original imported source path under `master` is historical; its metadata is retained. This repair follows the original ringed short-exact-sequence route, not a change of coefficient category to condensed coefficients and not an SGA trace route.

## The return, point by point

G1/A6/D asks for at least five genuinely new arguments, while permitting reuse where existing statements carry the old work. The initial required dry run of the retained seven-step, zero-new-node split passed at `3d24381a2fc`. That receipt does not answer the mathematical return; it is superseded by this repair. Comparison of `original-node.json` with the current read-only repository showed no field difference, so the original sixteen-step proof is the current returned-head reference.

1. Old step 1: the new finite-immersion node states the actual pullback partitions, closed-image partition plus open complement, exact cohomology comparisons and unchanged interval for i^*, j^*, i_*. The existing open-interval node supplies only j_!, so it is retained rather than duplicated. The Noetherian/finite-type argument stays in assembly step 1.
2. Old step 10: the new rational node pins the four actual functors, rationalized adjunctions and components of the counit/unit, image of any given integral completion, and the cross-object Hom tensor formula. It includes arbitrary rational morphisms and explicitly excludes an added Karoubi completion.
3. Old step 11: the new common-stage node states coherent descent for all four operations and both adjunctions, the exact finite-stage triangle, and the colimit formula for N and M at different fields. Every later-stage group is zero. This is not just a same-stage objectwise assertion.
4. Old step 12: the new automorphism node restores preservation of finite constructibility partitions and of the same reduction interval, actual completed coefficients and completion maps, inverse automorphism, exact triangulated and coefficient-linear equivalence at all four stages, and coherent b,d for commuting immersions. Scheme automorphisms need not be k-linear.
5. Old steps 13-15: the new mate node includes explicit alpha and c, defines a as alpha inverse, states both mate equations, and includes the full theta_A/theta_C formulas and first two squares in its statement. These formulas are no longer only in the report. Old step 16 remains an explicit assembly argument: triangle-morphism extension (2), the exact Frobenius image triangle, and cross-object vanishing give the third square, with its formula written out.

Existing statements, read again, retain old step 3 through `lem-sf-immersion-completed-pullback-comparison`; old 4 through `lem-sf-ringed-open-roos-preservation`; old 5 through `lem-sf-open-semilinear-tensor-model` and `lem-sf-integral-open-reduction-comparison`; the actual completion units through `lem-sf-open-quotient-koszul-completeness`; open adjunction normalization through `lem-sf-open-reduction-adjunction-transport`; closed step 6 through `prop-weil-pbc-direct-image-limits`; and old 8-9 through exact derived adjunction plus `lem-weil-pbc-triangle-morphism-extension` (2),(3). These are legitimate reuse of the statements identified by the maintainer, not five newly counted nodes. The five files listed above are genuinely additional work items.

## Not duplicates

I searched the whole DAG by ids, titles, notions, and the finite/rational/common-stage/automorphism/mate keywords, and the whole imported blueprint through `tools/blueprint_refs.py search`. Broad searches (constructibility, orthogonality, automorphism, mate, common-stage) were followed by targeted searches (open-closed, rational-transport, descent-functors and the specific new obligations). A phrase search was treated as a phrase, not as evidence that separately spelled words were absent. Existing ordinary-etale and condensed-module results were opened, with their categories kept distinct. The new nodes each have a strictly smaller task than the parent; none supplies its entire conclusion. The specific finer-splitting instruction explicitly requests these five separable arguments, overriding the earlier response that reused generic data but omitted their specialized normalization and constructibility obligations.

- lem-sf-finite-immersion-constructibility-interval vs lem-sf-open-finite-constructibility-interval: existing theorem covers j_! only; new theorem covers i^*, j^*, i_* with their actual finite stratifications and intervals, and does not restate j_!.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-finite-pullback-constructibility: existing theorem concerns intrinsic finite-quotient module inverse image alone and explicitly has no derived object, interval or direct image; new theorem includes closed-image partitions and exact cohomological interval control.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-condensed-constructible-open-closed-images: existing theorem is internal condensed modules with locally finitely presented strata; new theorem uses constant finite A_n-modules and finite-module restrictions in the specific finite-torsion category.
- lem-sf-rational-localization-triangle-orthogonality vs prop-weil-pbc-rational-transport: existing theorem transports supplied exact linear functors/transformations abstractly; new theorem identifies the actual immersion operations, their rational adjunctions and maps, and cross-object orthogonality; it does not assert that arbitrary morphisms preserve constructibility.
- lem-sf-qbar-localization-common-stage vs prop-weil-pbc-descent-functors: existing theorem descends supplied coherent families; new theorem supplies the localization families and adjunctions, finite-stage triangle comparison and cross-stage zero-Hom formula for two different coefficient fields.
- lem-sf-automorphism-constructible-stage-equivalence vs lem-sf-automorphism-completion-unit-comparison: existing theorem explicitly has no constructibility or boundedness hypothesis/conclusion; new theorem restricts to the finite/integral constructible categories with intervals and then passes to both field stages.
- lem-sf-automorphism-constructible-stage-equivalence vs lem-sf-completed-coefficient-pullback-linearity: existing theorem supplies scalar squares and A-linearity but no constructibility preservation, uniform interval or all-stage equivalence.
- lem-sf-automorphism-constructible-stage-equivalence vs new-p6-lisse-automorphism-equivalence: existing theorem is only the etale lisse algebraic-coefficient category; new theorem is the bounded constructible finite/integral/rational/common-stage pro-etale derived categories.
- lem-sf-automorphism-constructible-stage-equivalence vs lem-pod-semilinear-field-operation-lifts: existing theorem includes exact field-stage Frobenius equivalence on supplied constructible domains; new theorem supplies finite/integral constructibility, actual completion/reduction compatibility and unchanged uniform intervals for any scheme automorphism.
- lem-sf-open-closed-weil-mate-structures vs lem-weil-mate-iso-along-equivalences: existing theorem proves abstract invertibility for a supplied square; new theorem specifies the actual immersion mates, all coefficient-stage normalizations and two explicit Weil squares.
- lem-sf-open-closed-weil-mate-structures vs lem-pur-rational-weil-naturality-mate: existing theorem is smooth purity and exceptional-adjoint comparison, not the open counit/closed unit and two outer localization structures.
- lem-sf-qbar-localization-common-stage vs lem-a1-qbar-open-closed-cohomology: existing theorem is a smooth curve cohomological-heart statement, not common-stage localization descent and arbitrary cross-stage orthogonality.
- lem-sf-finite-immersion-constructibility-interval vs lem-sfb-local-integral-perfect-model-cohomology: existing theorem identifies local cohomology of a supplied perfect integral model, explicitly without global constructibility; the new theorem is finite-torsion constructibility under three immersion operations.
- lem-sf-finite-immersion-constructibility-interval vs lem-sfb-condensed-support-projection-formula: existing theorem is a derived tensor projection formula for condensed coefficients, not finite partitions or cohomological intervals.
- lem-sf-finite-immersion-constructibility-interval vs det-sfb-dc-restricted-functors-closed-image: existing theorem is integral completeness and boundedness for j_!, i_* plus a stratified-generation consequence; the new theorem is finite constant coefficients with explicit i^*, j^*, i_* partitions and the unchanged interval.
- lem-sf-finite-immersion-constructibility-interval vs sk-lem-int-ext: existing theorem is continuity of integral Hom and Ext bounds; the new theorem has no Ext or colimit claim.
- lem-sf-finite-immersion-constructibility-interval vs det-lem-int-ext-bound: existing theorem is a cohomological-dimension estimate on integral Ext for stratum extension; the new theorem asserts finite constructibility and exact interval preservation.
- lem-sf-finite-immersion-constructibility-interval vs lem-sfb-locally-closed-module-extension-coherence: existing theorem gives coherent abelian extension for arbitrary ring sheaves and explicitly no derived assertion; the new theorem gives finite constructible derived restrictions and closed images.
- lem-sf-finite-immersion-constructibility-interval vs det-formal-closed-support-ii-limits: existing theorem preserves products and Roos triangles for support operations on unbounded condensed coefficients; the new theorem concerns finite constructible partitions and intervals.
- lem-sf-finite-immersion-constructibility-interval vs sk-lem-formal-closed-support-ii: existing theorem gives left t-exactness and sequential limit compatibility of derived support; the new theorem concerns exact finite immersion restrictions/closed direct image and constructibility.
- lem-sf-finite-immersion-constructibility-interval vs lem-sfb-proetale-locally-closed-extension: existing theorem constructs a fully faithful exact abelian extension for arbitrary ring coefficients; it states no finite constructibility or same-interval derived result.
- lem-sf-finite-immersion-constructibility-interval vs lem-sfb-integral-bounded-stratum-base-change: existing theorem is a bounded integral base-change comparison with no constructibility/completeness assumption; the new theorem is finite-module stratification preservation.
- lem-sf-finite-immersion-constructibility-interval vs lem-formal-closed-pullback-derived-products: existing theorem is arbitrary-product preservation for a condensed module closed pullback; the new theorem asserts finite constructibility and same-interval behavior for three operations.
- lem-sf-finite-immersion-constructibility-interval vs lem-sfb-closed-supported-scalar-comparison: existing theorem is normalized invertibility of a supported scalar-comparison morphism, not finite constructible stratifications.

The same-tag comparisons above concern the support inputs 09AA/09BM/09AH. I opened their statements; a shared Stacks input is not an identification of these coefficient categories. The final server preflight checks this against the current DAG as well.

The first repaired dry run requested these additional same-tag comparisons against the server clone. I opened all twelve current statements and distinguished their conclusions as follows.

- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-closed-immersion-scalar-change: existing theorem is an ordinary scalar-change/direct-image isomorphism, with no finite constructibility or cohomology interval conclusion.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-condensed-open-closed-recollement: existing theorem supplies bounded-below localization and adjunctions for arbitrary condensed coefficient modules, with no finite constant-module constructibility restriction.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-integral-model-open-closed-pieces: existing theorem concerns continuous-constructible integral sheaves and their E-valued rationalization, not the finite-torsion derived categories and unchanged intervals of this lemma.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-proetale-abelian-closed-counit: existing theorem gives full faithfulness of abelian closed direct image; it does not assert constructibility, partitions or cohomological intervals.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-proetale-abelian-closed-support: existing theorem reconstructs an abelian sheaf supported on the closed part, with no finite constructibility assertion.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-proetale-closed-underived-projection: existing theorem identifies an underived tensor projection map for arbitrary ring sheaves; no finite stratification or cohomological interval claim occurs.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-proetale-immersion-limit-preservation: existing theorem asserts exactness and all-limit preservation of inverse image, not finite constructibility, closed-image stratifications or derived interval preservation on the constructible categories.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-proetale-inverse-image-limits-zariski-local: existing theorem glues inverse-image limit preservation from affine opens; no constructibility or closed pushforward conclusion occurs.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-proetale-restriction-preserves-limits: existing theorem is all-limit preservation for weakly etale inverse image on set sheaves; the new lemma treats finite-module constructibility and derived bounds, including a closed immersion.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-proetale-ringed-closed-counit: existing theorem says the specified module adjunction counit is invertible; no finite constructibility or same-interval conclusion occurs.
- lem-sf-finite-immersion-constructibility-interval vs lem-weil-pbc-proetale-ringed-open-closed: existing theorem gives ambient exactness, support identities and the localization sequence; new lemma supplies the missing finite constructibility partitions and exact derived interval control.
- lem-sf-finite-immersion-constructibility-interval vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: existing theorem transfers a supplied locally finitely presented condensed coefficient model to a morphism whose range lies in the immersion; it is not preservation of finite constant-module stratifications and derived intervals by i^*, j^*, i_*.

## Mathlib searches

The original item's eight historical records are preserved; they are not represented as searches rerun today. For each of the five new nodes I ran two distinct LeanFinder formulations, LeanSearch, Loogle, and grep through the required `msearch.py`, read the returned hits, and kept their outputs in sandbox search files and their exact query texts in each node. LeanSearch and LeanFinder were available. The first rational Loogle query used an unknown namespace identifier and the first mate query an unknown NatIso identifier; I recorded those errors and corrected both with valid substring/name patterns. The corrected results and extra targeted greps are also recorded, not silently substituted for the failed attempts.

Finite hits are topological constructibility, etale site definitions, and structure-sheaf restriction functors, not constructibility of finite-torsion pro-etale complexes. Rational hits are generic triangulated localization and orthogonal subcategories; `Mathlib/CategoryTheory/Triangulated/Orthogonal.lean:108,124`, read in place, concerns localization at P.trW and preservation of certain Hom sets, not scalar-localized immersion operations/adjunction normalization. Common-stage hits give filtered cocones, generic derived adjunctions and field algebraicity, not the field-pair category with these operations. Automorphism hits give abstract equivalences and ordinary scheme-ring/restriction facts; none carries completed coefficient constructibility and uniform reduction bounds. Mate hits do give the underlying algebra, already represented by existing DAG tool nodes: I read `Mathlib/CategoryTheory/Adjunction/Mates.lean:285,300` for the conjugate counit/unit identities and its warning that general square mates need not preserve isomorphisms. This is why the new statement uses vertical equivalences and specifies the actual coefficient-stage functors, comparisons and Weil structures rather than claiming the generic mate algebra is absent from Mathlib. All five new nodes remain unsplit; no leaf is claimed from a partial candidate.

## Review by O1

I read the full repair note, delivery-errors B-E, the three blueprint levels in SETUP, GOAL, the stage-1 contract, and the recorded chapter/unit. The parent statement is unchanged against the current blueprint. The source proof's claim that the connecting map factors through a zero map is read correctly: the factor from the shifted open term into the closed term is zero; the connecting map need not be zero. This correction was already in the retained detailed argument and is maintained. The source's finite/integral/rational/common-stage/Weil paragraphs are all represented. No level-1 or level-2 route or target statement is altered.

For the finite-immersion new node I read the finite paragraph and original step 1, its finite-torsion definition, and the ringed support statement. I also read Stacks proetale.tex, labels lemma-closed-immersion (09AA), lemma-closed-immersion-complement-retrocompact-exact (09BM), lemma-ses-associated-to-open (09AH), and lemma-j-shriek-limits (09BP). The partitions in the new statement are actual fiber-product subschemes, not an unjustified factorization through a subset. Noetherian means locally Noetherian and quasi-compact, and it makes the open complement retrocompact as required for exact i_*. The finite constructibility node defines a finite partition with finite-module locally constant restrictions, which is exactly what is asserted. Empty strata and a nonreduced closed immersion are allowed. The existing j_! node is explicitly separate.

For the rational new node I read the rational paragraph, the raw rationalization definition, rational transport and operation-reduction statements. Raw localization has exactly the same objects and Hom tensored with E; there is no idempotent completion here. The new statement uses an arbitrary supplied distinguished integral completion, so it does not obtain integral existence by citing its parent. Its other obligations are exactness and normalization of the actual immersion functors/adjunctions and the zero cross-Hom formula. An arbitrary rational morphism may involve a denominator, so the assertion is genuinely natural on the rational Hom group, not just on integral maps. A zero integral Hom group still tensors to zero, without any flatness inference for an unrelated module.

For the common-stage new node I read the algebraically closed paragraph and the whole common-stage definition and descent/scalar-extension/Verdier statements. I verified that an exact finite-stage inclusion is stated, and that the Hom formula is for two possibly different original fields. The source hypotheses of scalar extension are Noetherian, finite-dimensional schemes and invertible ell; these hold on X,U,Z because they are finite type over k and ell differs from p. The new statement does not choose an integral Frobenius-stable lattice, and it does not assume all original maps are defined at the smaller field. Coherence is part of the conclusion, not inferred from unrelated vertex isomorphisms.

For the automorphism new node I read the Weil paragraph, geometric-Frobenius definition, site-isomorphism statement, profinite coefficient comparison, completed-coefficient linearity and actual completion-unit comparison. The last comparison has no boundedness or constructibility conclusion, so I explicitly added the missing finite partitions and same interval of every integral reduction as a separate work obligation. Ordinary pullback along a scheme automorphism and its inverse are exact reindexing equivalences; the chosen coefficient comparisons respect quotient maps and composites. Rationalization and common-stage passage retain both inverse-composition identities. The argument uses a scheme automorphism even when it is semilinear over k; no k-linearity has been smuggled in.

For the mate new node I read the final source paragraph, both adjunction-mate definitions, the mate-invertibility and unit/counit/pasting tool statements, and the explicit original steps 13-15. I type-checked each composite by hand: alpha starts in j_!F_U N and ends in F_Xj_!N, so a is its inverse; c starts in F_Xi_*M and ends in i_*F_ZM, using d inverse before the closed counit. The first mate equation starts in F_Xj_!j^*K, and the second starts in F_XK. The theta formulas therefore start in F_X A_K and F_X C_K and end in A_K and C_K, respectively. Their isomorphism claims use the vertical automorphism equivalences, not an invalid assertion that arbitrary mates of isomorphisms are invertible. The new node asserts the first two squares but no localization-triangle existence or third-square claim, so it does not restate the parent.

For assembly step 1 I opened every cited statement: finite-type-over-Noetherian and open-subscheme-Noetherian give the required geometric hypotheses; the two finite constructibility statements cover the three immersion functors and j_!; the ringed theorem supplies the actual counit/unit short exact sequence; the complex theorem supplies the distinguished triangle; exact-functor derived realization pins its vertices/maps. The quotient-chart and finite principal-open-cover arguments are the elementary finite-type verification kept in the step, not hidden new inputs.

For step 2, the immersion comparison states the actual completed pullback comparison, quotient projections and common interval. The open Roos statement preserves the canonical product projections and 1-s maps; the semilinear tensor statement gives a flat-term K-flat model and the simultaneous generator map [x] tensor a to [x tensor a|_U], including transitions and both scalar-unit augmentations. The integral-open comparison identifies reduction systems and actual reconstruction maps. Open-adjunction transport states the realized unit/counit equalities before evaluating systems. Thus old steps 3-5, including the product/kernel calculation and strict tensor maps, are genuinely assigned to existing nodes, not erased by the shorter parent. The compact-support definition uses the compactification U -> X -> X with identity proper part, so its normalization agrees.

For step 3, the quotient/Koszul statement supplies every adic hypothesis of the direct-image-limits theorem for R, including Noetherianity, torsion residue ring and the perfect finite-free resolution [R --t^n--> R]. The tower theorem explicitly states the direct-image/total-limit isomorphism, finite projection formula, quotient transition and completion-unit compatibility. The finite immersion node supplies finite constructibility and the common interval for every closed-image reduction. The integral category definition and triangulated-subcategory theorem then put the ambient short-exact-complex triangle in the correct full subcategory. Exact derived realization and derived adjunction retain the unit and counit, rather than merely isomorphic outer objects.

For step 4, the ringed theorem literally gives j^*i_*=0. Exact derived adjunction gives Hom(j_!N[m],i_*M)=Hom(N[m],j^*i_*M)=0 for independent N,M at finite/integral stages. I read triangle-morphism-extension (2),(3): it requires Hom(A[1],C')=0 and the first two squares, exactly what is available. This proves naturality and uniqueness of delta, not delta=0. Both shifts m=0 and m=1 are covered.

For step 5, the two new field-stage statements give exactly the normalized triangle and cross-object vanishing used. The dimension theorem applies to all three finite-type schemes. The first step supplies Noetherianity and the standing coefficient datum gives ell invertible. Thus no generic direct-image-preserves-constructibility claim has been added. Applying step 4 at each field/common-stage category is justified for every morphism by the stated Hom formulas and natural adjunction maps.

For step 6, the geometric-Frobenius definition says g_T=id times Spec(gamma), so the base-changed immersions commute with it; the new automorphism theorem supplies the bounded-constructible exact equivalences, inverse, shift comparison and b,d at all stages. This restores the constructibility assertion absent from the returned node.

For step 7, the new mate node literally states all a,c,theta_A,theta_C formulas and both first squares used. The exact image under F_X of the existing distinguished triangle is distinguished. With A'=A_K,C'=C_K, triangle-morphism-extension (2) has source first vertex F_XA_K, and its required Hom(F_XA_K[1],C_K) vanishes: a identifies the first object with j_!F_Uj^*K, which lies in the open category by step 6, and cross-object vanishing applies. Consequently delta_K theta_C = theta_A[1] F_X(delta_K), with the canonical shift comparison. This is the third square itself, written in the parent's proof; I do not move it to an assertion of triangulation on Weil pairs.

Small cases checked: X, Z or U empty; identity open or closed immersion; zero complexes; n=1 and all n>=1; arbitrary intervals and all integer shifts; nonreduced Z; inverse automorphism including identity; Frobenius not k-linear; distinct coefficient fields and further common extensions; rational maps with denominators. Empty partitions may be omitted; no step requires a nonempty geometric point. No new statement is false on these cases. No parent statement correction or dispute is needed. Each new proof is intentionally empty, and there is no proof sketch hidden in a statement. The seven parent steps are all below 2000 characters individually. This repair neither writes Lean nor runs a compiler/Lake/build nor writes in the repository or launcher.

## Verification

The next server dry run detected grouped references such as [def-a, def-b] rather than separately bracketed node references. I normalized every new statement to [def-a], [def-b] and regenerated the verbatim citations; the mathematical statements and dependency lists are unchanged. The final repaired delivery is checked by the required server dry run; its final receipt and push outcome are recorded after those processes exit. No local check_dag/review_split/preflight tool is run.

## Original argument retained verbatim, with its new location

The following sixteen texts are copied from original-node.json without shortening. They preserve the argument for future workers; the location line assigns each argument to a new statement-only node, an already existing statement, or an explicit parent step. Citations after each are the original citation ids, not additional undeclared uses of the shortened assembly.

### Original step 1

Location: New finite-immersion node plus existing j_! interval node; elementary geometry in assembly 1.

The schemes in the statement are Noetherian: a field has only the ideals $0$ and $(1)$, so its spectrum is Noetherian, and apply [lem-weil-pbc-finite-type-over-noetherian]. Here $Z$ is finite type over $k$: intersect a finite affine finite-type cover of $X$ with $Z$ and take quotient coordinate rings. The open $U$ is also finite type over $k$: each of its intersections with those Noetherian affines is quasi-compact, hence a finite union of principal opens, whose rings are finitely generated over $k$ by adjoining an inverse. Every open in a Noetherian affine is quasi-compact by [lem-weil-pbc-noetherian-open-subscheme-noetherian], so $j$ is quasi-compact. We will use the ringed sheaf sequence with this hypothesis. At finite coefficients, inverse image along $i$ or $j$ preserves constructibility: intersect a finite locally closed constructible partition with $Z$ or $U$, and restrict the locally constant finite modules. Extension by zero along $j$ preserves constructibility: use the partition on $U$, viewed in $X$, together with $Z$, on which the restriction is zero. Direct image along $i$ preserves constructibility: view the partition of $Z$ in $X$ and add $U$, using $i^{-1}i_* = \mathrm{id}$ and $j^{-1}i_*=0$. These identities and exactness of $j_!,i_*$ are supplied by [lem-weil-pbc-proetale-ringed-open-closed]; exactness of inverse images is [def-weil-pbc-proetale-operations]. Thus each functor preserves the cohomological interval of a bounded finite-coefficient complex, since exact functors commute with kernels, images and cokernels. The partition condition is exactly [def-weil-finite-torsion-constructibility].

Original citations: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian, def-weil-finite-torsion-constructibility, lem-weil-pbc-proetale-ringed-open-closed, def-weil-pbc-proetale-operations.

### Original step 2

Location: Parent assembly 1, using ringed short exact sequence, exact derived realization and complex triangle nodes.

At finite coefficients apply the counit--unit short exact sequence of [lem-weil-pbc-proetale-ringed-open-closed] to every term of a representative complex of $K$. The maps are natural in the sheaf, hence commute with the differentials. By [lem-weil-pbc-complex-ses-triangle] this short exact sequence of complexes gives a distinguished triangle $j_!j^{-1}K\to K\to i_*i^{-1}K\to j_!j^{-1}K[1]$. The exact functors induce triangulated functors by [lem-sf-exact-functor-derived-triangulated], and their ordinary derived functors are their termwise functors by [lem-weil-pbc-exact-functor-derived-functor]. Thus the vertices and first two maps are exactly those in the statement. Step 1 puts the triangle in the full bounded constructible subcategory. This is the unit's termwise sheaf-sequence argument, with the ringed pro-etale sequence supplying the sheaf calculation; it does not assume ordinary geometric stalks conservative on arbitrary pro-etale sheaves.

Original citations: lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-complex-ses-triangle, lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-exact-functor-derived-functor.

### Original step 3

Location: Existing lem-sf-immersion-completed-pullback-comparison, parent assembly 2.

For the integral stage put $R_T=\widehat{\mathcal O}_{E,T}$ and $A_n=\mathcal O_E/\varpi_E^n$. By [lem-weil-pbc-profinite-coefficient-inverse-image] the actual inverse-image coefficient sheaves for $i,j$ are $R_Z,R_U$, compatibly with all finite quotient maps. Write $I=i^{-1}$, $J=j^{-1}$, $H=i_*$ and $L=j_!$ for the ordinary module functors for these ring sheaves. They satisfy the exact sequence, adjunctions, exactness and support identities of [lem-weil-pbc-proetale-ringed-open-closed]. By [lem-weil-pbc-proetale-immersion-limit-preservation], $I,J$ are exact and preserve countable products. On derived categories these products are represented termwise by [lem-weil-derived-limit-existence], since products of pro-etale module sheaves are exact [lem-weil-proetale-countable-products-exact]. Consequently $I,J$ carry a Roos triangle to a Roos triangle by [lem-pc-homotopy-limit-map]. Applied to the reduction tower of an integral $K$, this identifies $IK,JK$ with the completed pullbacks defined in [def-weil-derived-pullback-tensor-hom]. Indeed inverse image commutes with restriction of the module action along $R_T\to(A_n)_T$ by the compatible ring identifications, and the image tower is exactly $(\operatorname{Res}_n i_n^*K_n)_n$ or $(\operatorname{Res}_n j_n^*K_n)_n$, including its transition maps. The identifications commute with the projections and maps from $K$.

Original citations: lem-weil-pbc-profinite-coefficient-inverse-image, lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-derived-limit-existence, lem-weil-proetale-countable-products-exact, lem-pc-homotopy-limit-map, def-weil-derived-pullback-tensor-hom.

### Original step 4

Location: Existing lem-sf-ringed-open-roos-preservation, parent assembly 2.

The functor $L$ also preserves countable products. Here is the argument, rather than a new lemma. For a module $N$ on $U$, $Jj_*N=N$: in the slice-site description, restriction of $V\mapsto N(V\times_X U)$ back to $U$ evaluates $N$ on the same objects. Apply the ringed sheaf sequence to $j_*N$ to get $LN=\ker(j_*N\to HIj_*N)$. Both $j_*$ and $H$ preserve products as right adjoints (the adjunction and the universal property of a product give $\operatorname{Hom}(Q,R\prod N_a)=\prod_a\operatorname{Hom}(Q,RN_a)$); $I$ preserves products by [lem-weil-pbc-proetale-immersion-limit-preservation]. Taking the kernel of the product diagram gives the product of the kernels. Thus $L\prod N_a=\prod LN_a$. This is the proof of Stacks Tag 09BP, label lemma-j-shriek-limits, from the cited sheaf sequence and limit preservation. Exactness of $L$ and the termwise description of derived products now let [lem-pc-homotopy-limit-map] apply to $L$ too.

Original citations: lem-weil-pbc-proetale-ringed-open-closed, def-weil-proetale-inverse-image, lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-derived-limit-existence, lem-weil-proetale-countable-products-exact, lem-sf-exact-functor-derived-triangulated, lem-pc-homotopy-limit-map.

### Original step 5

Location: Existing lem-sf-open-semilinear-tensor-model and integral-open-reduction-comparison, parent assembly 2.

The ordinary $L$ commutes with derived reduction, including quotient transitions. To check it explicitly, take a K-flat representative $P$ of $N$ using [lem-pc-kflat-resolution]. The tensor isomorphism [lem-weil-pbc-ringed-slice-extension-tensor] extends to total tensor complexes: $F\otimes LP=L(JF\otimes P)$, since $L$ preserves direct sums as a left adjoint [lem-weil-pbc-left-adjoint-preserves-colimits]. If $F$ is acyclic, then $JF$ is acyclic; K-flatness of $P$ and exactness of $L$ show $LP$ is K-flat by [def-pc-kflat-complex]. Hence $(LN)\otimes^L_{R_X}(A_n)_X$ is represented by $(LP)\otimes_{R_X}(A_n)_X=L(P\otimes_{R_U}(A_n)_U)$, which is $L_n(N\otimes^L_{R_U}(A_n)_U)$. On underlying module presheaves changing the scalar action and extending by zero commute: on objects factoring through $U$ both are the same module with the same action, and on the other objects both are zero; the same universal property of module sheafification gives the sheaf comparison. This identifies the displayed right side with the finite-coefficient extension $L_n$. Every comparison is tensor balancing and respects $A_{n+1}\to A_n$, so these are comparisons of towers, not merely separate isomorphisms.

Original citations: lem-pc-kflat-resolution, def-pc-kflat-complex, lem-weil-pbc-ringed-slice-extension-tensor, lem-weil-pbc-left-adjoint-preserves-colimits, lem-weil-pbc-proetale-ringed-open-closed, def-weil-extension-by-zero-presheaf, def-weil-presheaf-modules-sheafification.

### Original step 6

Location: Existing open comparison/quotient-completeness nodes and direct-image-limits; finite-immersion new node supplies closed partitions, parent assembly 2-3.

For integral $N$, steps 4--5 carry its defining Roos triangle to one for $LN$ with its actual finite reductions and their maps from $LN$. Thus $LN$ is derived complete by [def-weil-derived-complete]. Its reductions are the finite extensions $L_nN_n$, whose constructibility and common cohomological interval follow from step 1. Hence $LN\in D^b_c(X,\mathcal O_E)$ by [def-weil-derived-complete-integral-detailed], and $LN=R\varprojlim_n\operatorname{Res}_nL_nN_n$ is exactly the integral $Rj_!N$ of [def-weil-integral-rational-qbar-compact-support], using the compactification $U\xrightarrow{j}X\xrightarrow{\mathrm{id}}X$. For integral $M$ on $Z$, apply [prop-weil-pbc-direct-image-limits] to its reduction tower and the closed direct image. Its tower comparison identifies ordinary $Ri_*M$ with the derived limit of the finite direct images; its completeness clause makes this object derived complete; and its projection-formula clause identifies each reduction with $Ri_{*,n}M_n$, compatibly with $A_{n+1}\to A_n$. Since $i_*$ is exact, ordinary $Ri_*$ is $H$ applied termwise. Step 1 gives a common interval for its reductions, so $HM$ belongs to the integral constructible category and agrees with [def-weil-derived-direct-image]. The integral pullbacks preserve the constructible category and have the asserted reductions by [lem-pur-integral-operations-preserve-constructible].

Original citations: def-weil-derived-complete, def-weil-derived-complete-integral-detailed, def-weil-integral-rational-qbar-compact-support, prop-weil-pbc-direct-image-limits, def-weil-derived-direct-image, lem-weil-pbc-exact-functor-derived-functor, lem-pur-integral-operations-preserve-constructible.

### Original step 7

Location: Parent assembly 3, with existing short-exact-complex, integral triangulated and derived-adjunction/normalization nodes.

For a representative complex $B^\bullet$ of the integral $K$, the ringed localization sequence in each degree gives $0\to LJB^q\to B^q\to HIB^q\to0$. Naturality of the counit and unit makes these maps commute with $d^q$, so this is a short exact sequence of complexes. Apply [lem-weil-pbc-complex-ses-triangle]. Steps 3 and 6 identify all three vertices with $j_!j^*K,K,Ri_*i^*K$ in $D^b_c(X,\mathcal O_E)$. This category has the induced triangles by [lem-weil-integral-constructible-triangulated]. The maps are the ordinary open counit and closed unit. The open exact adjunction descends to the derived categories by [lem-sc-derived-adjunction-from-underived], since exact functors are their absolute derived functors by [lem-weil-pbc-exact-functor-derived-functor]; the closed derived adjunction is [def-weil-pbc-proetale-operations]. The preceding tower identifications are induced by the same sheaf maps, so this is also the pair of maps for the completed operations. In particular the reductions of these maps are the finite maps; their compatibility with units and counits is also stated in [lem-fix-operation-reduction].

Original citations: lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-complex-ses-triangle, lem-weil-integral-constructible-triangulated, lem-sc-derived-adjunction-from-underived, lem-weil-pbc-exact-functor-derived-functor, def-weil-pbc-proetale-operations, lem-fix-operation-reduction.

### Original step 8

Location: Parent assembly 4 via exact adjunction and support identity.

At both finite and integral stages the stronger cross-object vanishing holds: for any $N\in D^b_c(U,\Lambda)$, $M\in D^b_c(Z,\Lambda)$ and $m\in\mathbf Z$, $\operatorname{Hom}(j_!N[m],i_*M)=\operatorname{Hom}(N[m],j^*i_*M)=0$. The adjunction comes from the exact ringed sheaf adjunction by [lem-sc-derived-adjunction-from-underived] and [lem-weil-pbc-exact-functor-derived-functor], and $j^*i_*=0$ is the exact support identity of [lem-weil-pbc-proetale-ringed-open-closed], applied termwise. At integral coefficients steps 3 and 6 justify using these ordinary operations for the completed symbols. Taking $N=j^*K$ and $M=i^*K$ gives the required vanishing.

Original citations: lem-weil-pbc-proetale-ringed-open-closed, lem-sc-derived-adjunction-from-underived, lem-weil-pbc-exact-functor-derived-functor.

### Original step 9

Location: Existing lem-weil-pbc-triangle-morphism-extension (2),(3), parent assembly 4.

Here is the uniqueness and naturality argument used at every stage below. Write $A_K=j_!j^*K$ and $C_K=i_*i^*K$, and assume the cross-object vanishing of step 8. For two completions of the same pair $A_K\to K\to C_K$, TR3 in [def-weil-triangulated-category] supplies $(1,1,h)$ between their triangles. The second square gives $(h-1)v=0$. By [lem-weil-pbc-hom-out-of-triangle-exact](ii), $h-1=t\delta$ for some $t:A_K[1]\to C_K$. Vanishing gives $t=0$, hence $h=1$; the third square then says the connecting maps coincide. For $f:K\to K'$, TR3 applied to $(j_!j^*f,f)$ produces a third component $h$. Naturality of the closed unit implies $(h-i_*i^*f)v=0$. The same factorization gives a map $A_K[1]\to C_{K'}$, zero by cross-object vanishing, so $h=i_*i^*f$. The third square is exactly naturality of the connecting arrow. This corrects the imported phrase 'hence through a zero map': it is $t$ that is zero, and $\delta:C_K\to A_K[1]$ need not be zero.

Original citations: def-weil-triangulated-category, lem-weil-pbc-hom-out-of-triangle-exact.

### Original step 10

Location: New rational-localization node, parent assembly 5.

For $\Lambda=E$, [def-weil-rationalization-karoubi] uses raw scalar localization with the same objects and Hom groups $\operatorname{Hom}_{\mathcal O_E}(-,-)\otimes_{\mathcal O_E}E$, and its localization functor is exact. The operations and maps are the rationalized integral ones; [prop-weil-pbc-rational-transport] extends exact linear functors and their transformations, and [lem-fix-operation-reduction] includes the compatibility of these operations, units and counits with rationalization. Applying localization to the integral triangle gives the required triangle. Every cross-object Hom group of step 8 becomes $0\otimes_{\mathcal O_E}E=0$. Step 9 proves uniqueness and naturality also for arbitrary rational morphisms, which need not be integral morphisms.

Original citations: def-weil-rationalization-karoubi, prop-weil-pbc-rational-transport, lem-fix-operation-reduction.

### Original step 11

Location: New common-stage node, parent assembly 5, including different original field stages.

The schemes $X,U,Z$ are Noetherian by step 1 and finite-dimensional by [lem-kun-dimension-finite-type], applied to their finite-type structure morphisms over $k$; the coefficient datum has $\ell\ne p=\operatorname{char}k$, so $\ell$ is invertible on all three. These verify the scheme hypotheses of the scalar-extension theorem. For $\Lambda=\Qlb$, choose a finite stage $(E,K)$ as in [def-weil-algebraically-closed-coefficients]. Scalar extension is exact with the coherent comparisons of [prop-weil-pbc-scalar-extension]; compatibility for compact support as well as pullback and direct image, including units and counits, is [lem-fix-operation-reduction]. Consequently [prop-weil-pbc-descent-functors] descends the four functors and the two transformations, with the same interpretation of compact support as [def-weil-integral-rational-qbar-compact-support]. The $E$-triangle maps to a distinguished triangle, because finite-stage inclusions are exact [thm-weil-pbc-verdier-axioms]. For possibly different finite stages $N,M$, represent both over a common extension $L$. At every further stage the group $\operatorname{Hom}(j_!N_L[m],i_*M_L)$ is zero by step 10. The common-stage Hom formula in [def-weil-algebraically-closed-coefficients] is a filtered colimit of these zero groups, and is zero. Step 9 again proves uniqueness and functoriality, now for every common-stage morphism.

Original citations: lem-kun-dimension-finite-type, def-weil-algebraically-closed-coefficients, prop-weil-pbc-scalar-extension, lem-fix-operation-reduction, prop-weil-pbc-descent-functors, def-weil-integral-rational-qbar-compact-support, thm-weil-pbc-verdier-axioms.

### Original step 12

Location: New automorphism-constructible-stage-equivalence, parent assembly 6.

Finally let $g_X,g_U,g_Z$ be the geometric Frobenius automorphisms of [def-weil-frobenius-detailed]. Because $i,j$ and the schemes are defined over $k_0$, these automorphisms commute with the immersions. They may be semilinear over $k$, so we use [def-weil-proetale-inverse-image] directly: pullback along each $g_T$ and $g_T^{-1}$ gives inverse equivalences of pro-etale sites preserving covering families. The coefficient identifications of [lem-weil-pbc-profinite-coefficient-inverse-image] respect composites and finite projections. Hence the induced module pullbacks are inverse exact equivalences; they preserve finite constructibility partitions and the Roos triangles for completeness, and therefore induce the Frobenius pullbacks $F_T=g_T^*$ on all four coefficient categories.

Original citations: def-weil-frobenius-detailed, def-weil-proetale-inverse-image, lem-weil-pbc-profinite-coefficient-inverse-image.

### Original step 13

Location: New automorphism node for b,d and new explicit-mate node for a,c, parent assembly 6-7.

Composition of these base-change functors gives $b:F_Uj^*\cong j^*F_X$ and $d:F_Zi^*\cong i^*F_X$. Define $c:F_Xi_*\cong i_*F_Z$ as the right-adjoint mate of $d^{-1}:i^*F_X\cong F_Zi^*$, and define $a:F_Xj_!\cong j_!F_U$ as the inverse of the left-adjoint conjugate $j_!F_U\to F_Xj_!$ of $b$. The vertical functors are equivalences, so [lem-weil-mate-iso-along-equivalences] makes the right-adjoint mate an isomorphism; applying the same result to opposite adjunctions makes the left-adjoint conjugate an isomorphism. These constructions are made first on module sheaves and then termwise on complexes and through the completed, rational and common-stage models of steps 3--7 and 10--11; no $k$-linearity of $g_T$ is used.

Original citations: def-weil-proetale-inverse-image, lem-weil-mate-iso-along-equivalences.

### Original step 14

Location: New explicit-mate node, including both actual equations in its statement, parent assembly 7.

The mate formulas are compatible with the units and counits. The unit and counit identities in [lem-pur-mate-unit-compatibility] and [lem-amb-mate-unit-counit], together with the pasting and identity laws of [lem-weil-pbc-mate-pasting], give componentwise
$$F_X\varepsilon_K=\varepsilon_{F_XK}\circ j_!(b_K)\circ a_{j^*K},\qquad i_*(d_K)\circ c_{i^*K}\circ F_X\eta_K=\eta_{F_XK}.$$
Thus these are the actual mate equations, rather than an appeal to a $k$-linear exchange theorem.

Original citations: lem-pur-mate-unit-compatibility, lem-amb-mate-unit-counit, lem-weil-pbc-mate-pasting.

### Original step 15

Location: New explicit-mate node, including both theta formulas and both squares in its statement; exact image triangle in parent assembly 7.

If $\theta:F_XK\xrightarrow{\sim}K$ is the Weil structure of [def-weil-weil-sheaf-complex], define structures on the outer terms by
$$\theta_A=j_!j^*(\theta)\circ j_!(b_K)\circ a_{j^*K},\qquad \theta_C=i_*i^*(\theta)\circ i_*(d_K)\circ c_{i^*K}.$$
The two mate equations of step 14 and naturality of the unit and counit give $\varepsilon_K\theta_A=\theta F_X\varepsilon_K$ and $\eta_K\theta=\theta_CF_X\eta_K$. Since $F_X$ is an exact equivalence, it transports the distinguished triangle to a distinguished triangle with these same first two arrows under $\theta_A,\theta,\theta_C$, using the stagewise triangulation supplied by [thm-weil-pbc-verdier-axioms].

Original citations: def-weil-weil-sheaf-complex, thm-weil-pbc-verdier-axioms.

### Original step 16

Location: Explicit third-square argument and formula in parent assembly 7, using triangle-morphism extension (2) and cross-object vanishing.

Apply the uniqueness argument of step 9 to the original triangle and the transported triangle: the first two squares already commute, and the factorization through the connecting morphism is killed by the cross-object Hom vanishing. Equivalently, the uniqueness calculation using [def-weil-triangulated-category] and [lem-weil-pbc-hom-out-of-triangle-exact] forces the third square
$$\delta_K\theta_C=\theta_A[1]F_X(\delta_K),$$
with the canonical shift comparison. Therefore all three arrows are Weil-equivariant in the category of pairs; no triangulated structure on that category is asserted.

Original citations: def-weil-triangulated-category, lem-weil-pbc-hom-out-of-triangle-exact.

