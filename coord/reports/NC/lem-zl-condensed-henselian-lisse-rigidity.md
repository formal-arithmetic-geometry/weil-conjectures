# Worker report

1. Files written

- dag/nodes/sec-zeta-weil/lem-zl-condensed-henselian-lisse-rigidity.json: item, split, unchanged statement; short assembly.
- dag/nodes/sec-zeta-weil/lem-zl-component-lift-base-change.json: new statement, unsplit; no Mathlib match.
- dag/nodes/sec-zeta-weil/lem-zl-component-derived-pullback-square.json: new statement, unsplit; no Mathlib match.
- citations.json: verbatim statement evidence for every step citation.

2. Attachments: none. The matching project theorem in Sheaf/AlgebraicGeometry/CondensedHenselianLisseRigidity.lean ends in `by sorry`; WeilConjectures contains no finished exact statement.

3. WANTED: none.

4. The released repair requires spreading the old proof into independent work. The sandbox initially contained only dispatcher markers, no node or report or search log; the required initial dry run exited with “no node files”. I continued the current live node, retaining all its metadata, statement and statement dependencies. The pre-existing topology argument of old Step 2 now has an exact reusable node, lem-sfb-spectral-clopen-component-homeomorphism, so creating another would violate duplicate rules. The two new tasks split the old component-square argument into geometric and derived module comparisons, neither a henselian rigidity assertion nor a clause restating the item. The original idempotent, w-strict locality, evaluation-equivalence and conjugation/scalar arguments remain in the parent assembly.

5. Nothing mathematical is left unfinished in the parent's assembly; the two new statements deliberately have no proof, proof dependencies or proof origin. Their proofs are work for subsequent workers. No Lean was written or compiled.

## Argument preservation and work division

The new geometric task must check each finite clopen stage and its projection normalization, extend it to arbitrary cofiltered presentations, and verify the naturality and composition laws on actual schemes. The new derived task must identify the actual inverse images induced by that test comparison, check ring-object/module linearity and the coefficient unit, and obtain the monoidal natural isomorphism on unbounded derived categories by termwise exact pullback and localization. These are separate arguments of comparable scope. The remaining old arguments are either the exact existing topology theorem or the explicit short assembly below. No long argument has been silently deleted.

Disposition of the six original steps:

- Old 1: retained verbatim as assembly Step 1, idempotent lifting plus D(e).
- Old 2: cite the exact existing spectral clopen criterion; its clopen descent, separation, compact-image surjectivity and compact-to-Hausdorff argument are preserved by that node. No duplicate new topology node.
- Old 3: retained verbatim as assembly Step 3, existing w-strict invariance plus homeomorphism invariance of extremal disconnectedness.
- Old 4: retained verbatim as assembly Step 4, apply the two existing component evaluations and actual scheme pullback.
- Old 5: finite subdivisions and inverse limits are the geometric new node; its induced actual coefficient-compatible inverse-image isomorphism is the derived new node.
- Old 6: retained verbatim as assembly Step 6, inverse relabelling, conjugation, morphism bijections and scalar compatibility.

For the next workers, the full pre-repair arguments follow verbatim:

### Original step 1

Apply the henselian-pair definition [def-weil-pbc-henselian-terminology] to the finite $A$-algebra $A$ itself. It gives a bijection $\operatorname{Idem}(A)\to\operatorname{Idem}(A/I)$. Under [lem-weil-pbc-spec-clopen-idempotent], the clopen corresponding to $e$ is $D(e)$, and $i^{-1}D(e)=D(\overline e)$. Thus inverse image is a bijection between the clopens of $T$ and those of $Z$.

Cited nodes: def-weil-pbc-henselian-terminology, lem-weil-pbc-spec-clopen-idempotent.

### Original step 2

Put $P=\pi_0(T)$, $Q=\pi_0(Z)$ and $h=\pi_0(i):Q\to P$. By [sk-def-pe-wlocal] the underlying spaces of these affine schemes are spectral; [lem-pe-spectral-components-profinite] makes $P,Q$ compact Hausdorff. Every clopen of a space is a union of components, and hence descends to a clopen of its component quotient. Therefore Step 1 says that $h^{-1}$ is a bijection on clopens. The formula of [lem-weil-pbc-quasicompact-components-clopen-intersection], applied to $T$ and $Z$, separates distinct components by clopens. If $q_1\ne q_2$ in $Q$, choose a separating clopen in $Q$ and lift it along $h^{-1}$; this separates $h(q_1),h(q_2)$, proving injectivity. The image $K=h(Q)$ is compact, hence closed in $P$. If $p\notin K$, for each $k\in K$ choose a clopen containing $p$ and excluding $k$. Compactness of $K$ gives finitely many whose intersection $V$ misses $K$. Then $h^{-1}V=\varnothing=h^{-1}\varnothing$, contradicting injectivity on clopens since $p\in V$. So $h$ is surjective. A continuous bijection from compact to Hausdorff is a homeomorphism: it sends closed sets to compact, thus closed, sets.

Cited nodes: sk-def-pe-wlocal, lem-pe-spectral-components-profinite, lem-weil-pbc-quasicompact-components-clopen-intersection.

### Original step 3

By [lem-zl-henselian-wstrict-local-invariance], $A$ is w-strictly local exactly when $A/I$ is. By Step 2, $P$ is extremally disconnected exactly when $Q$ is: a homeomorphism preserves open sets, their closures, and openness of those closures. The definition [sk-def-pe-wlocal] of w-contractibility is the conjunction of these two conditions, so $T$ is w-contractible if and only if $Z$ is.

Cited nodes: lem-zl-henselian-wstrict-local-invariance, sk-def-pe-wlocal.

### Original step 4

Assume these equivalent conditions. Apply [lem-zl-condensed-wcontractible-lisse-evaluation] to the two w-contractible affine schemes $T$ and $Z$. The coefficient-compatible component maps give equivalences $\pi_T^*:D_{\mathrm{lis}}(P,\Lambda)\simeq D_{\mathrm{lis}}(T,\Lambda)$ and $\pi_Z^*:D_{\mathrm{lis}}(Q,\Lambda)\simeq D_{\mathrm{lis}}(Z,\Lambda)$. Also [lem-zl-condensed-lisse-proetale-locality], for the scheme morphism $i$, gives the exact symmetric monoidal functor $i^*$, its restriction to dualizable objects, and its canonical coefficient identification.

Cited nodes: lem-zl-condensed-wcontractible-lisse-evaluation, lem-zl-condensed-lisse-proetale-locality.

### Original step 5

The square of component maps commutes with $i$ and $h$. Here this includes the maps of sites, not only the point maps: the component-site construction in [lem-zl-condensed-wcontractible-lisse-evaluation] starts with finite clopen subdivisions. A clopen $U\subseteq P$ gives the open-and-closed part $T_U\subseteq T$; pulling back gives $Z\times_TT_U=Z_{h^{-1}U}$. Thus the two composite constructions agree on every finite subdivision and on their inverse-limit construction of a profinite set over $P$. Functoriality of inverse image gives $i^*\pi_T^*\cong\pi_Z^*h^*$, compatibly with coefficients, since each coefficient ring is pulled back from the same condensed ring $\Lambda$.

Cited nodes: lem-zl-condensed-wcontractible-lisse-evaluation.

### Original step 6

Since $h$ is a homeomorphism, relabelling profinite sets over $P$ by $h$ gives an inverse to $h^*$, also on the dualizable subcategories. By Steps 4 and 5, $i^*$ is conjugate by $\pi_T^*,\pi_Z^*$ to this equivalence. Hence $i^*$ is an equivalence and in particular gives bijections on all morphism sets between dualizable objects. Finally [lem-zl-condensed-lisse-proetale-locality] identifies $i^*(\Lambda_T\otimes^L_{\underline R}\underline C)$ with $\Lambda_Z\otimes^L_{\underline R}\underline C$ for every constant discrete scalar complex $C\in D(R)$, $R=\Gamma(*,\Lambda)$; this is the required canonical scalar-extension compatibility.

Cited nodes: lem-zl-condensed-lisse-proetale-locality.

## Not duplicates

lem-zl-component-lift-base-change vs lem-zl-component-relative-profinite-site: the existing result constructs the lifts for one affine base and is functorial in the relative profinite object; the new one compares them under arbitrary changes of the affine scheme base.
lem-zl-component-lift-base-change vs lem-zl-affine-component-site-projection: the existing projection/evaluation theorem does not state the normalized base-change isomorphism or its naturality in the scheme base.
lem-zl-component-lift-base-change vs lem-sfb-component-lift-lisse-section-comparison: the existing theorem assumes two w-contractible affine schemes with identified component space and states the common-base comparison plus section consequences; the new geometric result has arbitrary affine source and target and arbitrary component map, including non-isomorphisms.
lem-zl-component-derived-pullback-square vs lem-sfb-component-lift-lisse-section-comparison: the latter gives the common-component, w-contractible case; the new statement identifies actual derived module inverse images for arbitrary affine maps, with arbitrary non-homeomorphic component map and no w-contractibility.
lem-zl-component-derived-pullback-square vs lem-zl-generic-component-site-comparison: the existing theorem has a geometric field base change and compares set-sheaf inverse images; the new statement concerns arbitrary affine maps, condensed ring/module coefficients and ordinary unbounded derived monoidal comparisons.
lem-zl-component-derived-pullback-square vs lem-zl-condensed-component-pullback-compatibility: the existing theorem compares the component pullback of one w-contractible scheme with its absolute condensed-point realization; the new theorem compares two arbitrary affine schemes along their actual morphism.
lem-zl-component-derived-pullback-square vs lem-zl-condensed-lisse-proetale-locality: locality supplies actual pullback, coefficients and scalar compatibility, not its comparison with the two component morphisms.

I searched the whole DAG statements and titles, the blueprint with blueprint_refs searches for component-site, clopen bijection, finite clopen, connected component quotient, component lift and component projection, and the source library by the item tag, henselian/lisse, and component comparison concepts. The exact topology match was reused. The two new names do not exist in the live DAG. Searches found no blueprint node stating either new result.

## Mathlib reading

All recorded queries are actual msearch.py calls, retained in searches.jsonl. Each new node has two LeanFinder phrasings, LeanSearch, valid Loogle and source grep. All services answered. The geometric search returns affine-space base-change, affine-transition-limit and open-cover comparison facts; they do not state relative component base change. I read AffineSpace.map_over and isPullback_map at lines 273 and 325. The derived search returns generic SheafOfModules.pullbackComp (PullbackContinuous.lean:167), free-module comparisons and mapDerivedCategorySingleFunctor (ExactFunctor.lean:112). These do not identify the actual component square or its coefficient-compatible monoidal derived comparison; no one-line specialization proves either new statement. No Mathlib leaves are claimed. Earlier topology queries remain logged even though that candidate was discarded as a duplicate.

## Review by NC

I read HRS construction (4.1), Proposition 4.3 and Corollary 4.4 with their proofs on printed pp. 8–10. The item is exactly the henselian pair situation of Corollary 4.4 and keeps the same coefficients and ordinary derived dualizable category. For the geometric new node, (4.1) constructs the lifts by finite clopen stages and affine-transition limits. Pullback of an open-and-closed subscheme is its inverse-image open-and-closed subscheme, including its restricted structure sheaf. At each finite stage this identifies the two diagrams, and the cone universal properties give the projection-preserving isomorphism at their limits. The specified projection equations fix the comparison and force naturality, identity and composition. This is the full geometric part of old Step 5, with no henselian or w-contractibility hypothesis needed.

For the derived new node I used the same construction, HRS Section 3 pullback paragraph and Corollary 4.4(2). The relative test comparison gives the geometric-morphism inverse-image comparison. The coefficients on both sides are pulled back from the same condensed ring; the component at that ring gives exactly the coefficient identification needed to pass to modules. Exact inverse images act termwise, preserve quasi-isomorphisms and carry the tensor comparison to ordinary derived tensor. The new node asserts these comparisons themselves, so the parent no longer labels their construction elementary. The ordinary derived category is retained throughout; nothing is replaced by completed coefficients or only by cohomology groups.

I opened every statement cited in the revised parent. Step 1 uses the henselian definition's unique finite-algebra idempotent lifting for B=A and the idempotent/clopen bijection; i inverse D(e)=D(e mod I) verifies naturality. Step 2 uses the explicit spectral-affine assertion in sk-def-pe-wlocal and the existing spectral clopen criterion, which states exactly that bijective clopen inverse image gives a component homeomorphism. Step 3 uses the two-way w-strict invariance statement and the conjunction defining w-contractibility; a homeomorphism preserves extremal disconnectedness. Step 4 uses the explicit component equivalence in the evaluation node, not only its perfect-complex clause, and the locality node's exact symmetric monoidal scheme pullback. Step 5 uses the new geometric base-change interface and its derived comparison with the displayed functor order. Step 6 uses the homeomorphism's inverse relabelling on profinite slice sites, conjugates it by the Step 4 equivalences, and uses locality's scalar-extension clause. Every use has a verbatim quote in citations.json.

I checked empty schemes and empty profinite objects, the identity morphism, a map whose component map is not surjective, disconnected finite products, I=0, the zero ring and I=A (the henselian condition forces A=0). Neither new statement assumes a component map is invertible, so they cannot be applications of the common-component special case; no connectedness or nonemptiness was inserted. The new geometric and derived tasks contain no proof sketches in their statements; their displayed equalities are theorem conclusions specifying the actual comparisons. I checked delivery-errors B1–B10, C1–C8, D1–D5 and E1–E7: no hollow definition, source by precise HRS place, no SGA, no missing non-elementary parent comparison, no source error or statement dispute. The generic topology tool use is declared in split_report; the unit and chapter route are unchanged. No parent step exceeds 2000 characters, and the total is below 3000.
