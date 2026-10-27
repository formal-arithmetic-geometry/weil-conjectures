# Q08 repair report

## Files written

- lem-sf-finite-immersion-constructibility-interval: split; statement unchanged; five-step assembly.
- lem-sf-cartesian-stratum-module-restriction: statement, unsplit; no Mathlib match.
- lem-sf-closed-partition-module-test: statement, unsplit; no Mathlib match.
- citations.json: full verbatim statements for all assembly citations.

## Attachments

None. The source project's constructible-sheaf pullback is on the small etale site, and ClosedImmersionStages gives adjunction units rather than the partitions and interval clauses. The full Sheaf.Paper.FiniteImmersionConstructibilityInterval theorem has sorry.

## Wanted

None. All sources used are present.

## Return repaired

The empty retained sandbox contained only dispatcher markers; the current read-only repository held the returned seven-step version. Copied that version and retained every metadata field and recorded prior item search. Its statement is unchanged. Added two smaller independently usable statements, with no proof steps or proof dependencies, after whole-DAG, blueprint and Lean searches. The assembly is below 3000 characters. The original proof is preserved below, assigned explicitly to the new tasks or the retained assembly. These are mathematical intermediate comparisons and a general partition test, not renamed conclusions of the parent. No SGA source is used.

## Review by Q08

I read the finite-stage and integral-stage paragraphs of main-20261015 prop-sf-open-closed-triangle-all-stages, the unit sk-prop-sf-open-closed-triangle, and the current item and Lean theorem. The blueprint suppresses these partition details; this remains an agent expansion along its finite-stage route. I read Stacks proetale.tex lemma-closed-immersion (09AA) and lemma-closed-immersion-complement-retrocompact-exact (09BM): closed exactness requires retrocompact complement, while the counit does not require a reduced closed subscheme. I read sites-modules.tex lemma-pullback-locally-constant (093R), schemes.tex lemma-composition-immersion (02V0), and derived.tex lemma-right-derived-exact-functor (015F). New node 1 isolates coefficient-compatible composition in a cartesian stratum square and its finite-local-constancy consequence; node 2 isolates the ambient topology and restriction test for a supplied P and N. The old paragraphs below specify their complete intended arguments rather than leaving them lost in a shorter parent.

For assembly step 1 I opened all four cited node statements: the new partition-test node supplies retrocompactness and quasi-compactness; the constant-ring-map node supplies exactly the canonical invertible coefficient map; the immersion-limit node explicitly gives exact module inverse image after transport across this isomorphism; the ringed-open-closed node explicitly supplies exact i_*, its counit and zero restriction, with the now verified complement hypothesis. For step 2, the stratification node gives actual fibre products and their disjoint covering images, the constructible-preimage node gives constructibility of those subsets, and the new cartesian module node gives A-linearity and both finite-local conditions. For step 3 the new partition-test node takes precisely the two identifications established in step 1, constructs the actual original closed-side strata and U, and makes them a constructibility witness. For step 4 I checked the two exact-functor nodes: the first supplies triangulated localization and termwise representatives on unbounded categories, and the second identifies these with both total derived functors; neither requires a bounded resolution of constructible terms. For step 5 the cited cohomology definition is explicitly kernel modulo image, support is explicitly the nonzero-degree set, and finite-torsion constructibility explicitly means bounded constructible cohomology. The exact kernel/image calculation is natural in complex maps and survives localization; additivity preserves zero. This is the only elementary step, and its argument is fully displayed.

I tested empty X, empty fibre-product strata, i the identity, i with empty source, zero coefficients and zero modules, and inverted bounds a>b. Empty partitions can retain an empty stratum to respect the positive-index constructibility convention. The new cartesian comparison asserts no unjustified factorization from an inclusion of supports; it uses an actual fibre product. Nilpotent thickenings are retained throughout; no reduction or radical ideal is introduced. A_n is a finite ring, not necessarily a field, so the finite-field-only pullback theorem is insufficient. Likewise condensed finite-presentation constructibility does not by its statement identify the intrinsic finite-geometric-stalk predicate needed here.

I checked delivery-errors B--E: new statements introduce all objects with definition dependencies, have TeX and precise source tags, have no proof sketches or proof dependencies, and searches are real msearch outputs. All parent citations are quoted verbatim in citations.json. Neither new statement refers back to the parent, so the construction does not introduce that cycle. Existing notion/composition/exactness statements are reused, and the two new nodes carry distinct multi-part intermediate arguments of comparable size. No parent proof step exceeds 2000 characters. No statement dispute was found.

## Not duplicates

- lem-sf-cartesian-stratum-module-restriction vs lem-exc-proetale-pullback-locally-constant: the existing statement does not supply the cartesian-stratum isomorphism with its two canonical coefficient paths and A-linear compatibility; finite local constancy alone is reused as input.
- lem-sf-cartesian-stratum-module-restriction vs lem-trf-finite-locally-constant-coherent: the existing statement does not supply the cartesian-stratum isomorphism with its two canonical coefficient paths and A-linear compatibility; finite local constancy alone is reused as input.
- lem-sf-cartesian-stratum-module-restriction vs lem-sfb-proetale-fp-local-models-pullback: the existing statement does not supply the cartesian-stratum isomorphism with its two canonical coefficient paths and A-linear compatibility; finite local constancy alone is reused as input.
- lem-sf-cartesian-stratum-module-restriction vs lem-sfb-adic-finite-stratification-pullback: the existing statement does not supply the cartesian-stratum isomorphism with its two canonical coefficient paths and A-linear compatibility; finite local constancy alone is reused as input.
- lem-sf-cartesian-stratum-module-restriction vs lem-sfb-finite-type-constant-module-pullback: the existing statement does not supply the cartesian-stratum isomorphism with its two canonical coefficient paths and A-linear compatibility; finite local constancy alone is reused as input.
- lem-sf-cartesian-stratum-module-restriction vs lem-sfb-normalized-local-module-pullback: the existing statement does not supply the cartesian-stratum isomorphism with its two canonical coefficient paths and A-linear compatibility; finite local constancy alone is reused as input.
- lem-sf-cartesian-stratum-module-restriction vs lem-weil-pbc-sets-etale-inverse-image-constant-sheaf: the existing statement does not supply the cartesian-stratum isomorphism with its two canonical coefficient paths and A-linear compatibility; finite local constancy alone is reused as input.
- lem-sf-cartesian-stratum-module-restriction vs new-etaleSetInverseImageConstantSheaf-existence: the existing statement does not supply the cartesian-stratum isomorphism with its two canonical coefficient paths and A-linear compatibility; finite local constancy alone is reused as input.
- lem-sf-cartesian-stratum-module-restriction vs new-etaleSetInverseImageConstantSheaf-uniqueness: the existing statement does not supply the cartesian-stratum isomorphism with its two canonical coefficient paths and A-linear compatibility; finite local constancy alone is reused as input.
- lem-sf-cartesian-stratum-module-restriction vs lem-pur-proetale-finite-local-constancy-pullback: the existing statement does not supply the cartesian-stratum isomorphism with its two canonical coefficient paths and A-linear compatibility; finite local constancy alone is reused as input.
- lem-sf-closed-partition-module-test vs lem-trf-noetherian-constructible-subset-criterion: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-sfb-locally-closed-module-extension-coherence: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-sfb-finite-stratification-wide-pullback: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-sfb-stratified-local-cohomological-bounds: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-sfb-integral-general-lfp-sequential-continuity: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-sfb-noetherian-space-compact-subsets: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-sfb-locally-closed-extension-coherence: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-weil-pbc-proper-fp-permanence: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-weil-pbc-noetherian-open-subscheme-noetherian: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-weil-pbc-basic-subset-immersion-image: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-weil-pbc-noetherian-finitely-many-components: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-weil-pbc-noetherian-scheme-closed-subsets-minimal: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-closed-partition-module-test vs lem-pur-affine-line-support-geometry: the existing statement does not construct the prescribed original closed-side schemes plus U and test an arbitrary supplied P by its two restriction identifications; general immersion/topology/extension facts alone are inputs.
- lem-sf-cartesian-stratum-module-restriction vs lem-sfb-intrinsic-finite-derived-pullback: that theorem assumes a finite field; this comparison works for any finite commutative ring, including R/t^n for n>1, and specifies canonical coefficient compatibility.
- lem-sf-cartesian-stratum-module-restriction vs lemma-constructible-pullback-stratification: that theorem constructs schemes and partitions, not coefficient-linear restriction isomorphisms or local module conditions.
- lem-sf-closed-partition-module-test vs lem-sfb-scalar-model-immersion-extension: that statement uses admissible condensed coefficient rings and scalar-model constructibility; this tests arbitrary supplied constant-ring pro-etale module sheaves with intrinsic finite geometric stalks on the actual unreduced original schemes.
- lem-sf-cartesian-stratum-module-restriction vs lem-weil-pbc-module-constructible-pullback: that theorem uses condensed internal finite-presentation local models; it does not assert this canonical cartesian comparison for intrinsic constant modules and their finite geometric stalk predicate.

## Search assessment

The first new node used two LeanFinder phrasings, LeanSearch, Loogle and grep; the second used the same three kinds and a second semantic phrasing. Read all hits. pullbackRestrictIsoRestrict in Mathlib/AlgebraicGeometry/Restrict.lean:553 is an isomorphism of schemes for an open restriction, not module inverse image on pro-etale sites. IsImmersion.instOfIsClosedImmersion supplies only an immersion instance; the remaining hits concern locally constant functions, Zariski tilde sheaves and generic pullback diagrams. Neither full intermediate statement is a one-line specialization. Whole-blueprint searches included constructible, pullback stratification, stratification, 093R, 09AA, local model and closed stratum; the nearest imported ancestor is prop-sf-open-closed-triangle-all-stages. Tags and related keywords were searched throughout dag/nodes, and the relevant finite-field, condensed-coefficient, finite-local-constancy and immersion nodes were opened. Existing general inputs are not recreated.

## Retained full arguments and task allocation

### Original step 1

Allocation: New node 2: retrocompactness and Noetherian topology; assembly 1 uses its explicit conclusion.

First check the quasi-compact-complement hypothesis. Every open subscheme of the Noetherian scheme $X$ is Noetherian, hence quasi-compact, by [lem-weil-pbc-noetherian-open-subscheme-noetherian]. For any affine open $W\subseteq X$, the open subscheme $U\cap W$ is therefore quasi-compact. This is precisely quasi-compactness of $j$. The same argument shows that every open subset $V\subseteq X$ is retrocompact: its intersection with any quasi-compact open is again an open subscheme of $X$, hence quasi-compact. Thus, if $C$ is closed in $X$ and $V$ is open, then $V\cap C=V\setminus(X\setminus C)$ is constructible by the definition in [def-weil-constructible-subset].

Dependencies: lem-weil-pbc-noetherian-open-subscheme-noetherian, def-weil-constructible-subset

### Original step 2

Allocation: Assembly 1: exactness, coefficient transport, counit and zero restriction, using existing nodes.

Put $A=A_n$. The canonical coefficient maps $g^{-1}A_X\to A_Y$ for $g=i,j$ are ring-sheaf isomorphisms by [prop-weil-pbc-proetale-constant-ring-map]. Hence the module inverse images are ordinary inverse images with their transported $A$-actions, and are exact by [lem-weil-pbc-proetale-immersion-limit-preservation]. The hypotheses of [lem-weil-pbc-proetale-ringed-open-closed] now hold, since step 1 supplied quasi-compactness of the complement. Its statement gives exactness of $i_*$ and the identities $i^{-1}i_*\cong\operatorname{id}$ and $j^{-1}i_*=0$. These assertions concern all module sheaves and do not assume constructibility.

Dependencies: prop-weil-pbc-proetale-constant-ring-map, lem-weil-pbc-proetale-immersion-limit-preservation, lem-weil-pbc-proetale-ringed-open-closed

### Original step 3

Allocation: New node 1: cartesian coefficient-linear comparison and finite-local-constancy passage; assembly 2 retains the existing geometric partition and constructible-preimage applications.

Let $M$ be a constructible $A_X$-module sheaf and let $(s_\nu:S_\nu\to X)$ be its given witnessing partition. For $g:Y\to X$ equal to $i$ or $j$, form the actual fibre products $S'_\nu=S_\nu\times_XY$, with projections $s'_\nu:S'_\nu\to Y$ and $g_\nu:S'_\nu\to S_\nu$. By [lemma-constructible-pullback-stratification], these immersions give a finite disjoint locally closed partition of $Y$ with images $g^{-1}(|S_\nu|)$. Each image is constructible by [lem-pur-scheme-constructible-preimage]. The inverse-image composition comparisons of [lem-weil-pbc-left-exact-site-inverse-image-tensor], applied to $g\circ s'_\nu=s_\nu\circ g_\nu$, identify $(s'_\nu)^{-1}g^{-1}M$ with $g_\nu^{-1}s_\nu^{-1}M$. For the coefficient identifications, both composition paths take each constant section $a\in A$ to that same section; uniqueness of maps from a constant sheaf equates the two ring maps. Naturality of the product-preserving comparison for the action map $A\times M\to M$ then proves that the displayed comparison is $A$-linear. By [def-weil-finite-torsion-constructibility] (through [def-weil-proetale-constructible-sheaf]), $s_\nu^{-1}M$ is a locally constant $A$-module sheaf with finite stalks at every geometric point of $S_\nu$; hence, by [lem-pur-proetale-finite-local-constancy-pullback] applied to $b=g_\nu$, so is $g_\nu^{-1}s_\nu^{-1}M$, and therefore so is the isomorphic sheaf $(s'_\nu)^{-1}g^{-1}M$. Thus these exact fibre-product partitions witness constructibility of $i^{-1}M$ and $j^{-1}M$. Empty pieces can be removed from a finite partition.

Dependencies: lemma-constructible-pullback-stratification, lem-pur-scheme-constructible-preimage, lem-weil-pbc-left-exact-site-inverse-image-tensor, lem-pur-proetale-finite-local-constancy-pullback, def-weil-finite-torsion-constructibility, def-weil-proetale-constructible-sheaf

### Original step 4

Allocation: New node 2: original ambient partition geometry and no reduction.

Let $N$ be constructible on $Z$, witnessed by immersions $t_\mu:T_\mu\to Z$. By the immersion-composition clause (e) of [lem-weil-pbc-proper-fp-permanence], $i\circ t_\mu:T_\mu\to X$ are immersions. Their images, together with $U$, are disjoint and cover $X$ because $i$ is a homeomorphism onto the closed complement of $U$. These images are locally closed in $X$: writing $|T_\mu|=V\cap D$ with $V$ open in $Z$ and $D$ closed in $Z$, choose an open $V'\subseteq X$ with $i(V)=i(Z)\cap V'$; the closed embedding makes $i(D)$ closed in $X$, and $i(|T_\mu|)=V'\cap i(D)$. This uses only the definitions [def-weil-closed-immersion], [def-weil-locally-closed-subset]. Step 1 shows that these locally closed images and the open $U$ are constructible. Thus we have the required finite partition on $X$, using the original schemes $T_\mu$ without replacing them by reductions.

Dependencies: lem-weil-pbc-proper-fp-permanence, def-weil-closed-immersion, def-weil-locally-closed-subset

### Original step 5

Allocation: New node 2: general supplied-restriction test; assembly 3 substitutes P=i_*N using assembly 1.

Restrict $i_*N$ to the strata just constructed. The composition comparisons of [lem-weil-pbc-left-exact-site-inverse-image-tensor] identify $(i\circ t_\mu)^{-1}i_*N$ with $t_\mu^{-1}i^{-1}i_*N$. The counit isomorphism of [lem-weil-pbc-proetale-ringed-open-closed] therefore identifies this with $t_\mu^{-1}N$, which is locally constant with finite stalks at every geometric point by the choice of the partition [def-weil-proetale-constructible-sheaf]; isomorphic module sheaves have isomorphic restrictions to a covering and isomorphic stalks, so $(i\circ t_\mu)^{-1}i_*N$ is locally constant with finite stalks. On $U$, the other identity $j^{-1}i_*=0$ of that same node gives zero; the zero sheaf is the constant sheaf of the zero $A$-module, with zero stalks. This proves constructibility of $i_*N$ on exactly the asserted partition. Neither the counit identity nor the argument imposes reducedness on $Z$.

Dependencies: lem-weil-pbc-left-exact-site-inverse-image-tensor, lem-weil-pbc-proetale-ringed-open-closed, def-weil-proetale-constructible-sheaf

### Original step 6

Allocation: Assembly 4: existing unbounded exact-derived factorization and identification.

Apply [lem-weil-pbc-exact-functor-derived-factorization] to each of the three exact functors of step 2, between the ambient abelian module-sheaf categories. It gives a triangulated functor on the unbounded derived categories, represented by applying that functor termwise to any representing cochain complex. By [lem-weil-pbc-exact-functor-derived-functor], this termwise functor is also its total derived functor: in particular the ordinary closed direct image computes $Ri_*$, and the exact inverse images compute $i^*$ and $j^*$. No resolution or bounded complex of constructible terms is assumed.

Dependencies: lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-exact-functor-derived-functor

### Original step 7

Allocation: Assembly 5: natural kernel/image cohomology, localization, identical intervals and bounded-constructible restriction.

For any representing complex $C^\bullet$ and any of the three functors $F$, exactness preserves kernels, images and cokernels. Consequently the cohomology formula of [def-weil-derived-cohomology-sheaves] gives the natural isomorphism $\mathcal H^r(FC)=\ker(Fd^r)/\operatorname{im}(Fd^{r-1})\cong F(\ker d^r/\operatorname{im}d^{r-1})=F\mathcal H^r(C)$. It descends to the derived categories because step 6 supplies the termwise representative and quasi-isomorphisms induce the stated cohomology isomorphisms. If $\mathcal H^r(C)=0$ outside $[a,b]$, the right side is zero there since an additive functor takes zero to zero. This is preservation of the same interval by [def-weil-cohomological-support], including the zero complex when $a>b$. Finally, when $C\in D^b_c$, its finitely many nonzero cohomology sheaves are constructible by [def-weil-finite-torsion-constructibility]; steps 3 and 5 make their images constructible, while the same-interval argument keeps them bounded. Hence the ambient triangulated functors of step 6 restrict to the asserted bounded constructible categories.

Dependencies: def-weil-derived-cohomology-sheaves, def-weil-cohomological-support, def-weil-finite-torsion-constructibility

## Unfinished work

The two new nodes are deliberately statement-only tasks for parallel future workers. No requested stage-1 assembly argument is omitted.
