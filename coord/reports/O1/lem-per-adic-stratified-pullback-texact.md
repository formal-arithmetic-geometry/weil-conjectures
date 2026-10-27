# Worker report

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-adic-stratified-pullback-texact.json: item, unchanged statement; five assembly steps, 2236 characters.
- dag/nodes/sec-deligne-laumon-a1/lem-per-integral-pullback-bounds.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-pullback-coefficient-descent.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rational-stratum-pullback-models.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statement evidence for every assembly-step citation.

## Attachments

None. Searched the live WeilConjectures tree for the blueprint tag and adic/stratified pullback terminology. The corresponding Sheaf/Paper/AdicStratifiedPullbackInterface.lean has sorry in finiteTypeBaseGeometry, finiteTypeBasePrime, pullHeart and commonPullHeart; its interface is not a finished proof. No compiler, Lake or build was used.

## WANTED

None. Bhatt–Scholze arXiv:1309.1198 and the current blueprint were available locally.

## Repair order and allocation

The released stage-1 repair note dated 2026-10-22 explicitly reopens the previous reviewed split and requires at least two comparable new statement-only tasks and an assembly of at most 3000 characters. It overrides the usual prohibition on extracting a clause already present in an item. Three independent tasks distribute the substantial arguments, rather than merely rename the whole theorem. They have no proofs or proof dependencies; their complete inherited arguments are preserved verbatim below for the next workers.

Old step 1 stays in assembly step 1. Old steps 2–4 belong to lem-per-integral-pullback-bounds: ordinary/completed comparison, constructible witnesses, linear triangulated restriction, pulled-back perfect charts, cohomological bounds, detection and integral halves. Old steps 5–6 belong to lem-per-pullback-coefficient-descent: fraction localization, restriction of the actual scalar comparisons and their equations, pair-category action, exactness and independence of enlargement. The t-exactness consequence in old step 6 and all of old step 9 remain an application of the existing abstract coefficient-stage descent in assembly step 4; no extra node duplicates that abstract theorem. Old steps 7–8 belong to lem-per-rational-stratum-pullback-models: rational realization, immersion composition, slice normalization without noetherian chart assumptions, explicit balanced free map and inverse, degree-zero detection and degenerate cases. Assembly step 5 applies that calculation.

No statement correction, route change or new SGA source. No unresolved mathematical issue. Only the authorized sandbox was written; the source repository and launcher were read only.

## Searches and blueprint provenance

Ran tools/blueprint_refs.py ancestor for the item: nearest ancestor lem-per-smooth-pullback-t-exact. New via lists prepend the item to its existing via list. Searched the entire imported blueprint for completed pullback, coefficient-stage, stratified pullback, pullback cohomological, rational realization, continuous rational, cohomological interval and finite free; searched DAG statements by the same ideas and the existing Bhatt–Scholze place 6.8.15. No blueprint node states any of the three tasks with all the specified comparisons and hypotheses. The first paragraph of the main-20261015 ancestor proof asserts ordinary exactness and pullback of cohomology; these tasks refine exactly that paragraph, without entering the smooth dimension estimate or purity part. same_as is empty.

All new nodes have leanfinder searches in two phrasings, a Loogle query, source grep and LeanSearch, with exact query text copied from searches.jsonl. Services were available. Read all hits, including AdicCompletion.map_exact, derived isLE/isGE facts, generic triangulated/localization functors, ellAdicSheaf, and SheafOfModules.pullbackObjFreeIso. Read Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean and CategoryTheory/Triangulated/TStructure/TruncLTGE.lean, and PullbackFree.lean through the free-pullback comparison at lines 114–129. The latter is only ordinary pullback of a free module; our task includes the actual completed-to-realized identification and arbitrary immersion/slice comparison before that calculation. It is not a one-line specialization. Thus all three remain unsplit and none is a Mathlib leaf.

## Not duplicates

lem-per-integral-pullback-bounds vs lem-a1-integral-stratum-chart-restrictions: the existing statement gives exact chart models and restriction comparisons; the new task assembles their global preservation of arbitrary ambient cohomological intervals and integral halves using detection.
lem-per-integral-pullback-bounds vs lem-a1-completed-perfect-scalar-pullback: the existing statement calculates one bounded scalar model; the new task passes from all strata to an arbitrary integral constructible object globally.
lem-per-integral-pullback-bounds vs lem-tw-ordinary-completed-integral-pullback: the existing statement proves constructible preservation and specified unit; the new task adds cohomological bounds, actual triangulated restriction and integral halves.
lem-per-integral-pullback-bounds vs lem-per-rational-realization-pullback-comparison: the existing statement supplies the unit and rational realization comparison, but does not state preservation of integral cohomological intervals.
lem-per-pullback-coefficient-descent vs lem-a1-texact-coefficient-stage-descent: the existing abstract theorem assumes exact comparison data and integral half preservation; the new task constructs the normalized comparisons and arrow action for the actual completed-pullback system. It does not duplicate the abstract t-exactness conclusion.
lem-per-pullback-coefficient-descent vs prop-weil-pbc-scalar-extension: the latter is an ambient comparison package conditional on constructible preservation; the new task restricts it, rationalizes it and produces the completed-pullback functor on the pair category.
lem-per-rational-stratum-pullback-models vs lem-per-continuous-rational-derived-realization: the latter supplies realization and ambient pullback; the new task assembles restriction to a chosen stratum, arbitrary trivializing slices, balanced free map and degree-zero detection for the realized completed pullback.
lem-per-rational-stratum-pullback-models vs lem-per-continuous-coefficient-slice-normalization: the latter is coefficient and slice normalization, not the stratified free calculation of a completed rational pullback.
lem-per-rational-stratum-pullback-models vs lem-tw-ordinary-pullback-stratified-models: that statement concerns ordinary integral perfect models, before completion and rational realization; the new task is the continuous rational realized finite free formula with actual quotient-normalized comparisons.
lem-per-integral-pullback-bounds vs lem-a1-constructible-pullback-t-exact: that statement is rational/common-stage over the fixed algebraic closure of a finite field, not integral ambient bounds over arbitrary noetherian finite-dimensional schemes.

## Review by O1

I read the repair note and the complete current nine-step proof, chapter and unit records, and the main-20261015 ancestor proof. I read Bhatt–Scholze Lemma 6.5.9(4)–(5), Remark 6.5.10, Proposition 6.6.11 and its proof, Lemma 6.8.2, Definitions 6.8.6/6.8.8, Proposition 6.8.14 and Remark 6.8.15. The first new task follows the completed pullback and stratified perfect route of 6.5.9 and 6.6.11; the second is the normalization and pair-category implementation of 6.8.14–6.8.15; the third is the ringed tensor formula of 6.8.15 after the continuous coefficient and constructible definitions. These are agent syntheses of those passages and the existing nodes, not claims that the paper literally states every normalized equation.

For assembly step 1 I opened lem-weil-pbc-finite-type-over-noetherian and lem-fin-finite-type-fibre-dimension-bound: their statements respectively give noetherianity of a finite-type source and a uniform bound on the fibres over a quasi-compact base. Applying to Spec k gives the needed noetherianity and dimension for both schemes, and invertibility of ell passes to local rings. No smoothness or flatness is inferred.

For assembly step 2 I opened the new integral-bounds statement: it supplies every property used there including the actual gamma unit, finite witnesses, A_E-linearity, inherited triangles, intervals and integral halves. The inherited argument uses the integral characterization to match categories, rational-realization-pullback-comparison for the specified gamma, cbc-completed-pullback-triangles for shifts/triangles, and integral-stratum-chart-restrictions for linearity and restriction to pulled-back charts. I opened all these statements and completed-perfect-scalar-pullback, noetherian-stratum-detection and integral-tstructure. The perfect calculation explicitly states interval preservation without coefficient flatness; the detection statement applies to each ambient cohomology sheaf after exact restrictions. The scheme hypotheses hold on X,Y; arbitrary chart schemes require none in the scalar-model calculation. No proof of a cited node is used in place of its statement.

For step 3 I opened the new coefficient-descent statement and checked its objects, fraction rule, orientation of beta, scalar tower equation and common-stage arrow formula. Its inherited proof uses semilinear-scalar-localization with identity A_E coefficient map, the scalar-extension package's exact ambient completed comparison, and constructible preservation from the integral task to restrict. Localization preserves equations of comparisons. The displayed tower equation has source T_{M/L,Y}T_{L/E,Y}F_E and target F_MT_{M/E,X} on both sides.

For step 4 I opened lem-a1-texact-coefficient-stage-descent, prop-weil-localized-tstructure, lem-per-adic-common-stage-truncations, def-weil-pbc-qbar-category and thm-weil-pbc-verdier-axioms. The first requires integral linear exactness and preservation of halves (step 2), and exact normalized beta data (step 3). Localized-tstructure states image halves; common-stage-truncations supplies t-exact scalar transitions, pair halves and finite truncations. The qbar definition describes common-stage triangles but does not itself prove the axioms: the Verdier theorem is therefore retained explicitly, as in the previous independent review's C4 repair. The descent theorem states exact hearts and canonical truncation/cohomology comparisons and their beta compatibility. Taking an inverse gives the user's direction of the cohomology comparison; interval preservation is intersection of shifted halves. No additional non-elementary inference was silently inserted.

For step 5 I opened the new rational-stratum-model statement and checked that it supplies the exact derived isomorphism, degree-zero conclusion and balanced chart formula it is cited for. Its inherited argument uses continuous-rational-derived-realization for J and the finite-stage comparison; ringed-derived-monoidal-comparisons for composition and tensor unit; continuous-coefficient-slice-normalization for actual restriction on arbitrary U; and noetherian-stratum-detection for the final vanishing. Those statements explicitly supply the coefficients and comparisons. S' is a fibre product, not a factorization inferred from an image. S' is noetherian finite-dimensional but U and U' may not be; the slice lemma is explicitly free of that hypothesis. The free calculation sends basis vectors to basis vectors and its written inverse checks by balancing.

I tested the three statements on g=id, empty X or Y, empty pulled strata, rank zero, a closed point immersion, and non-flat structural coefficient maps. The zero complex stays zero by additivity; both signs of the integral t-structure are obtained from a finite interval; free modules require no structural-map flatness. Finite E=L makes beta the identity and the tower equation reduces to the unit normalization. Arbitrary k remains allowed; none of the new tasks introduces algebraic closedness of k or smoothness. Each new statement introduces its objects, writes TeX once, cites its notions, carries no proof sketch or proof steps, and is a genuine allocation of a different part of the human-ordered re-split. All assembly steps are below 2000 characters and their sum is below 3000.

I corrected the initial allocation by leaving the already-existing abstract t-exactness/truncation consequence in assembly step 4 instead of creating another abstract descent node. I retained the previous review's explicit Verdier-axioms citation. I made no change to the item's statement or maintainer-owned fields. All former proof arguments are recorded verbatim in the next section, so the re-split loses no details.

## Preserved inherited arguments

The following is source material for future workers, not proof steps on the new statement-only nodes. Allocation above specifies where each argument belongs.

### Former step 1

Both $X$ and $Y$ satisfy the noetherian and finite-dimensional hypotheses of the cited adic results. Apply the finite-type noetherian theorem to their structure maps to $\operatorname{Spec}k$ (a field is noetherian). Apply the finite-type fibre dimension bound to the same maps: their unique fibres are $X$ and $Y$. The base is quasi-compact. Invertibility of $\ell$ is inherited from $k$. No smoothness, flatness or assumption that $k$ is algebraically closed is used.

Cited node statements read: lem-weil-pbc-finite-type-over-noetherian, lem-fin-finite-type-fibre-dimension-bound.

### Former step 2

Write $\mathcal C_W=D^b_c(W,A_E)$ with exactly the compatible etale-origin witnesses in the statement. The integral stratified-perfect characterization identifies this category with the detailed integral category used by the chart lemmas, with the same completed ring and reduction functors. The rational-realization pullback comparison states that ordinary ringed pullback $P_g$ preserves $\mathcal C$ and that the specified quotient-tower unit $\gamma_g:P_gK\to\widehat P_gK$ is invertible; it also retains the compatible etale witnesses. Thus the actual completed pullback restricts to $\mathcal C_X\to\mathcal C_Y$. The completed-pullback triangle theorem supplies its shift comparison and preservation of distinguished triangles. These are inherited ambient triangles, not newly chosen triangles. The functor is $A_E$-linear by the chart-restriction lemma (equivalently its scalar action on all quotient-tower maps).

Cited node statements read: lem-weil-pbc-integral-stratified-perfect-characterization, lem-per-rational-realization-pullback-comparison, lem-cbc-completed-pullback-triangles, lem-a1-integral-stratum-chart-restrictions.

### Former step 3

Fix integral $K$ with ambient cohomology supported in a finite interval $[a,b]$. The chart-restriction lemma supplies a finite locally closed stratification $S_\alpha$ and pro-etale covers $V_{\alpha t}\to S_\alpha$ on which $K$ is $C_V(P)=B_{E,V}\otimes_{\underline{A_E}}\underline{P^\bullet}$ for bounded finite-projective $A_E$-complexes $P^\bullet$. Its exact restriction assertion puts each such model in $[a,b]$. Set $S'_\alpha=Y\times_XS_\alpha$, $V'_{\alpha t}=Y\times_XV_{\alpha t}$ and $g_{\alpha t}:V'_{\alpha t}\to V_{\alpha t}$. The same lemma states that the nonempty $S'_\alpha$ stratify $Y$, the $V'_{\alpha t}$ cover them pro-etale, and the restriction of $\widehat P_gK$ is the specified completed pullback of this model along $g_{\alpha t}$. In particular we take fibre-product strata, not a factorization deduced merely from inclusion of images.

Cited node statements read: lem-a1-integral-stratum-chart-restrictions.

### Former step 4

Apply the completed perfect scalar-pullback calculation on every $g_{\alpha t}$. It gives $Lg_{\alpha t}^*C_V(P)\cong C_{V'}(P)$, with the actual finite quotient projections and transitions. Its cohomology and balanced-tensor assertions give $\mathcal H^jC_{V'}(P)\cong g_{\alpha t}^*\mathcal H^jC_V(P)$ and therefore zero for $j\notin[a,b]$. The exact restrictions in the previous step identify these sheaves with the restrictions of $\mathcal H^j(\widehat P_gK)$. Apply noetherian stratum detection on $Y$ to each such abelian sheaf to obtain global vanishing. Empty strata contribute nothing; if $K=0$ the additive functor sends it to zero, covering an empty interval. Finally the integral standard t-structure is bounded and its halves are defined by ambient vanishing: for an integral nonpositive object choose a bound $[a,0]$, and for a nonnegative one choose $[0,b]$. The same argument proves preservation of both integral halves. This checks the crucial hypothesis of coefficient-stage descent, without assuming flatness of $g^{-1}B_{E,X}\to B_{E,Y}$.

Cited node statements read: lem-a1-completed-perfect-scalar-pullback, lem-weil-pbc-noetherian-stratum-detection, lem-a1-integral-stratum-chart-restrictions, prop-weil-pbc-integral-tstructure.

### Former step 5

Rationalize the $A_E$-linear exact functor using semilinear scalar localization with $R=S=A_E$ and $t=u=\varpi_E$: on a fraction it is $f/\varpi_E^n\mapsto\widehat P_g(f)/\varpi_E^n$. The localized t-structure has exactly the image halves required by descent. The scalar-extension package gives the completed integral comparison $C_{L/E,Y}\widehat P_{g,E}\cong\widehat P_{g,L}C_{L/E,X}$ and its identity, composition, coefficient-tower and shift equations. Since Step 2 proved constructible preservation, these comparisons restrict here, and semilinear localization preserves their equations. Thus they are the exact rational-stage comparisons $\beta_{L/E}:T_{L/E,Y}F_E\cong F_LT_{L/E,X}$, with their stated unit and associator normalizations.

Cited node statements read: lem-pur-semilinear-scalar-localization, prop-weil-localized-tstructure, prop-weil-pbc-scalar-extension.

### Former step 6

Apply coefficient-stage descent with integral categories $\mathcal C_X,\mathcal C_Y$ and integral functors $\widehat P_{g,E}$ for every finite field $E$. Step 2 gives linear exactness, Step 4 gives preservation of integral halves, and Step 5 gives the exact scalar comparisons. The common-stage truncation theorem supplies t-exact transitions and the bounded common-stage t-structures with finite-stage truncations; the scalar-extension package supplies exact transition functors with literal identities and associators; the pair-category definition supplies the same common-stage morphisms and cone triangles (a triangle is distinguished iff isomorphic to the image of one finite-stage triangle), and the Verdier-axioms theorem proves that these data form a triangulated category. These are precisely the remaining hypotheses of descent. Consequently each rational $F_E$ and the functor $F_{\overline{\mathbf Q}_\ell}$ are exact and t-exact. Explicitly the latter sends $(E,K)$ to $(E,F_EK)$ and sends a common-stage arrow $u$ over $L$ to $\beta_{\mathrm{target}}^{-1}F_L(u)\beta_{\mathrm{source}}$. The unit and tower equations proved in Step 5 make this independent of further enlargement, as asserted by descent. This constructs the requested common-stage pullback, with its actual arrow action.

Cited node statements read: lem-a1-texact-coefficient-stage-descent, lem-per-adic-common-stage-truncations, def-weil-pbc-qbar-category, prop-weil-pbc-scalar-extension, thm-weil-pbc-verdier-axioms.

### Former step 7

For the additional finite-stage local formula, use $J$ to write the realized pullback of a constructible module sheaf $F$ as $G_gF=E_Y\otimes^L_{g^{-1}E_X}g^{-1}F$. Let $i:S\hookrightarrow X$ be the chosen stratum and $i':S'=Y\times_XS\hookrightarrow Y$. Their coefficient maps are isomorphisms and their pullbacks are exact restrictions, by continuous rational realization. Composition for ambient ringed derived pullbacks identifies $i'^*G_gF$ with $G_{g_S}i^*F$, since $g i'=i g_S$; the structural coefficient maps agree by the finite quotient normalization. On a pro-etale chart $v:U\to S$, put $U'=S'\times_SU$. Slice normalization identifies its restriction with $G_{g_U}(F|_U)$, where $g_U:U'\to U$. This uses restriction for a site object, so imposes no noetherian hypothesis on $U$ or $U'$.

Cited node statements read: lem-per-continuous-rational-derived-realization, lem-sfb-ringed-derived-monoidal-comparisons, lem-per-continuous-coefficient-slice-normalization.

### Former step 8

On a chart trivializing $F|_S$ as $E_U^r$, the derived pullback unit $G_{g_U}(E_U)\cong E_{U'}$ and additivity give $G_{g_U}(E_U^r)\cong E_{U'}^r[0]$. The balanced-tensor map is $e'\otimes(e_1,\ldots,e_r)\mapsto(e'g_U^\sharp(e_1),\ldots,e'g_U^\sharp(e_r))$; its inverse sends the $j$-th basis vector with coefficient $a$ to $a\otimes e_j$. These are inverse by the balancing relation. For $r=0$ both sides are zero. Since pro-etale restriction is exact, all nonzero-degree cohomology sheaves restrict to zero on this cover and hence are zero; alternatively apply stratum detection to the one-stratum scheme $S'$ with these charts. Thus the restriction to $S'$ is concentrated in degree zero, with exactly the asserted continuous finite free chart model. For empty $S'$ this assertion is vacuous. The calculation uses only the derived pullback unit, not flatness of its coefficient map.

Cited node statements read: lem-sfb-ringed-derived-monoidal-comparisons, lem-per-continuous-coefficient-slice-normalization, lem-weil-pbc-noetherian-stratum-detection.

### Former step 9

The descent theorem gives exactness on both hearts and the canonical truncation comparisons $\alpha^-:F\tau^{\le m}\cong\tau^{\le m}F$ and $\alpha^+:F\tau^{\ge m}\cong\tau^{\ge m}F$, characterized by their counit and unit equations. It also gives $F\mathcal H^j\cong\mathcal H^jF$ and compatibility with every $\beta_{L/E}$. On a heart object define $g^*=F|_{\mathrm{heart}}$; invert this cohomology comparison to get $\mathcal H^j(Lg^*K)\cong g^*\mathcal H^j(K)$ in the direction in the statement. Preservation of every interval is just preservation of the intersection $D^{\ge a}\cap D^{\le b}$, using t-exactness and the shift comparisons; an empty interval contains only zero. These conclusions hold at each finite stage and on the common-stage category by the same theorem.

Cited node statements read: lem-a1-texact-coefficient-stage-descent.

## Completion

All requested stage-1 work is prepared. Required server dry run and direct push are the final validation/delivery steps; their exact results are recorded below after execution.
